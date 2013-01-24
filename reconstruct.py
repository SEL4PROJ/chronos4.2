#!/usr/bin/env python

import os
import re
import sys
import copy
from subprocess import Popen, PIPE
from sets import Set

global path_counts
path_counts = {}

global tcfg_paths
tcfg_paths = {}

global tcfg_to_bb_map
tcfg_to_bb_map = {}

global tcfg_to_context_map
tcfg_to_context_map = {}

global total_edges
total_edges = 0

global root_set
root_set = Set([])

global elf_file
global root_node_id
root_node_id = 'Sta'

def read_variables(input_filename):
    var_re = re.compile(r'^d(\d+|Sta)_(\d+)\s+([\d.]+)$')

    f = open(input_filename)
    global path_counts
    global total_edges

    has_out_edge = Set([])

    while True:
        s = f.readline()
        if s == '':
            break
        g = var_re.match(s.strip())
        if not g:
            continue

        from_id, to_id, count = g.groups()
        if from_id not in path_counts:
            path_counts[from_id] = {}

        if to_id in path_counts[from_id]:
            raise Exception("Variable from %s to %s mentioned more than once." % (from_id, to_id))

        count = int(round(float(count)))
        if count == 0:
            continue

        path_counts[from_id][to_id] = count
        if to_id in root_set:
            root_set.remove(to_id)
        has_out_edge.add(from_id)
        total_edges += count

    f.close()
    if not path_counts:
        raise Exception("No variables found in solution.")
    root_set.intersection_update(has_out_edge)
    global root_node_id
    if len(root_set) == 0:
        root_node_id = 'Sta'
    elif len(root_set) != 1:
        raise Exception("Cannot find root node.")
    else:
        root_node_id = root_set.pop()

def read_tcfg_map(input_filename):
    tcfg_re = re.compile(
        r'''^
            (\d+)
            \( \d+ \. \d+ \)
            \(
                (0x[0-9a-f]+)
                \+
                (0x[0-9a-f]+)
            \):
            \s
            \[\s
                ([\d\s]*)
            \] 
            \s([0-9]+)\s
            ([a-f0-9\s]*)$''',
            re.VERBOSE)

    f = open(input_filename)
    global tcfg_paths
    global tcfg_to_bb_map
    global tcfg_to_context_map
    while True:
        s = f.readline()
        if s == '':
            break
        g = tcfg_re.match(s.strip())
        if not g:
            continue

        bb_id, bb_addr, bb_size, bb_dests, bb_lphead, bb_context = g.groups()

        root_set.add(bb_id)
        bb_addr = int(bb_addr, 16)
        bb_size = int(bb_size, 16)
        bb_dests = [ x.strip() for x in bb_dests.split() if x.strip() ]
        bb_context = [ x.strip() for x in bb_context.split() if x.strip() ]

        assert bb_id not in tcfg_paths

        tcfg_paths[bb_id] = bb_dests
        tcfg_to_bb_map[bb_id] = (bb_addr, bb_size)
        tcfg_to_context_map[bb_id] = bb_context

    f.close()
    if not tcfg_paths:
        raise Exception("No nodes found in tcfg map.")

global addr2line_proc
addr2line_proc = None
def addr2line(addr):
    if not elf_file:
        return ''

    global addr2line_proc
    if addr2line_proc is None:
        addr2line_proc = Popen(
            ['arm-none-eabi-addr2line', '-fe',
            elf_file],
            stdin=PIPE, stdout=PIPE, close_fds=True
        )

    addr2line_proc.stdin.write('%#x\n' % addr)
    func = addr2line_proc.stdout.readline().strip()
    line = addr2line_proc.stdout.readline().strip()
    return func

def print_block(node_id):
    if node_id == 'Sta':
        return
    addr, size = tcfg_to_bb_map[node_id]
    space = '   ' * len(tcfg_to_context_map[node_id])
    for i in xrange(0, size, 4):
        print '%#x %s%s' % (addr + i, space, addr2line(addr + i))

def follow():
    # Find an eulerian path through the graph.

    local_path_counts = copy.deepcopy(path_counts)

    edges_remaining = total_edges

    seen_set = set()
    stack = []
    stack.append(root_node_id)

    annotations = dict([(x, []) for x in tcfg_paths.keys()])

    path = []

    while stack:
        node_id = stack[-1]

        # If we cannot go anywhere from here, return back up to the next node.
        # We execute this node on the way out.
        if node_id not in local_path_counts:
            stack.pop()

            path.append(node_id)
            continue

        # Visit the next edge. Most loops blocks have two edges, one for the
        # loop, one for the entry (or exit in this case). Follow the loop one
        # first (the one with the higher execution count).
        sorted_edges = local_path_counts[node_id].keys()
        sorted_edges.sort(key = lambda dst: local_path_counts[node_id][dst],
                reverse=True)

        # If we have no edges, we are done. Just delete this from path_counts
        # and continue, so that the first test in the loop will catch us.
        if not sorted_edges:
            del local_path_counts[node_id]
            continue

        dest_id = sorted_edges[0]

        # If that edge cannot be taken anymore, discard it and try again.
        if local_path_counts[node_id][dest_id] == 0:
            del local_path_counts[node_id][dest_id]
            continue

        # Tell the user what's going on.
        if len(sorted_edges) > 1:
            choices = ', '.join([
                '%s/%#x(%d)' % (
                    x, tcfg_to_bb_map[x][0], local_path_counts[node_id][x])
                for x in sorted_edges])
            #annotations[dest_id].append(
            #    "# (from %s had choice of [%s])" % (node_id, choices))

        # Do we need to accelerate matters for long loops?
        # We can accelerate once we have been through the loop once.
        if local_path_counts[node_id][dest_id] > 100 and dest_id in seen_set:
            # Find dest_id in the stack, starting from the end.
            for repeat_idx in xrange(len(stack) - 1, -1, -1):
                if dest_id == stack[repeat_idx]:
                    break
            else:
                # This shouldn't happen. We should have found it in the
                # stack if we added it to the set.
                assert False, "Internal error!"

            blocks = ' '.join(stack[repeat_idx:])
            count = local_path_counts[node_id][dest_id] - 1
            annotations[node_id].append(
                "# The following blocks repeat %d times: [ %s ]" % (
                    count, blocks))

            # Decrement the appropriate count from each of the basic blocks
            # within the loop.
            # This probably does not work for nested loops!

            stack.append(dest_id)
            prev = dest_id
            for next in stack[repeat_idx+1:]:
                assert local_path_counts[prev][next] >= count, \
                    "Needed %d spare iterations in (%s -> %s), but only had %d" % (
                            count, prev, next, local_path_counts[prev][next])
                local_path_counts[prev][next] -= count
                edges_remaining -= count
                prev = next
            stack.pop()

            continue

        stack.append(dest_id)
        seen_set.add(dest_id)

        assert local_path_counts[node_id][dest_id] > 0
        local_path_counts[node_id][dest_id] -= 1
        edges_remaining -= 1

    prev = None
    for node_id in reversed(path):
        # print '# %s(%#x) -> %s(%#x)' % (
        #         prev, tcfg_to_bb_map.get(prev, [0])[0],
        #         node_id, tcfg_to_bb_map.get(node_id, [0])[0])

        for s in annotations.get(node_id, []):
            print s

        print_block(node_id)

        prev = node_id

    if edges_remaining > 0:
        print "%d edges remain:" % edges_remaining
        def tryint(x):
            try:
                return int(x)
            except:
                return -1

        for src in sorted(local_path_counts.keys(), key=tryint):
            for dst in sorted(local_path_counts[src].keys(), key=tryint):
                if local_path_counts[src][dst] == 0:
                    continue

                print "%d\t: %s(%#x) -> %s(%#x)" % (
                    local_path_counts[src][dst],
                    src, tcfg_to_bb_map[src][0],
                    dst, tcfg_to_bb_map[dst][0])

                # Is this node reachable from the current path?
                if src in seen_set:
                    print "\t and it could be reached!"


if __name__ == '__main__':
    if not (3 <= len(sys.argv) <= 4):
        print "Usage: reconstruct <solution file> <tcfg map file> [ELF file]"
        sys.exit(1)

    if len(sys.argv) >= 4:
        elf_file = sys.argv[3]
    else:
        elf_file = None
    read_tcfg_map(sys.argv[2])
    read_variables(sys.argv[1])

    follow()
