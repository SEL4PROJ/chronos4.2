#!/usr/bin/env python

import os
import re
import sys
import copy
from subprocess import Popen, PIPE

global bb_addr_to_ids
bb_addr_to_ids = {}

global id_to_context
id_to_context = {}

global bb_count
bb_count = {}

global edge_count
edge_count = {}

global bb_loop_head
bb_loop_head = {}

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
            \]\s
            ([0-9]+)\s
            ([0-9a-f\s]+)$''',
            re.VERBOSE)

    f = open(input_filename)

    global bb_addr_to_ids
    global bb_count
    global edge_count

    while True:
        s = f.readline()
        if s == '':
            break
        g = tcfg_re.match(s.strip())
        if not g:
            continue

        bb_id, bb_addr, bb_size, bb_dests, bb_lphead, ctx_str= g.groups()

        #print ctx_str

        bb_addr = int(bb_addr, 16)
        bb_size = int(bb_size, 16)
        bb_lphead = int(bb_lphead)
        bb_dests = [ x.strip() for x in bb_dests.split() if x.strip() ]

        ctx_str_list = ctx_str.split(' ')
        ctx_list = [ int(x, 16) for x in ctx_str_list if x <> '' ]

        if not bb_addr in bb_addr_to_ids:
            bb_addr_to_ids[bb_addr] = [bb_id]
        else:
            bb_addr_to_ids[bb_addr].append(bb_id)

        id_to_context[bb_id] = ctx_list
        bb_count[bb_id] = 0
        bb_loop_head[bb_id] = bb_lphead
        for dest in bb_dests:
            edge_count[(bb_id, dest)] = 0

    f.close()

def context_match(ctx1, ctx2, start, end, id1, id2):
    i = len(ctx1) - 1
    j = len(ctx2) - 1
    while i >= 0 and j >= 0 and ctx1[i] == ctx2[j]:
        if start <= ctx1[i] <= end:
            return True

        i = i - 1
        j = j - 1

    #if (id1, id2) == ('2658', '2967'):
        #print ['%x' % x for x in ctx1]
        #print ['%x' % x for x in ctx2]
        #print i, j, hex(start), hex(end), hex(ctx1[i]), hex(ctx2[j])

    if i >= 0 and (ctx1[i] < start or ctx1[i] > end):
        return False
    if j >= 0 and (ctx2[j] < start or ctx2[j] > end):
        return False

    return True

def read_preemption_edges(conflict_file):
    preemption_edges = []
    f = open(conflict_file)
    while True:
        l = f.readline()
        if l == '':
            break
        bits = l.strip().split()
        if bits[0] == "preemption_point":
            preemption_edges.append(tuple([int(x, 0) for x in bits[1:4]]))

    f.close()
    return preemption_edges

def process_conflict(fout, conflict_file):
    f = open(conflict_file)

    global bb_count
    global edge_count
    global bb_addr_to_id

    fout.write('\ === conflict constraints === \n\n')

    last_bb_id = 0
    while True:
        conflict_line = f.readline()
        if conflict_line == '':
            break
        conflict_line = conflict_line.strip()
        if conflict_line[0] == '#':
            #print conflict_line
            fout.write("\\ %s\n" % conflict_line)
            continue

        parts = conflict_line.split()

        if parts[0] == 'times':
            n = parts[1]
            s = parts[2]

            num = int(n.strip(), 0)
            bb_addr = int(s.strip(), 0)

            if bb_addr in bb_addr_to_ids:
                id_list = bb_addr_to_ids[bb_addr]
                if len(id_list) > 0:
                    for id in id_list:
                        if id <> id_list[0]:
                            fout.write(" + ")
                        fout.write("b{0}".format(id))
                    fout.write(" <= {0}\n".format(num))
        elif parts[0] == "conflict_edge_set":
            # Each pair of bbs specifies an edge.
            assert ((len(parts) - 1) % 2) == 1, \
                    "conflict_edge_set does not have an odd number of arguments."
            s = None
            p = parts[1:]
            n = 0
            while len(p) >= 2:
                a = int(p[0], 0)
                b = int(p[1], 0)
                if s == None:
                    s = 'd%d_%d' % (a, b)
                else:
                    s += ' + d%d_%d' % (a, b)
                p = p[2:]
                n += 1
            s += ' <= %d\n' % (int(p[0], 0))
            fout.write(s)
        elif parts[0] == "preemption_point":
            pass
        elif parts[0] in ("conflict", "consistent"):
            bb1_str = parts[1]
            bb2_str = parts[2]
            start_str = parts[3]
            end_str = parts[4]
         
            bb1 = int(bb1_str.strip(), 0)
            bb2 = int(bb2_str.strip(), 0)
            start = int(start_str.strip(), 0)
            end = int(end_str.strip(), 0)

            did_it = False
            if bb1 in bb_addr_to_ids and bb2 in bb_addr_to_ids:
                id_list1 = bb_addr_to_ids[bb1]
                id_list2 = bb_addr_to_ids[bb2]
                #if bb1 == 0xf0014c18 and bb2 == 0xf0014ad4:
                    #print "LISTS"
                    #print id_list1
                    #print id_list2
                for id1 in id_list1:
                    for id2 in id_list2:
                        if context_match(id_to_context[id1], id_to_context[id2], start, end, id1, id2):
                            if parts[0] == 'conflict':
                                fout.write("b{0} + b{1} <= 1\n".format(id1, id2))
                                did_it = True
                            elif parts[0] == 'consistent':
                                fout.write("b{0} - b{1} = 0\n".format(id1, id2))
                                did_it = True

            if not did_it:
                print "WARNING: No constraints generated for line: %s" % conflict_line
        else:
            assert False, "Invalid line: %s" % parts[0]

    fout.write("\n");
    f.close()

def process_preemptions(fout, preemption_edges, pp_num):
    fout.write("\ === preemption point constraints === \n\n")
    if pp_num == None:
        fout.write("\ No preemption points enabled.\n\n")
    else:
        if pp_num == 0:
            # Leave the starting edge in.
            fout.write("\ Assuming entry at start.\n\n")
        else:
            fout.write("\ Assuming entry at pp %d.\n\n" % pp_num)

        # Disable all not-preempt edges from preemption points, except our
        # starting preemption point.
        for i, (src, preempt_dst, not_preempt_dst) in enumerate(preemption_edges):
            if i == pp_num - 1:
                fout.write("b%d = 1\n" % src)
                fout.write("d%d_%d = 1\n" % (src, not_preempt_dst))
            else:
                fout.write("d%d_%d = 0\n" % (src, not_preempt_dst))
    fout.write("\n")

def print_constraints(conflict_file, old_cons_file, new_cons_file, pp_num):
    global bb_count
    global edge_count
    global bb_loop_head

    preemption_edges = read_preemption_edges(conflict_file)
    num_pp = len(preemption_edges)
    print "Have %d preemption points" % num_pp
    entry_pp = None
    if num_pp > 0:
        if pp_num != None:
            assert 0 <= pp_num <= num_pp
            if pp_num == 0:
                print "Exercising pps from START"
                entry_pp = None
            else:
                print "Exercising pps from %d" % (pp_num)
                entry_pp = preemption_edges[pp_num - 1]
        else:
            print "But not doing anything about it. Iterate from 0 .. %d." % num_pp

    # If we want to start the CFG at some other point, we need to fudge the
    # flow equations. If we're forcing the edge A->B as our starting point, we
    # need to set dA_B = 1, and also remove the flow equation for A's sources.
    # Here we construct a regexp that describes the line we're looking for.
    if entry_pp != None:
        entry_pp_src = re.compile(r'\bb%d\b' % entry_pp[0])
        entry_pp_edge = re.compile(r'\bd\d+_%d\b' % entry_pp[0])
        lphead = bb_loop_head[str(entry_pp[0])]
        entry_pp_lp = re.compile(r'b%d(.v\d)*\s-\s\d+\sd\d+_%d(.v\d)*\s<=\s0' % (lphead, lphead))
    else:
        entry_pp_src = None
        entry_pp_edge = None

    fin = open(old_cons_file)
    fout = open(new_cons_file, 'w+')

    start_edge_line = None

    discarded_pp_line = False
    for line in fin:
        line = line.strip()
        if line == 'dSta_0 = 1':
            if entry_pp != None:
                # Force the start edge to 0.
                fout.write('dSta_0 = 0\n')
                continue

        if entry_pp_src != None:
            g1 = entry_pp_src.search(line)
            g2 = entry_pp_edge.search(line)
            if g1 and g2:
                #if discarded_pp_line:
                #    raise Exception("Found multiple flow lines for preemption point.")
                discarded_pp_line = True
                continue

        if entry_pp_lp != None:
            g = entry_pp_lp.match(line)
            if g:
                discarded_pp_line = True
                continue

        if line.strip() == 'Generals':
            process_conflict(fout, conflict_file)
            process_preemptions(fout, preemption_edges, pp_num)
        fout.write(line + "\n")

    #if entry_pp_src != None and not discarded_pp_line:
    #    raise Exception("Failed to find flow line for preemption point.")

    fin.close()
    fout.close()

if __name__ == '__main__':
    if not (5 <= len(sys.argv) <= 6):
        print "Usage: conflict <tcfg map> <conflict file> <old constraints file> <new constraints file> [preemption point number]"
        sys.exit(1)
    read_tcfg_map(sys.argv[1])
    pp_num = None
    if len(sys.argv) > 5:
        pp_num = int(sys.argv[5])
    print_constraints(sys.argv[2], sys.argv[3], sys.argv[4], pp_num)
