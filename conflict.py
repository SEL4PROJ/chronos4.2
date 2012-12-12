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
            \]([0-9a-f\s]+)$''',
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

        bb_id, bb_addr, bb_size, bb_dests, ctx_str= g.groups()

        #print ctx_str

        bb_addr = int(bb_addr, 16)
        bb_size = int(bb_size, 16)
        bb_dests = [ x.strip() for x in bb_dests.split() if x.strip() ]

        ctx_str_list = ctx_str.split(' ')
        ctx_list = [ int(x, 16) for x in ctx_str_list if x <> '' ]

        if not bb_addr in bb_addr_to_ids:
            bb_addr_to_ids[bb_addr] = [bb_id]
        else:
            bb_addr_to_ids[bb_addr].append(bb_id)

        id_to_context[bb_id] = ctx_list
        bb_count[bb_id] = 0
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
            preemption_edges.append(tuple([int(x) for x in bits[1:4]]))

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
            print conflict_line
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
            assert ((len(parts) - 1) % 2) == 0, \
                    "conflict_edge_set does not have an even number of arguments."
            s = None
            p = parts[1:]
            n = 0
            while p:
                a = int(p[0], 0)
                b = int(p[1], 0)
                if s == None:
                    s = 'd%d_%d' % (a, b)
                else:
                    s += ' + d%d_%d' % (a, b)
                p = p[2:]
                n += 1
            s += ' <= %d\n' % (n - 1)
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
                print "WARNING: No constraints generated!"
        else:
            assert False, "Invalid line: %s" % parts[0]

    fout.write("\n");
    f.close()

def print_constraints(conflict_file, old_cons_file, new_cons_file, pp_num):
    global bb_count
    global edge_count

    preemption_edges = read_preemption_edges(conflict_file)
    num_pp = len(preemption_edges)
    print "Have %d preemption points" % num_pp
    if num_pp > 0:
        if pp_num != None:
            assert 0 <= pp_num <= num_pp
            if pp_num == num_pp:
                print "Exercising pp from %d -> END" % (pp_num)
            elif pp_num == 0:
                print "Exercising pp from START -> %d" % (pp_num + 1)
            else:
                print "Exercising pp from %d -> %d" % (pp_num, pp_num + 1)
        else:
            print "But not doing anything about it. Iterate from 0 .. %d." % num_pp

    fin = open(old_cons_file)
    fout = open(new_cons_file, 'w+')

    for line in fin:
        if line.strip() == 'Generals':
            process_conflict(fout, conflict_file)
        fout.write(line)

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
