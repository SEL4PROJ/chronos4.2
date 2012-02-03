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

def context_match(ctx1, ctx2, start, end):
    i = len(ctx1) - 1;
    j = len(ctx2) - 1;
    while i >= 0 and j >= 0 and ctx1[i] == ctx2[j]:
        i = i - 1
        j = j - 1
    
    #print ctx1
    #print ctx2
    #print i, j, start, end, ctx1[i], ctx2[j]
   
    if i >= 0 and (ctx1[i] < start or ctx1[i] > end):
        return False
    if j >= 0 and (ctx2[j] < start or ctx2[j] > end):
        return False

    return True

def process_conflict(fout, conflict_file):
    f = open(conflict_file)

    global bb_count
    global edge_count
    global bb_addr_to_id

    fout.write('\ === conflict constraints === \n\n')

    last_bb_id = 0
    while True:
        kind_str = f.readline()
        if kind_str == '':
            break;
        kind_str = kind_str.strip()

        if kind_str == 'times':
            n = f.readline();
            if n == '':
                break;
            s = f.readline()
            if s == '':
                break

            num = int(n.strip())
            bb_addr = int(s.strip(), 16)

            if bb_addr in bb_addr_to_ids:
                id_list = bb_addr_to_ids[bb_addr]
                if len(id_list) > 0:
                    for id in id_list:
                        if id <> id_list[0]:
                            fout.write(" + ")
                        fout.write("b{0}".format(id))
                    fout.write(" <= {0}\n".format(num))
        else:
            bb1_str = f.readline()
            if bb1_str == '':
                break
            bb2_str = f.readline()
            if bb2_str == '':
                break
            start_str = f.readline()
            if start_str == '':
                break
            end_str = f.readline();
            if end_str == '':
                break
         
            bb1 = int(bb1_str.strip(), 16)
            bb2 = int(bb2_str.strip(), 16)
            start = int(start_str.strip(), 16)
            end = int(end_str.strip(), 16)

            if bb1 in bb_addr_to_ids and bb2 in bb_addr_to_ids:
                id_list1 = bb_addr_to_ids[bb1]
                id_list2 = bb_addr_to_ids[bb2]
                #print id_list1, id_list2
                for id1 in id_list1:
                    for id2 in id_list2:
                        if context_match(id_to_context[id1], id_to_context[id2], start, end):
                            if kind_str == 'conflict':
                                fout.write("b{0} + b{1} <= 1\n".format(id1, id2))
                            elif kind_str == 'consistent':
                                fout.write("b{0} - b{1} = 0\n".format(id1, id2))

    fout.write("\n");
    f.close()

def print_constraints(conflict_file, old_cons_file, new_cons_file):
    global bb_count
    global edge_count

    fin = open(old_cons_file)
    fout = open(new_cons_file, 'w+')
    for line in fin:
        if line.strip() != 'Generals':
            fout.write(line)
            continue
        process_conflict(fout, conflict_file)
        fout.write(line)
    fin.close()
    fout.close()

if __name__ == '__main__':
    if len(sys.argv) != 5:
        print "Usage: conflict <tcfg map> <conflict file> <old constraints file> <new constraints file>"
        sys.exit(1)
    read_tcfg_map(sys.argv[1])
    print_constraints(sys.argv[2], sys.argv[3], sys.argv[4])
