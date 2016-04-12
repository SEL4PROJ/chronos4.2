'''
Copyright 2014, NICTA

This software may be distributed and modified according to the terms of
the GNU General Public License version 2. Note that NO WARRANTY is provided.
See "LICENSE_GPLv2.txt" for details.

@TAG(NICTA_GPL)
'''
#!/usr/bin/env python

import os
import re
import sys
import copy
from subprocess import Popen, PIPE

global bb_addr_to_ids
bb_addr_to_ids = {}

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
            \].*$''',
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

        bb_id, bb_addr, bb_size, bb_dests = g.groups()

        bb_addr = int(bb_addr, 16)
        bb_size = int(bb_size, 16)
        bb_dests = [ x.strip() for x in bb_dests.split() if x.strip() ]

        if not bb_addr in bb_addr_to_ids:
            bb_addr_to_ids[bb_addr] = [bb_id]
        else:
            bb_addr_to_ids[bb_addr].append(bb_id)
        bb_count[bb_id] = 0
        for dest in bb_dests:
            edge_count[(bb_id, dest)] = 0

    f.close()

def process_blacklist(fout, blacklist_file):
    f = open(blacklist_file)

    global bb_count
    global edge_count
    global bb_addr_to_id

    fout.write('\ === black list constraints === \n\n')

    last_bb_id = 0
    while True:
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
    fout.write("\n");
    f.close()

def print_constraints(blacklist_file, old_cons_file, new_cons_file):
    global bb_count
    global edge_count

    fin = open(old_cons_file)
    fout = open(new_cons_file, 'w+')
    for line in fin:
        if line.strip() != 'Generals':
            fout.write(line)
            continue
        process_blacklist(fout, blacklist_file)
        fout.write(line)
    fin.close()
    fout.close()

if __name__ == '__main__':
    if len(sys.argv) != 5:
        print "Usage: blacklist <tcfg map file> <blacklist file> <old constraints file> <new constraints file>"
        sys.exit(1)
    read_tcfg_map(sys.argv[1])
    print_constraints(sys.argv[2], sys.argv[3], sys.argv[4])
