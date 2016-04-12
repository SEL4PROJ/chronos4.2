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

global bb_id_to_next
bb_id_to_next = {}

global bb_id_to_addr
bb_id_to_addr = {}

global bb_count
bb_count = {}

global bb_size
bb_id_to_size = {}

global edge_count
edge_count = {}

global bb_id_to_dests
bb_id_to_dests = {}

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
            \][0-9a-f\s]+$''',
            re.VERBOSE)

    f = open(input_filename)

    while True:
        s = f.readline()
        if s == '':
            break
        g = tcfg_re.match(s.strip())
        if not g:
            continue

        bb_id, bb_addr, bb_size, bb_dests = g.groups()

        bb_id = int(bb_id)
        bb_addr = int(bb_addr, 16)
        bb_size = int(bb_size, 16)

        bb_dests = [ int(x.strip()) for x in bb_dests.split() if x.strip() ]

        if not bb_addr in bb_addr_to_ids:
            bb_addr_to_ids[bb_addr] = [bb_id]
        else:
            bb_addr_to_ids[bb_addr].append(bb_id)
        bb_id_to_dests[bb_id] = bb_dests
        bb_id_to_addr[bb_id] = bb_addr
        bb_count[bb_id] = 0
        bb_id_to_size[bb_id] = bb_size
        for dest in bb_dests:
            edge_count[(bb_id, dest)] = 0
        if len(bb_dests) == 1:
            bb_id_to_next[bb_id] = bb_dests[0]
        elif len(bb_dests) == 0:
            bb_id_to_next[bb_id] = -1
        else:
            bb_id_to_next[bb_id] = -2

    f.close()

def read_profile(profile_name):
    profile_re = re.compile(r'([0-9]+:\s*)([0-9a-f]+)')
    f = open(profile_name)

    global bb_count
    global edge_count
    global bb_addr_to_id

    start_address = int(sys.argv[5], 16)
    if not start_address in bb_addr_to_ids:
        raise Exception("Start address is invalid.")
    assert(len(bb_addr_to_ids[start_address]) == 1)
    start_bb = bb_addr_to_ids[start_address][0];    
    start_times = int(sys.argv[6])

    line_count = 0;
    print hex(start_address)

    num_skip = 0;
    last_bb_id = 0
    while True:
        s = f.readline()
        line_count += 1
        if s == '':
            break
        g = profile_re.match(s.strip())
        if not g:
            continue

        if num_skip > 0:
            num_skip -= 1
            continue
        prefix, bb_addr = g.groups()
        bb_addr = int(bb_addr, 16)

        if bb_addr in bb_addr_to_ids:
            if bb_addr == start_address:
                start_times = start_times - 1
                print line_count
                if start_times < 0:
                    f.close()
                    return
            if start_times == 0:
                print "searching {0}".format(hex(bb_addr))
                bb_id = -1
                id_list = bb_addr_to_ids[bb_addr]
                if bb_addr == start_address:
                    bb_id = start_bb
                else:

                    next_bb_id = bb_id_to_next[last_bb_id]
                    while next_bb_id >= 0 and bb_id_to_size[next_bb_id] == 0:
                        # last_bb_id -> next_bb_id
                        if last_bb_id != 0:
                            if (last_bb_id, next_bb_id) in edge_count:
                                edge_count[(last_bb_id, next_bb_id)] = edge_count[(last_bb_id, next_bb_id)] + 1
                        bb_count[next_bb_id] = bb_count[next_bb_id] + 1
                        print "..=> ", next_bb_id
                        last_bb_id = next_bb_id
                        next_bb_id = bb_id_to_next[last_bb_id]

                    # last node
                    if bb_id_to_next[last_bb_id] == -1:
                        break 

                    for id in id_list:
                        if (last_bb_id, id) in edge_count:
                            bb_id = id
                            break
                    if bb_id == -1:

                        bb_dests = bb_id_to_dests[last_bb_id]
                        for id in bb_dests:
                            if bb_id_to_size[id] == 0:
                                next_bb_id = id
                                break
                        while next_bb_id >= 0 and bb_id_to_size[next_bb_id] == 0:
                            # last_bb_id -> next_bb_id
                            if last_bb_id != 0:
                                if (last_bb_id, next_bb_id) in edge_count:
                                    edge_count[(last_bb_id, next_bb_id)] = edge_count[(last_bb_id, next_bb_id)] + 1
                            bb_count[next_bb_id] = bb_count[next_bb_id] + 1
                            print "..=> ", next_bb_id
                            last_bb_id = next_bb_id
                            next_bb_id = bb_id_to_next[last_bb_id]

                        for id in id_list:
                            if (last_bb_id, id) in edge_count:
                                bb_id = id
                                break

                        # check if the last instruction of last_bb_id is switch
                        last_bb_addr = bb_id_to_addr[last_bb_id]
                        last_inst_addr = last_bb_addr + bb_id_to_size[last_bb_id] - 4
                        if last_inst_addr in bb_addr_to_ids:
                            switch_id_list = bb_addr_to_ids[last_inst_addr]
                            assert(len(switch_id_list) > 1)
                            next_bb_id = -1
                            for id in switch_id_list:
                                if (last_bb_id, id) in edge_count:
                                    next_bb_id = id
                                    break
                            if next_bb_id > 0:
                                while next_bb_id in switch_id_list:
                                    if last_bb_id != 0:
                                        if (last_bb_id, next_bb_id) in edge_count:
                                            edge_count[(last_bb_id, next_bb_id)] = edge_count[(last_bb_id, next_bb_id)] + 1
                                    bb_count[next_bb_id] = bb_count[next_bb_id] + 1
                                    print last_bb_id, " => ", next_bb_id
                                    last_bb_id = next_bb_id
                                    next_bb_id = last_bb_id + 1
                                    for id in id_list:
                                        if (last_bb_id, id) in edge_count:
                                            bb_id = id
                                            break
                                    if bb_id >= 0:
                                        break

                        if bb_id == -1:
                            print last_bb_id, bb_id, hex(bb_addr)
                            print id_list
                            assert(0)

                if last_bb_id != 0:
                    if (last_bb_id, bb_id) in edge_count:
                        edge_count[(last_bb_id, bb_id)] = edge_count[(last_bb_id, bb_id)] + 1
                bb_count[bb_id] = bb_count[bb_id] + 1 
                print "=> ", bb_id
                num_skip = bb_id_to_size[bb_id] / 4 - 1
                last_bb_id = bb_id

    f.close()

def print_constraints(old_cons_file, new_cons_file):
    global bb_count
    global edge_count

    fin = open(old_cons_file)
    fout = open(new_cons_file, 'w+')
    infeasible = False
    for line in fin:
        if line.find('loop') >= 0:
            infeasible = True
        else:
            if line.find('===') >= 0 or line.find('Generals') >= 0:
                infeasible = False
        if infeasible:
            continue
        if line.strip() != 'Generals':
            fout.write(line)
            continue
        fout.write('\ === specified path constraints === \n\n')
        for bb_id, count in bb_count.iteritems():
##            if count > 0:
            if bb_id > 1:
                 fout.write('b{0} = {1}\n'.format(bb_id, count))
##                fout.write('b{0} <= {1}\n'.format(bb_id, count+1))
        for (src, dest), count in edge_count.iteritems():
            if count > 0:
                fout.write('d{0}_{1} = {2}\n'.format(src, dest, count))
#                fout.write('d{0}_{1} <= {2}\n'.format(src, dest, count+1))
        fout.write('\n' + line)
    fin.close()
    fout.close()

if __name__ == '__main__':
    if len(sys.argv) != 7:
        print "Usage: path_cons <tcfg map file> <profile file> <old constraints file> <new constraints file> <start address> <start times>"
        sys.exit(1)
    read_tcfg_map(sys.argv[1])
    read_profile(sys.argv[2])
    print_constraints(sys.argv[3], sys.argv[4])
