#!/usr/bin/env bash
strace -f -s 800 -o out.txt -e select,connect,recvfrom,sendto,write,bind python scripts/demo.py 5
