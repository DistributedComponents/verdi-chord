#!/usr/bin/env bash
strace -f -s 800 -o out.txt -e select,connect,recvfrom,sendto,write,bind,socket,listen,accept,accept4,close python scripts/demo.py 5
