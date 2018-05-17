#!/usr/bin/env bash

strace -f -s 800 -o client_out.txt -e select,connect,recvfrom,sendto,write,bind ./client.native -bind 127.0.0.1 -node 127.0.0.2:6000 -query get_ptrs
