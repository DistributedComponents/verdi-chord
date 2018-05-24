#!/usr/bin/env bash

strace -f -s 800 -o client_out.txt -e select,connect,recvfrom,sendto,write,bind,socket,listen,accept,accept4,close ./client.native -bind 127.0.0.6 -node 127.0.0.2:7000 -query get_ptrs
