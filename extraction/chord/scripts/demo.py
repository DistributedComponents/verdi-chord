import itertools
import os
import Queue
import random
import subprocess
import sys
import threading
import time

CHORD = os.path.join(os.path.dirname(__file__), "../chord.native")

# Should agree with SUCC_LIST_LEN in ExtractChord.v
SUCC_LIST_LEN = 3
N = 256

class Addr(object):
    def __init__(self, ip, port):
        self.ip = ip
        self.port = int(port)

    def __repr__(self):
        return "{}:{}".format(self.ip, self.port)

    # should agree with hash in ExtractChord.v
    def chordhash(self):
        return self.last_ip_byte() % N

    def last_ip_byte(self):
        return int(self.ip.split(".")[-1])

def read_to_queue(f, queue):
    while True:
        for line in f:
            if line != "":
                # trim newline
                queue.put(line[:-1])

class Node(object):
    def __init__(self, addr, known=None, pred=None, succs=None):
        self.args = ["-bind", str(addr)]
        if known is None and pred is not None and succs is not None:
            self.knowns = [pred] + succs
            self.args += ["-pred", str(pred)]
            for s in succs:
                self.args += ["-succ", str(s)]
        elif known is not None and pred is None and succs is None:
            self.knowns = [known]
            self.args += ["-known", str(known)]
        else:
            raise InvalidArgumentException("please specify pred+succs or known, and not both")
        self.addr = addr
        self.started = False
        self.p = None
        self.buffer = ""

    def spawn(self):
        args = [CHORD] + self.args
        print "# running", " ".join(args)
        p = subprocess.Popen(
                args,
                stdin=open(os.devnull, "r"),
                stdout=subprocess.PIPE)
        q = Queue.Queue()
        self.t = threading.Thread(target=read_to_queue, args=(p.stdout, q))
        self.t.daemon = True
        self.t.start()
        self.output_queue = q
        self.started = True

    def readlines(self):
        lines = []
        while len(lines) < 10:
            try:
                lines.append(self.output_queue.get_nowait())
            except Queue.Empty:
                break
        return lines

    def kill(self):
        self.p.terminate()
        self.p.wait()

    def __repr__(self):
        template = "Node(addr={}, knowns={}, started={})"
        return template.format(self.addr, self.knowns, self.started)

def ideal_ring(start, n):
    nodes = []
    addrs = sorted([Addr("127.0.0.{}".format(start + i), 8000) for i in range(n)],
                   key=lambda a: a.chordhash())
    for i, a in enumerate(addrs):
        pred = addrs[i - 1]
        if n - i <= SUCC_LIST_LEN:
            extra = SUCC_LIST_LEN - (n - i - 1)
            succs = addrs[i+1:] + addrs[0:extra]
        else:
            succs = addrs[i+1:i+SUCC_LIST_LEN+1]
        nodes.append(Node(a, pred=pred, succs=succs))
    return nodes

def add_node(nodes):
    known = random.choice(nodes)
    num = max(n.addr.last_ip_byte() for n in nodes) + 1
    addr = Addr("127.0.0.{}".format(num), 8000)
    new_node = Node(addr, known=known.addr)
    print "adding node {} at {}".format(addr.chordhash(), addr)
    new_node.spawn()
    nodes.append(new_node)

def kill_random_node(nodes):
    if len(nodes) > 3 * SUCC_LIST_LEN:
        condemned = random.choice(nodes)
        print "killing node {}".format(node.addr.chordhash())
        node.kill()

def random_action(nodes):
    r = random.random()
    if r < 0.4:
        add_node(nodes)
    if 0.5 < r < 0.1:
        kill_random_node(nodes)

def main(count):
    nodes = ideal_ring(1, count)
    for node in nodes:
        node.spawn()
    tick = time.time() + 25.0
    while True:
        lines = []
        for node in nodes:
            for l in node.readlines():
                if " - " not in l:
                    print "# " + l
                else:
                    timestamp, line = l.split(" - ", 1)
                    lines.append((float(timestamp), line))
        lines.sort(key=lambda (ts, _): ts)
        for (ts, line) in lines:
            sys.stdout.write(line + "\n")
        sys.stdout.flush()
        if time.time() > tick:
            #random_action(nodes)
            tick = time.time() + 20.0

if __name__ == "__main__":
    if len(sys.argv) > 1:
        count = int(sys.argv[1])
    else:
        count = 4
    main(count)
