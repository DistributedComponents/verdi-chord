# for computing chord IDs
import md5
import os.path
import Queue
import subprocess
# for sys.argv
import sys
import threading

CHORD = os.path.join(os.path.dirname(__file__), "../chord.native")

# Must agree with SUCC_LIST_LEN in ExtractChord.v
SUCC_LIST_LEN = 3

class Addr(object):
    def __init__(self, host, port):
        self.host = host
        self.port = int(port)

    def __repr__(self):
        return "{}:{}".format(self.host, self.port)

    # should agree with hash in ExtractChord.v
    def chordhash(self):
        md5.new(self.host).digest()

# Each node's "read_thread" executes this function to put logged information
# from its chord.native process into the node's queue.
def read_to_queue(f, queue):
    for line in f:
        if line != "":
            # trim newline from logged message
            queue.put(line[:-1])

class Node(object):
    def __init__(self, addr, ring=None, known=None):
        self.args = ["-bind", str(addr)]
        if ring is not None and known is None:
            self.knowns = ring
            for s in ring:
                self.args += ["-ring", str(s)]
        elif ring is None and known is not None:
            self.knowns = [known]
            self.args += ["-known", str(known)]
        else:
            raise InvalidArgumentException("please specify ring nodes or known, but not both")
        self.addr = addr
        self.proc = None
        self.output_queue = None
        self.buffer = ""

    def spawn(self):
        args = [CHORD] + self.args
        print "# executing", " ".join(args)
        self.proc = subprocess.Popen(args, stdin=open(os.devnull, "r"), stdout=subprocess.PIPE)
        q = Queue.Queue()
        self.read_thread = threading.Thread(target=read_to_queue, args=(self.proc.stdout, q))
        self.read_thread.daemon = True
        self.read_thread.start()
        self.output_queue = q
        self.started = True

    def readlines(self):
        lines = []
        while len(lines) == 0:
            try:
                lines.append(self.output_queue.get_nowait())
            except Queue.Empty:
                break
        return lines

    def kill(self):
        self.proc.terminate()
        self.proc.wait()

    def __repr__(self):
        template = "Node(addr={}, knowns={}, started={})"
        return template.format(self.addr, self.knowns, self.started)

def initial_ring(start, n):
    initial_addrs = [Addr("127.0.0.{}".format(start + i), 8000) for i in range(n)]
    nodes = []
    for addr in initial_addrs:
        nodes.append(Node(addr, initial_addrs))
    return nodes

def main(count):
    nodes = initial_ring(1, count)
    for node in nodes:
        node.spawn()
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

if __name__ == "__main__":
    if len(sys.argv) > 1:
        count = int(sys.argv[1])
    else:
        count = 5
    main(count)
