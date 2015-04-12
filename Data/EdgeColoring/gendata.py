# gendata.py
# generate data file for vizingShannon.py
# command line parameters are infile and outfile
# input wfile formula is
# N w0 w1 w2 ... wk
# N is number of vertices in the graph
# w0 ... wk give weights for probability
# of 0, 1, 2, ... k edges beween a par of vertices

import sys, random, itertools
from collections import defaultdict

count = defaultdict(int)

if sys.version_info.major < 3 or sys.version_info.minor < 2:
    cout << 'requires python 3.2 or better\n'
    exit()
    
if not len(sys.argv) == 3:
    print("Usage: gendata.py infile outfile")

with open(sys.argv[1]) as fin:
    text = fin.read().split()
    N = int(text[0])
    w = list(map(int, text[1:]))
    weights = list(itertools.accumulate(w))
    totalWeight = sum(w)
random.seed()

with open(sys.argv[2], 'w') as fout:
    fout.write(str(N)+'\n')
    for k in range(N):
        for j in range(k+1, N):
            p = random.randint(1, totalWeight)
            for idx, w in enumerate(weights):
                if p <= w:
                    count[w] += 1
                    if idx > 0: fout.write('%5d %5d %5d\n'  % (k, j, idx))
                    break

print(count)

    

