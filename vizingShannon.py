# vizingShannon.py
'''
This program edge-colors a multigraph with no more than K colors,  where K is the 
lesser of Vizing's bound (Delata + mu) and Shannon's bound (floor(3*Delta/2)).  
Here Delta is the maximum vertex degree, and mu is the maximum multiplicity 
(number of parallel edges).  I got this from  www.mathcs.emory.edu/~rg/vizing.pdf, 
last downloaded on April 9, 2015.  When I first saw this some time ago, I thought
the proof couldn't easily be turned into an algorithm, but I was wrong, as the 
comments will show.

The program reads a multigraph from file, edge colors it with
min((Delta + mu), floor(3*Delta//2)) colors, and writes the 
colored graph to an output file.  Here Delta is the maximum vertex degree
and mu is the maximum edge multiplicity (the maximum number of parallel) edges.

Delta + mu is Vizing's bound, and floor(3*Delta//2) is Shannon's bound.  Ron Gould,
who posted the proof (obtained from B. Toft) says is the "Book proof" of the two 
theorems, referring to Erdos's conceit that God has a Book with all the best proofs
of all the theorems.  Erdos would describe an elegant proof as "from the Book." I
have to agree that this proof belongs in the Book.
'''
from __future__ import division
import sys, os
from collections import namedtuple
import random

class Edge:
    def __init__(self, ident, x, y, m, G):
        self.ident = ident   # for output
        self.x = x              # endpoints
        self.y = y 
        self.m = m             # multiplicity
        self.color = 0        # uncolored
        self.G = G              # the multigraph
        
    def colorWith(self, c):
        a = self.color
        if a:
            self.x.colors.remove(a)
            self.y.colors.remove(a)
        self.color = c
        self.x.colors.add(c)
        self.y.colors.add(c)
        
    def __str__(self):
        # for debugging
        x = self.x
        y = self.y
        c = self.color
        return 'id: %d x: %d y:%d c: %d %s %s' %(
                 self.ident, x.ident, y.ident, c, c in x.colors, c in y.colors)
    
class Vertex:
    def __init__(self, ident, G):
        self.ident = ident     # for debugging
        self.edges = set()    # edges incident on this vertex
        self.colors = set()    # colors of incident edges
        self.G = G                 # the multigraph
        
    def present(self, c):
        return c in self.colors
    
    def missing(self, c):
        return c not in colors
    
    def degree(self):
        return len(self.edges)
    
    def missingColors(self):
        return self.G.colors - self.colors
    
    def withColor(self, c):
        # Pre: c in self.colors
        for e in self.edges:
            if e.color == c:
                return e
    
'''
A fan anchored at vertex x is an ordered sequence of distinct edges 
e0, e1, ..., en all incident on x, with non-anchor vertices y0, y1, ..., yn, 
such that for each edge ej with 1 <= j <= n, there exists an i, 0 <= i < j, 
such that the color of edge ej is missing at vertex yi.  Each edge of 
the fan is colored, exept for e0, which is uncolored.

When we are coloring the edges, and encounter an edge e such that no
color is missing at both endpoints of e, we will construct a fan, anchored
at one of the endpoints, with e0 = e, and use this to recolor some edges
so that e can be colored.

Note that if e0, e1, ..., en is a fan anchored at x, then so is e0, e1, ..., ek
for any 0 <= k < n.  Also, even though all the edges ej are distinct, since
this is a multigraph, it is quite possible that yi = yj for some i != j.

The important operation on a fan is what I will call "folding" it.  (Think 
of a Japanese fan.)  The fan is foldable if some color c is missing at
both x and yn where en = (x, yn) is the last edge of the fan.  
Let the color of ej be b.  By the definition of a fan, there is some i, with 
0 <= i < n, so that b is missing at yi.  Now, we can recolor en with c,  since c 
is missing at both x and yn, and still have a valid edge-coloring.  Now, e0, 
e1, ..., ei is a fan with fewer edges, and b is missing at both x and yi.  
That is, e0, e1, ..., ei is foldable, so we  can repeat the process until we 
arrive  at a fan with just the edge e0, with a color c missing at both x and y0.  
We can then color e0 with c.  But e0 = e, the edge we were trying to color, 
so we can move on to the next edge.

Another possibility is that as we add an edge (x, yj) it will turn out that there
is some i, 0 <= i < j, so that the same color is missing at both yi and yj, and
yi != yj.  (Since this is a multgraph, it is possible that yi == yj even though
ei != ej.)  The comments to reduce() below explain how to "reduce" the fan 
(replace it by a foldable fan) in this case.  

Finally, the paper cited at the beginning of vizingShannon.py proves that one of
these cases must occur, so that we always get to a foldable fan.  This proof
is paraphrased in the comments to nextEdge().
'''

class Fan:
    '''
    Pre: e is an uncolored edge, and there is no color missing 
           at both endpoints of e.
    Construct a fan anchored at one endpoint of e.  Once one of the conditions 
    explained in the comments occurs, the constructor will reduce the fan until 
    e is colored.  That is, calling Fan(e) will properly color e, and we will have
    no further use for the fan.
    '''
    
    def __init__(self, e):
        # Heuristic: Choose the endpoint with lower degree as anchor.
        self.x = e.x if e.x.degree() <= e.y.degree() else e.y  # heuristic
        # The "rim" comprises the non-anchor vertices of the fan
        self.rim = [e.y if self.x == e.x else e.x]
        self.fan = [e]
        done = False
        # possible edges to be added to the fan
        self.candidates = [e for e in self.x.edges if e.color != 0]
        # colors missing at one or more of the rim vertices
        self.missingColors = self.rim[0].missingColors()
        while not done:
            f = self.nextEdge()
            self.append(f)
            y = self.rim[-1]
            if y.missingColors() & self.x.missingColors():
                self.fold()
                done = True
            else:
                reduc, idx = self.reducible()
                if reduc:
                    self.reduce(idx)
                    done = True
                
    def nextEdge(self):
        '''
        Choose the next edge en of the fan such that the color of en is missing at one 
        of the existing edges of the fan.  If we can always do this provided that the fan
        is not foldable or reducible, then since  there are only finitely many edges, we 
        must eventually arrive at a foldable or reducible fan, and as explained above, we
        can then color edge e.
        
        Suppose, on the contrary that we have a fan with n edges that is not foldable 
        or reducible, but that no suitable next edge exists.  For each vertex v, let M(v) 
        be the set of colors missing at v.  Let M'(x) be the colors at x that are not in 
        the fan.  For each i, 0 <= i <= n, M'(x) and M(yi) are disjoint, for otherwise, we
        could add a new edge to the fan.  Let z0 (=y0), z1, ..., zm be the different yi.
        The the M(z0), M(z1), ..., M(zm) are pairwise disjoint, because the fan is not
        reducible, and M(x) is disjoint from each of them, since the fan is not foldable.
        M(x) and M'(x) are obviously disjoint, so M(z0), M(z1), ... , M(x), and M'(x) are
        pairwise disjoint.  If there are K available colors, then 
                         |M(z0)| + |M{z1)| + ... + |M(zm)| + |M(x)| + |M'(x)| <= K. 
        Now for 1 <= j <= m, |M(zj)| >= K - deg(zj), but we know there is an uncolored
        edge at y0, so |M(z0)| >= K - deg(z0) + 1.   Let p(x) be the number of colors 
        present at x.  Then |M(x)| = K - p(x) and |M'(x)| = p(x) - (n-1), since the fan 
        has one uncolored edge.  Putting all this together,
        
            K - deg(z0) + 1 + sum([K - deg(zj)], 1 <= j <= m) + K - p(x) + p(x) -(n-1) <= K
    
            (m+2)K - sum([deg(zj)], 0 <= j <= m) - n + 2 <= K
          
            2 <= sum([deg(zj)], 0 <= j <= m) + n - (m+1)K.
            
        Let m(x, zj) be the number of edges  between x and zj.  Then
        n <= sum([m(x, zj)], 0 <= j <= m).  Then the following inequality holds:
        
           2 <= sum([deg(zj) + m(x, zj) - K],  0 <= j <= m), where m >= 1 (see below).
           
        So there is some j such that deg(zj) + m(x, zj) - K > 0.  Then Delta + mu > K, so
        K is less than Vizing's bound.  Also, since m >= 1, there are two distinct vertices
        zi and zj such that
        
           2 <= deg(zi) + m(x, zi) - K + deg(zj) + m(x, zj) - K.
        
        Since deg(x) >= m(x, zi) + m(x, zj),
        
           2(K+1) <= deg(zi) + deg(zj) + deg(x) <= 3 * Delta, 
        
        so K is also less than Shannon's bound.  This is a contradiction, since K is chosen
        as the lesser of Shannon's bound and Vizing's bound.
        
        To see that m >= 1, we only have to confirm that at least one edge not parallel to
        e0 is added to the fan.  To add e1, we must find a color present at x and missing 
        at y0.  If there is no such color, then every color present at x is present at y0, so 
        every color missing at y0 is missing at x.  There is a color missing at y0 (K > Delta), 
        but if it were missing at x,  we would would not build the fan in the first place,
        contradiction, and we can add an edge e1 to the fan.  The color of e1 is present at 
        y1 and missing at y0, so y0 != y1 and e0 and e1 are not parallel.
        '''
        x = self.x
        for e in self.candidates:
            if e.color in self.missingColors:
                return e   # self.append will remove e from self.candidates 
            
    def append(self, e):
        # add edge e to the fan and do all the bookkeeping
        self.fan.append(e)
        self.candidates.remove(e)
        y = e.y if e.x == self.x else e.x
        self.rim.append(y)
        self.missingColors |= y.missingColors()
        
    def fold(self):
        fan, rim, x = self.fan, self.rim, self.x
        xMissing = x.missingColors()
        for new in xMissing & rim[-1].missingColors():
            break
        old = fan[-1].color
        fan[-1].colorWith(new)
        if len(fan) > 1:
            for idx, y in enumerate(rim[:-1]):
                if old in y.missingColors(): break
            self.fan = fan[:idx+1]
            self.rim = rim[:idx+1]  
            self.fold()
               
    def reducible(self):
        # Return (False, None) if irreducible
        # Otherwise, return (True, i) where i is the index of the
        # rim vertex we found.
        yn = self.rim[-1] 
        missing = self.rim[-1].missingColors()
        for idx, y in enumerate(self.rim[:-1]):
            if y != yn and (missing & y.missingColors()):
                return(True, idx)
        return (False, None)

    def reduce(self, i):
        '''
        Pre: yi is the first vertex on the rim with yi != yn (the last vertex on the rim)
        such that some color a is missing at both yn and yi.  The fan e0, ..., en is not
        foldable.  For 0 <= k < n, the fan e0, ..., ek is neither foldable nor reducible.
        Note that if yk = yn for some k < i then e0, ..., ei would be a reducible fan,
        contradiction, so that yi is the first vertex on the rim with a missing.
        
        Let b be any color missing at x.  Since we only get here if the fan is not
        foldable, b is present at every rim vertex.  An a-b chain is a maximal sequence
        of adjacent edges alternately colored a and b.  Such a chain must be a 
        simple path or a simple cycle, since all its vertices are of degree 1 or 2.
        We will only consider the a-b chain Pi starting at yi and the a-b chain 
        Pn starting at yn.  Since a is missing at both the rim vertices, both the 
        chains are simple paths.
    
        We can swap the colors on an a-b chain, coloring every a-colored edge
        on the chain with b, and vice versa.  We still have a valid coloring
        of the graph.  The colors don't change at the interior vertices of the
        chain, and at the endpoints (if any) we are replacing the current color
        with a color missing at the endpoint.    
        
        It is not possible for Pi and Pn both to reach x.  Both chains must
        reach x by the unique a-colored edge at x, since b is missing at x,
        so Pi and Pn are the same chain.  But then x, yi, and yn are three 
        distinct endpoints of this chain, which is absurd.
        
        Now suppose that x is not on Pi.  When we reverse the colors on Pi,
        I claim that e0, e1, ..., ei is still a fan.  Since x is not on Pi, we have 
        not re-colored any of the fan edges.  We have to check 
        whether some color missing at one of the vertices y0, y1, ... yi-1 is 
        now present, since that might destroy the fan property. But the only 
        colors that have changed are a and b, and b was originally present at 
        every rim vertex, and a was present at y0, ..., yi-1.  After reversing
        the colors, b is missing at x and yi, to the fan is foldable.
        
        Suppose then that x is on Pi.  Then x is not on Pn. When we swap the
        colors on Pn, e0, e1, ..., en is still a fan.  As before we only have to
        check whether a is present at some vertex at which it was missing
        before.  In fact, since yi was the first vertex at which a was missing,
        we only have to show that a is still missing at yi.  The colors at yi
        can have changed only if Pn reaches x, but since Pi reaches x, Pn 
        would then reach x, contradiction.  Since b is now missing at x and at yn,
        the fan is foldable.
        '''
        x = self.x
        yi = self.rim[i]
        yn = self.rim[-1]
        a = random.sample((yn.missingColors() & yi.missingColors()), 1)[0]
        b = random.sample(x.missingColors(), 1)[0]
        if self.chain(yi, a, b, x):
            self.fan = self.fan[:i+1]
            self.rim = self.rim[:i+1]
            self.fold()
        else:
            self.chain(yn, a, b, x)
            self.fold()
    
    def chain(self, y, a, b, x):
        # Construct a-b chain at y.  If the last vertex is  not x, swap the colors.
        # Return True if colors swapped, else return False
        # Pre: b present at y, a missing at y
        current = b
        z = y
        chain = []
        while current in z.colors:
            e = z.withColor(current)
            chain.append(e)
            z = e.y if e.x == z else e.x  
            current = a if current == b else b
        if z != x: 
            self.swapColors(chain, a, b, y, z)          
        return z != x
    
    def swapColors(self, chain, a, b, init, term):
        #  We can't use Edge.colorWith to swap the chain colors, because
        # it assumes a properly colored graph, and as soon as we swap the
        # first color, this isn't true
        
        for e in chain:
            e.color = a if e.color == b else b
        for (v, e) in ((init, chain[0]), (term, chain[-1])):
            new, old = (a, b) if e.color == a else (b, a)
            v.colors.add(new)
            v.colors.remove(old)
        
class Multigraph:
    def __init__(self, infile, progress = True):
        self.infile = infile
        self.progress = progress
        self.vertices = dict()
        self.edges = dict()
        self.mu = self.getData(infile)
        self.Delta = 0
        for v in self.vertices.values():
            self.Delta = max(self.Delta, v.degree())
        K = min(self.Delta + self.mu, 3*self.Delta//2)
        print('|V| = %d |E| = %d Delta = %d mu = %d K = %d' %
              (len(self.vertices), len(self.edges), self.Delta, self.mu, K))
        self.colors = set()
        for c in range(1, K+1):
            self.colors.add(c)
        
    def edgeColor(self):
        edges = self.edges
        N = len(edges)
        placebo = self. progress
        for e in edges.values():
            if placebo and (e.ident % 10000==0):
                pct = 100*e.ident/N
                sys.stdout.write("\rColoring edge %d %.2f %%  " %(e.ident, pct))
                sys.stdout.flush()
            both = e.x.missingColors() & e.y.missingColors()
            if both:
                e.colorWith(random.sample(both, 1)[0])
            else:
                Fan(e)
    
    def getData(self, infile):
        mu = 0
        vertices = self.vertices
        edges = self.edges
        try:
            with open(infile) as fin:
                try:
                    N = int(next(fin))
                except ValueError:
                    print('Illegal value for N in line 1\n')
                    exit()
                for k in range(N):
                    vertices[k] = Vertex(k, self)
                count = 2
                goodData = True
                for line in fin:
                    line = line.split()
                    if not line: continue
                    goodLine = True
                    try:
                        x, y, m = map(int, line)
                    except ValueError:
                        print('Illegal input in line %d\n' % count)
                        count += 1
                        goodData = False
                        continue
                    for v in (x, y):
                        if not 0 <= v < N:
                            print('Illegal vertex %d at line %d\n' % (v, count))
                            goodLine = False         
                    if not 0 < m:
                        print('Multiplicity must be positive at line %d\n' % count)
                        goodLine = False                
                    if not goodLine:
                        goodData = False
                    if goodData:
                        mu = max(mu, m)
                        for k in range(m):
                            vx, vy = vertices[x], vertices[y]
                            e = edges[count] = Edge(count,vx,vy,m,self)
                            for v in (vx, vy):
                                v.edges.add(e)
                            count += 1
            if not goodData:
                print("Bad input data ... aborting")
                exit()
            return mu
        except IOError:
            print("Could not open input file\n" % infile)
            exit()        
            
    def ouputColors(self, outfile):
        self.outfile = outfile
        header = 'N %d M %d Delta %d mu %d colors %d\n' %( 
              len(self.vertices),len(self.edges), self.Delta, self.mu, len(self.colors)) 
        sys.stdout.write('\r'+header)
        sys.stdout.flush()
        length = len(str(len(self.edges)))
        fs = ('%%%dd %%%dd %%%dd %%%dd\n' % (length, length, length, length))
        try:
            with open(outfile, 'w') as fout:
                fout.write(header)
                for e in self.edges.values():
                    fout.write(fs % (e.x.ident, e.y.ident, e.m, e.color))
        except IOError:
            print("Could not open output file/n")
            exit()
            
    def invariant(self):
        # Is the grapgh properly colored so far?
        # test that for every colored edge, the color is listed at both ends
        for e in self.edges.values():
            a = e.color
            if a and (a not in e.x.colors or a not in e.y.colors):
                return False
        #test that for each vertex, there are no duplicate colors
        for v in self.vertices.values():
            ec = [e for e in v.edges if e.color]
            if len(v.colors) != len(ec):
                return False
            if {e.color for e in ec} != v.colors:
                return False
        return True
                
    def audit(self):
        #Pre: self.outputColors has already been called
        # Return True if all checks passed
        vertex = namedtuple('vertex', 'degree colors' )
        vertices = list()
        infile = open(self.infile, 'r') 
        outfile =open(self.outfile, 'r') 
        N1 = int(next(infile))
        line = next(outfile).split()[1:10:2]
        N, M, Delta, mu, K = map(int, line)
        if N1 != N:
            print('Number of vertices differ in input and output files\n')
            exit()
        for n in range(N):
            vertices.append(vertex(0, set()))
        count_o = 1     # line count in output file
        count_i  = 1    # line count in input_file
        for line in infile:
            count_i += 1
            if not line.strip(): continue
            x,y,m = map(int, line.split())
            for k in range(m):
                count_o += 1
                x1, y1, m1, color = map(int, next(outfile).split())
                if x != x1 or y != y1 or m != m1:
                    print("inconsistent data:")
                    print("\tinput file  line %d: %d %d %d" %(count_i, x,y,m) )
                    print("\toutput file line %d: %d %d %d %d" %(count_o, x1, y1, m1, color ))
                    return(False)
                if not 1 <= color <= K:
                    print("Illegal color %d in output line %d" %(color, count_o))
                    return False
                for v in x, y:
                    degree, colors = vertices[v]
                    degree += 1
                    colors.add(color)
                    vertices[v] = vertex(degree, colors)
        for idx, (degree, colors) in enumerate(vertices):
            if degree != len(colors):
                print("Duplicate colors at vertex %d"  % idx)
                return False
        return True
    
def main():
    if len(sys.argv) != 3:
        print('Usage: %s infile outfile' % os.path.basename(sys.argv[0]))
    from time import time
    start = time()
    G = Multigraph(sys.argv[1])
    G.edgeColor()
    G.ouputColors(sys.argv[2])
    print("Coloring complete. %.2f seconds\nChecking" %(time()-start))
    start = time()
    result = G.audit()
    if not result:
        print('**** Failed audit ****  time %.2f seconds' % (time() -start))
    else:
        print("All tests passed.  Time %.2f seconds" % (time() -start))

if __name__ == '__main__':
    main()
 