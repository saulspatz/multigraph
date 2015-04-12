'''
Implementation of the Hungarian method of solving the assignment problem.
Given a complete, weighted bipartite graph with bipartition sets X and Y,
and card(x) = card(Y), find a complete matching of optimum weight.

We follow the outline at http://www.cse.ust.hk/~golin/COMP572/Notes/Matching.pdf
but change the expanation in terms of "neighbor vertices" to a simpler one in
terms of "candidate edges", and we minimize instead of maximizing.

Call an assignment L of real numbers to the vertices an "labeling" if
for every edge xy, we have L(x) + L(y) <= w(xy,) where w is the weight.
Call an edge xy "tight" (w.r.t L) if L(x) + L(y) = w(x,y).
It can be shown that a complete matching in which every edge is tight
is of minimal weight.

The algorithm employs an alternating tree A.  This is a tree with the properties
- the root is a free vertex in X
- every edge is tight
- every path from the root to a leaf alternates between edges not in the 
  match M constructed so far, and edges in M.

Call an edge xy a "candidate edge" if 
 - it is tight
 - x is in A (and in X)
 - y is not in A (and in Y)
 
 A candidate edge can be attached to A at x and the resulting tree will be
 alternating.
 
 The algorithm is:
 Consruct a trivial labeling.
 While M is not complete:
     choose a free X-vertex u and make it the root of A
     loop forever
        - choose a candidate edge xy (if none exists, we
        can relabel the vertices so that the edges in A and M
        remain tight, and at least one candidate edge exists)
        - add xy to A
        - if y is free, then the path from u to y is augmenting,
          so augment M and break out of the inner loop
        - if y is matched in M to z, say, then add edge yz to A.
'''

class Tree():
    '''
    A directed tree.  Each vertex knows its parent
    '''
    def __init__(self, root):
        self.root = root
        self.parent = {root:None}
        self.S = set([root])     # X-vertices in tree
        self.T = set()               # Y-vertices in tree
                              
    def path2(self, y):
        '''
        Return path from y to root.   
        '''
        path = [y]
        while y != self.root:
            y = self.parent[y]
            path.append(y)
        return path
        
    def add(self, v1, v2):
        '''
        Pre: v1 is in the tree. 
        Add edge (v1, v2) to the tree.
        '''
        self.parent[v2] = v1
        if v1 in self.S:
            self.T.add(v2)
        else:
            self.S.add(v2)
            
class Matching(set):
    '''
    The set of matched edges
    '''
    def __init__(self, X, Y):
        super().__init__()
        self.freeX = X.copy()
        self.freeY = Y.copy()
    
    def augment(self, path):
        '''
        Pre: 
          path is a list of vertices whose first and last entries are free.
          The first is in Y and the last in X.
          Pairs of consecutive vertices are considered as edges.
          The edges alternate between unmatched and matched.
        Post:
           Matching is augmented by exchanging the matched and unmatched
           edges in the path.
        '''
        self.freeY.remove(path[0])
        self.freeX.remove(path[-1])
        for idx, v in enumerate(path[:-1]):
            if idx % 2 == 0:
                edge = path[idx+1], v
                self.add(edge)
            else:
                edge = v, path[idx+1]
                self.remove(edge)
                
    def getFreeX(self):
        '''
        Return an unmatched X-vertex
        '''
        answer = self.freeX.pop()
        self.freeX.add(answer)
        return answer
    
    def matchingX(self, y):
        '''
        Return the X-vertex matched to y
        '''
        for x, v in self:
            if v == y:
                return x
            
class Hungarian:
    def __init__(self, weight):
        '''
        weight is a dict whose keys are tuples (x, y) with x in X and y in Y, and
        whose values are the weights of t.  By default, the weight will be
        minimized.
        
        The vertices will usually be strings, but they can be any immutable
        objects, provided that they are all distinct.  No vertex may be in
        both X and Y.
        
        The only methods that user should call explicitly are solveMin and solveMax.
        
        After solving, the object has the following atrributes of interest:
        X -- bipartition set
        Y -- bipartition set
        matchX -- dict giving the match; key is any X-vertex
        matchY -- inverse dict of matchX
        value -- sum of the weights of edges in M
        '''
        self.weight = weight
        X = self.X = set([k[0] for k in weight])
        Y = self.Y = set([k[1] for k in weight])
        self.setup()
        self.audit()
               
    def setup(self):
        self.M = Matching(self.X, self.Y)
        self.value = 0
        self.labels = dict()  # vertex labels 
        self.slack = dict()    # for improving labeling and finding candidates        
        
    def audit(self):
        weight = self.weight
        X, Y = self.X, self.Y
        if len(X) != len(Y):
            raise ValueError("X and Y must be same size")
        for x in X:
            for y in Y:
                if not (x, y) in weight:
                    raise KeyError("No weight given for edge (%s, %s)" % (x,y))
                if not isinstance(weight[x,y], (int, float)):
                    raise ValueError("%s is not a legal weight for edge (%s, %s)" %(weight[x,y],x,y))
                
    def solveMin(self):
        self.setup()
        X, Y, M = self.X, self.Y, self.M
        w , labels, slack = self.weight, self.labels, self.slack
        for y in Y:
            labels[y] = 0
        for x in X:
            labels[x] = min(w[x, y] for y in Y)        
 
        while len(M) < len(X):
            u = M.getFreeX()       # is the root of the alternating tree
            for y in Y:
                slack[y] = w[u,y] - labels[u] - labels[y]
            A = self.A = Tree(u)        
            while (True):
                y = self.candidate()
                for s in A.S:
                    if labels[s] + labels[y] == w[s,y]:
                        z = s
                        break
                A.add(z, y)
                if y in M.freeY:
                    path = A.path2(y)
                    M.augment(path)
                    break
                else:
                    z = M.matchingX(y) 
                    A.add(y, z)
                    # update the slacks
                    for y in  Y - A.T:
                        slack[y] = min(slack[y], w[z, y] - labels[z] - labels[y])
        self.wrapup()
                
    def candidate(self):
        '''
        It's too inefficient to maintain a list of the candidate edges, but we can
        find a Y-vertex on a candidate edge simply by finding one not on the
        tree whose slack is 0.  If there is none, we can relabel the vertices so
        that a candidate edge exists, and return the appropriate y.
        '''
        slack, labels = self.slack, self.labels
        alpha = max(slack.values())        # alpha = infinity
        S = self.A.S
        T = self.A.T
        Tbar = self.Y - T
        for y in Tbar:
            s = slack[y]
            if s == 0:
                return y
            if s <= alpha:
                alpha = s
                answer = y
        # No candidate found, so relabel the vertices
        for t in T:
            labels[t] -= alpha
        for s in S:
            labels[s] += alpha
        # and recompute the relevant slacks
        for y in Tbar:
            slack[y] -= alpha
        return answer
                          
    def negate(self):
        weight = self.weight
        for k in weight:
            weight[k] = -weight[k] 
            
    def wrapup(self):
        '''
        Called after solution computed
        '''
        w = self.weight
        self.value = sum([w[e] for e in self.M])
        self.matchX  = {x:y for x, y in self.M}
        self.matchY = {y:x for x, y in self.M}
        
    def solveMax(self):
        self.negate()
        self.solveMin()
        self.negate()
        self.value = -self.value
        
if __name__  ==  '__main__':
    a = 'Albany'
    b = 'Boston'
    c = 'Chicago'
    d = 'Denver'
    e = 'Edmonton'
    f = 'Fargo'
    airfare = {(a,d):250, (a,e):400, (a,f):350,
                     (b,d):400, (b,e):600, (b,f):350,
                     (c,d):200, (c,e):400, (c,f):250}
    h = Hungarian(airfare)
    h.solveMin()
    assert(h.value == 950)
    assert(h.matchX['Boston']=='Fargo')
    h.solveMax()
    assert(h.value==1150)
    assert(h.matchX['Albany']=='Fargo')
    h.solveMin()
    assert(h.value == 950)    
