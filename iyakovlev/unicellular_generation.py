from sage.misc.cachefunc import cached_function
from sage.misc.prandom import randint
from sage.functions.other import binomial
from sage.combinat.dyck_word import DyckWords
from sage.combinat.permutation import Permutation
from sage.combinat.subset import Subsets
from sage.combinat.combinat import catalan_number

# SOME CONVENTIONS:
# - the corner corresponding to a half-edge is in the clockwise direction
# - face permutation is always (1,2,3,...)

@cached_function
def C(g,n):
    r"""
    Compute the value of Zagier polynomial C_g(n)
    """
    if g==0:
        return 1
    elif n==2*g:
        return n*(n-1)/2 * C(g-1,n-2)
    return C(g,n-1) + n*(n-1)/2 * C(g-1,n-2)

def random_slicing_sizes(g,ne):
    # generate a random list of sizes of slicings (with the right distribution)
    slicing_sizes=[]
    while g>0:
        i=randint(1,2*g*C(g,ne))
        tmp=0
        j=0
        while(i>tmp):
            j+=1
            tmp+=C(g-j,ne) * 2**j * binomial(ne+1-2*g+2*j,2*j+1)
        slicing_sizes.append(j)
        g-=j
    return slicing_sizes

def dyck_word_to_planar_tree(w):
    # returns edge permutation (assuming face permutation is (1,2,3,...))
    # 1 is the root half-edge
    ep=[]
    ind=[] #indices of unfinished edges in ep
    for i in range(1,len(w)+1):
        if w[i-1]==1:
            ep.append([i,None])
            ind.append(len(ep)-1)
        else:
            ep[ind.pop()][1]=i
    return [tuple(i) for i in ep]

def random_rooted_plane_tree(ne):
    # returns edge permutation (assuming face permutation is (1,2,3,...))
    # 1 is the root half-edge
    assert(ne>0)
    w=DyckWords(ne).random_element()
    return dyck_word_to_planar_tree(w)

def glue_vertices(vp,v):
    # we assume that vp is given as list of cycles, and that face permutation == (1,2,3,...)

    assert len(v)%2==1 
    if len(v)==1:
        return vp
        
    v = sorted(v, key = lambda i : min(vp[i])) # order vertices by first visits
    he = [vp[i].index(min(vp[i])) for i in v] # first visit half-edges

    # compute new labels of half-edges, so that face permutation remains (1,2,3,...)
    new_labels = {}
    k = 1
    while k<vp[v[0]][he[0]]:
        new_labels[k] = k
        k+=1
    for j in range(1,len(v),2):
        for i in range(vp[v[j]][he[j]], vp[v[j+1]][he[j+1]]):
            new_labels[i] = k
            k+=1
    for j in range(0,len(v)-1,2):
        for i in range(vp[v[j]][he[j]], vp[v[j+1]][he[j+1]]):
            new_labels[i] = k
            k+=1
    while k<=sum(len(i) for i in vp):
        new_labels[k] = k
        k+=1
    
    # glue the vertices
    new_vertex = []
    for i,e in zip(v,he):
        new_vertex.extend(vp[i][e:]+vp[i][:e])
    vp = [vp[i] for i in range(len(vp)) if i not in v]
    vp.append(tuple(new_vertex))

    # relabel half-edges
    vp=[tuple(new_labels[i] for i in j) for j in vp]
    
    return vp

def random_rooted_unicellular_map(g,ne):
    r'''
    Generates a uniformly random rooted unicellular map of genus g with ne edges,
    and returns its vertex permutation, assuming the face permutation is (1,2,...,2*ne).
    The root half-edge is labeled with 1.

    The algorithm is based on the CFF bijection from the paper
        Chapuy, Guillaume; Féray, Valentin; Fusy, Éric;
        A simple model of trees for unicellular maps.
        J. Comb. Theory, Ser. A 120, No. 8, 2064-2092 (2013).
    '''
    #returns vertex permutation assuming face permutation=(1,2,3,...)
    #1 is the root half-edge
    assert g>=0
    assert ne>=1
    assert ne+1-2*g>0 
    #C.precompute([(g,n) for n in range(ne+1) for g in range(ne//2+1)],8) #use 8 processors
    slicing_sizes=random_slicing_sizes(g,ne)
    slicing_sizes.reverse()
    ep=random_rooted_plane_tree(ne)
    vp=Permutation(ep)*Permutation([tuple(i for i in range(1,2*ne+1))]) #first permutation is applied first
    vp=vp.cycle_tuples()
    for i in slicing_sizes:
        v=Subsets(len(vp),2*i+1).random_element().list() #choose a random subset of 2*i+1 vertices
        vp = glue_vertices(vp,[i-1 for i in v])
    return Permutation(vp)

def num_rooted_unicellular_maps(g,ne):
    r'''
    Returns the number of isomorphism classes of rooted unicellular maps
    of genus g with ne edges.
    
    The formula is from 
        Harer J., Zagier D. The Euler characteristic of the moduli space of curves.
        Invent. Math., 1986, vol. 85, 457-485.
    See also Section 3.1 in
        S. K. Lando, A. K. Zvonkin, Graphs on surfaces and their applications. 
        Appendix by Don B. Zagier. Berlin: Springer (2004)
    '''
    return C(g,ne)*catalan_number(ne)/2**g