# -*- coding: utf-8 -*-
"""
helper functions.
"""

import string
import copy
from operator import eq
import itertools

def atomset(e):
    """ treat None as empty set """
    return set() if e is None else e


def remove_from_list(l, removelist):
    """ remove multiple items from list"""
    return [v for i, v in enumerate(l) if v not in removelist]


def list_contains(small, big):
    """ check if all elements of small are contained in big """
    for i in range(len(big) - len(small) + 1):
        for j in range(len(small)):
            if big[i + j] != small[j]:
                break
        else:
            return i, i + len(small)
    return False

#> def longest_path(G):



def flatten(*args):
    """ generator that flattens nested structure to list of elements """
    for x in args:
        if hasattr(x, '__iter__'):
            for y in flatten(*x):
                yield y
        else:
            yield x


class frozendict(dict):
    def _blocked_attribute(obj):
        raise AttributeError("A frozendict cannot be modified.")
    _blocked_attribute = property(_blocked_attribute)

    __delitem__ = __setitem__ = clear = _blocked_attribute
    pop = popitem = setdefault = update = _blocked_attribute

    def __new__(cls, *args, **kw):
        new = dict.__new__(cls)
        args_ = []
        for arg in args:
            if isinstance(arg, dict):
                arg = copy.copy(arg)
                for k, v in list(arg.items()):
                    if isinstance(v, dict):
                        arg[k] = frozendict(v)
                    elif isinstance(v, list):
                        v_ = list()
                        for elm in v:
                            if isinstance(elm, dict):
                                v_.append( frozendict(elm) )
                            else:
                                v_.append( elm )
                        arg[k] = tuple(v_)
                args_.append( arg )
            else:
                args_.append( arg )

        dict.__init__(new, *args_, **kw)
        return new

    def __init__(self, *args, **kw):
        pass

    def __hash__(self):
        try:
            return self._cached_hash
        except AttributeError:
            h = self._cached_hash = hash(tuple(sorted(self.items())))
            return h

    def __repr__(self):
        return "frozend(%s)" % dict.__repr__(self)


def draw_dot(g, name):
    """ render graph g in name.png using pydot """
    try:
        import pydot
    except:
        raise Exception('Error importing pydot, can not plot this graph')
    d = pydot.Dot(name=name)
    d.set_type('digraph')

    for node in g.nodes():
        label = str(node)+"\n"+str(g.node[node])
        d.add_node(pydot.Node(str(node),label=label))
    for edge in g.edges():
        d.add_edge(pydot.Edge(str(edge[0]), str(edge[1])))
    d.write_png(name + '.png')
    d.write_dot(name + '.dot')

    print(name + '.png')



def uniquefy(seq): 
    """ uniquefy sequence, elements need not be hashable """
   # order preserving
    noDupes = []
    [noDupes.append(i) for i in seq if not noDupes.count(i)]
    return noDupes


def ports_wildcard_check(mli, rli):
    # special case, wildcards
    if rli and mli:
        if any("@" in s for s in rli):
            # handle it later 
            return True
        # get positions that differ
        different_pos = [i for i, (m, r) in enumerate(zip(mli, rli)) if m != r and (m!='?' and r!='?')]
        return len(different_pos)==0 and len(mli)==len(rli)
    elif rli is None and mli is None:
      return True
    else:
      return False

def eq_overload_wildcard(left,right):
  try:
    return ports_wildcard_check(left,right)
  except:
    return eq(left,right)

def eq_overload_world(left,right):
  if left=="world" or right=="world":
    return True
  if left==right:
    return True
  return eq(left,right)

