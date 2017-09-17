# -*- coding: utf-8 -*-
"""
Various checking helpers
"""

from operator import eq

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
