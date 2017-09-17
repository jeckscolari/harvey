# -*- coding: utf-8 -*-
"""
High-level invoking of the matcher.
"""

from matcher.match2 import *
from matcher.acexp import *
from matcher.bigformula import *


def reaction_invoker(modelstring, reactionstring, outputtype):
    """ invoke the reactor, generating new bigraphs """
    model = Bigraph(modelstring)
    reactions_strings = reactionstring.split(";")
    reactions = []
    for r in reactions_strings:
        reactions.append(RxProp(r))
    new_states = []
    for reaction in reactions:
        # new_states += match_iso(Bigraph(model.formula), reaction)
        new_states += match_iso(model, reaction)
    if outputtype == "proposition":
        return "\n".join([n.props_strings() for n in new_states])
    elif outputtype == "gml":
        prefix=str(id(model))
        for idx, n in enumerate(new_states):
            n.export_gml(prefix+'-'+str(idx))
        print("exported", len(new_states),"gml files with prefix",prefix)
    else:
        return "\n".join([n.formula for n in new_states])


def pattern_invoker(modelstring, patternstring):
    """ return True if any of the ';' delimited patterns matches the model"""
    model = Bigraph(modelstring)
    patterns_strings = patternstring.split(";")
    patterns = []
    for r in patterns:
        patterns.append(RxProp(r))

    for pattern in patterns:
        found = match_iso(Bigraph(model.formula), pattern)
        # need str return values for the C bindings
        if found:
            return str(True)
    return str(False)


def eq_invoker(modelstring, secondmodelstring):
    """ check if two bigraphs are equal """
    model = Bigraph(modelstring)
    second_model = Bigraph(secondmodelstring)
    # need str return values for the C bindings    
    if model == second_model:
        return str(True)
    else:
        return str(False)
