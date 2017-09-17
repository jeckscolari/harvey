# -*- coding: utf-8 -*-
try:
   import pickle as pickle
except:
   import pickle
# from helpers.config import *

# pyparsing is extremely slow for the kind of parsing we do
# so we cache the predicate ASTs
# TODO change parser.

AST_CACHE={}
# ENABLE_CACHE=True
ENABLE_CACHE = False


def initialize_cache():
    global AST_CACHE
    AST_CACHE = {}
    pickle.dump(AST_CACHE, open("pred_cache", "wb"))


def load_cache():
    if ENABLE_CACHE:
        # print 'cache enabled'
        try:
            AST_CACHE = pickle.load(open("pred_cache", "rb"))
        except EOFError:
            print("pred_cache damaged, re-initializing.")
            initialize_cache()
    else:
        # print 'cache disabled'
        AST_CACHE = {}

def save_cache(d):
    if ENABLE_CACHE:
        pickle.dump(d, open("pred_cache", "wb"))
