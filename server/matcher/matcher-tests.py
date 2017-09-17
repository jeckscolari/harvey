import matcher

try:
    import pytest
except:
    raise ImportError("Error importing pytest. Make sure its installed")



# format: (modelformula,reactionformula,target)
cases = [

    ("a.(c) | b.(d) ",
     " a.($0) | b.($1) -> f.($0) | a.($1) ",
     " f.(c) | a.(d) "),

    (" dummy[d] | a[link].(c|n) | b ",
     "a[link].(c|$0) | b |$1-> b.($0)|$1",
     "b.(n) | dummy[d]"
     ),

    (" a[link].(c|n) | b ",
     "a[link].($0) |$1 -> b.($0)|$1",
     " b.(c | n) |b"
     ),

    (" a | b | a ",
     " a | b |$0-> b|$0 ",
     [" b|a ", "b|a "]
     ),

    (" a.(c) | a.(d) | b  ",
     " a.($0) | $1 -> b.($0) | $1 ",
     [" b.(d) | a.(c) | b ", " b.(c) | a.(d) | b "]
     ),

    (" a ",
     " a -> b",
     "b"
     ),

    ("a | b | c",
     "a | $0 | c -> $0",
     "b"),

    (" a.(b|v) ",
     "a.(b | $0) -> a.( b.(c) | $0 ) ",
     "a.( b.(c)|v )"),

    # this does not match because there is nothing for $0 to match
    (" a.(b) ",
     "a.(b | $0) -> a.( b.(c) | $0 ) ",
     None),

    (" z | x ",
     " z |$0 -> z |$0",
     "z|x"),

    # do not match if not site
    (" z | x ",
     " z -> v ",
     "v|x"),

    (" a.(b) | c | d.(g | h) | x ",
     " $0 | d.($1) -> $0 | n.($1) ",
     # "n.(g | h) | a.(b) | c | x"),
     "c | a.(b) | n.(h | g) | x"),


    ("a.(b)",
     "a.(b | $0) -> a.(b.(c) | $0)",
     None),

    ("a.(b)",
     "a.($0) -> c.($0)",
     "c.(b)"),

    ("a | b | c | d",
     "a | b | $0 -> $0",
     "c|d"),

    # *** moving stuff around ***
    (" a.(b.(c)) | x ",
     "$0| a.(b.($1)) -> v | $0 | $1",
     "x|v|c"),

    (" c.(z | x) ",
     " z |$0 -> z |$0 ",
     "c.(x|z)"),

    (" a.(b)|c|x |d.(g|h)  ",
     " $0 | d.($1) -> $0 | n.($1) ",
     "n.(g | h) | c | x | a.(b)"),

    (" c.(z | x) ",
     " z|x |$0 -> z|v |$0 ",
     None),

    ("x.(z.(v))",
     "v->h",
     "x.(z.(h))"),

    ("a | b.(a | b | c) | d",
     "a | $0 | c -> $0",
     "a|d|b.(b)"),

    (" v[o] ",
     "v[?]->v[p]",
     "v[p]"),

    # enter room
    ("""Building.(Agent[x].(something)|Agent[x].(other)|  waitingchair | Room[roomname].(officedesk) )""",
     "Agent[x].($0) | Room[roomname].($1) | $2 -> Room[roomname].($1 | Agent[x].($0)) | $2",
     [
         "Building.(Room[roomname].(Agent[x].(something) | officedesk) | Agent[x].(other) | waitingchair)",
         "Building.(Room[roomname].(Agent[x].(other) | officedesk) | Agent[x].(something) | waitingchair)"
     ]
     ),
    (
        "a|b|c",
        "a|$0->a.($0)",
        "a.(c | b)"
    ),

    (
        "a|b|a",
        "a|$0->a.($0)",
        ["a.(a | b)", "a.(a | b)"]
    ),

    (
        "a|a",
        "a|$0->a.($0)",
        ["a.(a)", "a.(a)"]
    ),

    (" a|k.(a) ",
     "a|$0->b|$0",
     "b|k.(a)"
     ),

    ("a[v]|a",
     "a[v]|a->n",
     "n"),


    ("z.( a|k.(a) )",
     "a|$0->b|$0",
     "z.(b|k.(a))"
     ),

    # eat one a
    ("b | a | a | a",
     "b | a |$1-> b|$1",
     ["b | a | a ",
      "b | a | a ",
      "b | a | a ",
      "b | a | a ",
      "b | a | a ",
      "b | a | a "]),

    (
        "a|a|a",
        "a|$0->a.($0)",
        ["a.(a | a)", "a.(a | a)", "a.(a | a)"]
    ),


    # multiple matches
    (
        "l.(a)| l.(a)| l.(a)",
        "l.(a)|$1 -> z|$1",
        ["z | l.(a) | l.(a)", "z | l.(a) | l.(a)", "z | l.(a) | l.(a)"]
    ),



    ("l.(a|b)|  l.(a|b)",
     "l.(a|$0)|$1 -> z|$0|$1",
     ["z | b | l.(a | b)",
      "z | b | l.(a | b)"]),

    (
        "z.(a | b.(a | b) )",
        "z.(a | $0) -> $0",
        "b.(b | a)"
    ),

    # ),

    ("a|a|a[e]",
     "a|$0->z.($0)",
     ["z.(a[e] | a)",
      "z.(a[e] | a)"
      ]
     ),

    ("a|a|a",
     "a|$0->z.($0)",
     ["z.(a | a)",
      "z.(a | a)",
      "z.(a | a)"]),

    # wildcard links
    ("a[q]|a[o]",
     "a[?]|$1->b|$1",
     [
         "b | a[o]",
         "b | a[q]"
     ]
     ),

    # sites and backtracking!
    ("a | b.(a | b | c) | c",
     "a | $0 | c -> $0",
     ["b.(b | c | a)", "c | a | b.(b)"]
     ),


    ('City.(Block.(BldConn[x,y] | Building[x].(Drone.(Victim) | Victim) | Building[y] | Building[bla]) | Block.(Building[y] | Building[bla] | BldConn[x,y] | Building[x].(Victim | Drone.(Victim2))) | Block)',
     '$2 | Building[@a].(Drone.($1) | Victim) -> $2 | Building[@a].(Drone.($1 | Victim))',
     ['City.(Block.(BldConn[x,y] | Building[bla] | Building[y] | Building[x].(Drone.(Victim | Victim))) | Block.(Building[y] | Building[bla] | BldConn[x,y] | Building[x].(Victim | Drone.(Victim2))) | Block)',
      'City.(Block.(BldConn[x,y] | Building[x].(Drone.(Victim) | Victim) | Building[y] | Building[bla]) | Block.(Building[bla] | Building[y] | Building[x].(Drone.(Victim2 | Victim)) | BldConn[x,y]) | Block)'
      ]),

    ('Room[t] | Door[r,t] | Room[x].(Doctor) | Room[y] | Room[r].(Doctor) | Door[x,y]',
     'Room[@a].(Doctor) | Door[@a,@b] | $0 | Room[@b] -> Room[@b].(Doctor) | Room[@a] | $0 | Door[@a,@b]',
     [
         'Room[t].(Doctor) | Room[r] | Room[x].(Doctor) | Door[r,t] | Room[y] | Door[x,y]',
         'Room[t] | Room[y].(Doctor) | Room[x] | Door[r,t] | Door[x,y] | Room[r].(Doctor)',
     ]),

    ("a[q,k]|a[o,k]",
     "a[?,k]|$1->b[z,k]|$1",
     ["b[z,k] | a[o,k]", "b[z,k] | a[q,k]"])
]


@pytest.mark.parametrize("modelformula,reactionformula,target", cases)
class TestIokeMatcher:

    def setup(self):
        print ("setup             class:TestStuff")

    def teardown(self):
        print ("teardown          class:TestStuff")

    def setup_class(cls):
        print(("setup_class       class:%s" % cls.__name__))

    def teardown_class(cls):
        print(("teardown_class    class:%s" % cls.__name__))

    def setup_method(self, method):
        print(("setup_method      method:%s" % method.__name__))

    def teardown_method(self, method):
        print(("teardown_method   method:%s" % method.__name__))

    def test_generator(self, modelformula, reactionformula, target):

        def rm_space(i):
            return i.replace(" ", "")

        f = matcher.Bigraph(modelformula)
        b = matcher.RxProp(reactionformula)
        new_bigraphs = matcher.match_iso(f, b)
        if isinstance(target, list):
            for i in target:
                print(target)
                print(new_bigraphs)
                assert any([r == matcher.Bigraph(i) for r in new_bigraphs])
        elif target is None:
            print('new_bigraphs', new_bigraphs)
            if len(new_bigraphs):
                assert all(x == None for x in new_bigraphs)
            else:
                assert True

        else:

            if len(new_bigraphs):
                assert matcher.Bigraph(target) == new_bigraphs[0]




class TestIo:

    def setup(self):
        print ("setup             class:TestStuff")

    def teardown(self):
        print ("teardown          class:TestStuff")

    def setup_class(cls):
        print(("setup_class       class:%s" % cls.__name__))

    def teardown_class(cls):
        print(("teardown_class    class:%s" % cls.__name__))

    def setup_method(self, method):
        print(("setup_method      method:%s" % method.__name__))

    def teardown_method(self, method):
        print(("teardown_method   method:%s" % method.__name__))

    def test_io(self,tmpdir):

        p = tmpdir.mkdir("sub").join("hello.txt")
        p.write("content")
        assert p.read() == "content"
        assert len(tmpdir.listdir()) == 1


        # TODO

        model_formula = """
        Casa.(
           Room[kitchen].( Door[sliding]| Door[pivot] | Light[on] |Agent[due] )
          |Room[bedroom].(   Door[sliding] | Agent[tre] ) 
          |Room[living].(     Door[pivot] | Window[one,two] )
          )
        """
        model = matcher.Bigraph(model_formula)
