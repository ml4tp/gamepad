import networkx as nx
import matplotlib.pyplot as plt
import numpy as np

"""
decls ::= ignore | ignore '\n' decls | decl | decl '\n' decls
decl ::= hdr '\n' ctx '============================' '\n' goal

ctx ::= ldecl | 
ldecl ::= id ':' string '\n'

hdr ::= kind '{!}' tac '{!}' full_tac '{!}' int '{!}' int
kind ::= 'AFTER' | 'BEFORE'
tac ::= string
full_tac ::= string
int ::= [0-9]+
"""

"""
AFTER {!} induction n {!}  {!} 10 {!} 2

n : nat
IHn : n + 0 = n
============================
S n + 0 = S n
"""

# -------------------------------------------------
# Data structures

class TacStHdr(object):
    def __init__(self, mode, tac, kind, ftac, gid, ngs, loc):
        self.mode = mode
        self.tac = tac
        self.kind = kind
        self.ftac = ftac
        self.gid = gid
        self.ngs = ngs
        self.loc = loc

    def __str__(self):
        return "({} tac: {}  ftac: {}  gid: {}  ngs: {})".format(
            self.mode, self.tac, self.ftac, self.gid, self.ngs)

class TacStDecl(object):
    def __init__(self, tac_st_hdr, ctx, goal):
        self.hdr = tac_st_hdr
        self.ctx = ctx
        self.goal = goal

    def dump(self):
        return "{}\n{}\n{}".format(str(self.hdr), str(self.ctx), str(self.goal))

    def __str__(self):
        if self.hdr.mode == "before":
            return "B{}{}".format(self.hdr.gid, self.hdr.tac)
        else:
            return "A{}{}".format(self.hdr.gid, self.hdr.tac)

    def __hash__(self):
        s = "{}{}".format(self.hdr.loc, self.hdr.gid)
        return int.from_bytes(s.encode(), "little")
        """
        if self.hdr.mode == "before":
            return self.hdr.gid * 2
        else:
            return self.hdr.gid * 2 + 1
        """

class LemTacSt(object):
    def __init__(self, name, decls):
        self.name = name
        self.decls = decls

    def __str__(self):
        return "{}<{}>".format(self.name, ", ".join([str(decl) for decl in self.decls]))

def mk_root_decl():
    return TacStDecl(TacStHdr("after", "root", "", "", 0, 0, ""), "", "")

def mk_term_decl(gid):
    return TacStDecl(TacStHdr("after", "term", "", "", gid, 0, ""), "", "")    

# -------------------------------------------------
# Parsing utility

class MyFile(object):
    def __init__(self, file):
        self.f_head = file
        self.line = 0

    def raw_consume_line(self):
        self.line += 1
        return self.f_head.readline()

    def consume_line(self):
        self.line += 1
        return self.f_head.readline().rstrip()

    def raw_peek_line(self):
        pos = self.f_head.tell()
        line = self.f_head.readline()
        self.f_head.seek(pos)
        return line

    def peek_line(self):
        pos = self.f_head.tell()
        line = self.f_head.readline().rstrip()
        self.f_head.seek(pos)
        return line

    def advance_line(self):
        self.raw_consume_line()
        return self.peek_line()


# -------------------------------------------------
# Parsing

TOK_SEP = "{!}"
TOK_DIV = "============================"
TOK_BEFORE = "before"
TOK_AFTER = "after"
TOK_BEG_TAC_ST = "begin(tacst)"
TOK_END_TAC_ST = "end(tacst)"
TOK_BEG_SUB_PF = "begin(subpf)"
TOK_END_SUB_PF = "end(subpf)"
TOK_BEG_PF = "begin(pf)"
TOK_END_PF = "end(pf)"

def basic_have_stats(lemmas):
    total = 0;
    haves = 0;
    pfsizes = [];
    for lemma in lemmas:
        size = 0
        for decl in lemma.decls:
            if decl.hdr.mode == "before":
                if decl.hdr.tac == "<ssreflect_plugin::ssrhave@0> $fwd":
                    haves += 1
                total += 1
                size += 1
        pfsizes += [size]
    return len(lemmas), haves, total, 1.0 * haves / (total + 1), np.mean(pfsizes)


def is_goal_end(line):
    """
    return line.startswith(TOK_BEFORE) or \
           line.startswith(TOK_AFTER) or \
           line.startswith(TOK_BEG_SUB_PF) or \
           line.startswith(TOK_END_SUB_PF) or \
           line.startswith(TOK_QED)
    """
    return line.startswith(TOK_END_TAC_ST)

class TacStParser(object):
    def __init__(self, h_file, f_log=False):
        self.f_head = MyFile(h_file)
        self.f_log = f_log
        self.log = []
        self.lems = []
        self.decls = []

    def _mylog(self, msg):
        if self.f_log:
            #self.log.append(msg)
            print(msg)

    def parse_hdr(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_hdr:before<{}>".format(f_head.peek_line()))

        # Parse header
        hdr = f_head.consume_line()
        toks = hdr.split(TOK_SEP)
        while len(toks) != 7:
            line = f_head.consume_line()
            hdr += line
            toks = hdr.split(TOK_SEP)

        # Unpack header
        mode = toks[0].strip()
        tac = toks[1].strip()
        kind = toks[2].strip()
        ftac = toks[3].strip()
        gid = int(toks[4].strip())
        ngs = int(toks[5].strip())
        loc = toks[6].strip()
        tac_st_hdr = TacStHdr(mode, tac, kind, ftac, gid, ngs, loc)
        return tac_st_hdr

    def parse_local_decl(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_local_decl:before<{}>".format(f_head.peek_line()))

        # Parse local decl
        ldecl = f_head.consume_line()
        idx = ldecl.find(':')
        if idx < 0:
            raise NameError("Parsing local declaration but found {}".format(line))
        name = ldecl[:idx].strip()
        typ = ldecl[idx:].strip()

        # Parse rest of type it is on newline
        line = f_head.peek_line()
        while line != TOK_DIV and line.find(':') < 0:
            typ += " " + line.strip()
            line = f_head.advance_line()
        return (name, typ)

    def parse_local_ctx(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_local_ctx:before<{}>".format(f_head.peek_line()))

        # Parse local context
        local_decls = []
        line = f_head.peek_line()
        while line.find(':') >= 0:
            name, typ = self.parse_local_decl()
            local_decls += [(name, typ)]
            line = f_head.peek_line()
        return local_decls

    def parse_newline(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_newline:before<{}>".format(f_head.peek_line()))

        # Parse new line
        line = f_head.consume_line()
        return line

    def parse_pf_div(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_pf_div:before<{}>".format(f_head.peek_line()))

        # Parse proof divider
        line = f_head.consume_line()
        if line != TOK_DIV:
            raise NameError("Found {} instead of {}".format(line, TOK_DIV))
        return line

    def parse_goal(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_goal:before<{}>".format(f_head.peek_line()))

        # Parse goal
        goal = f_head.consume_line()
        line = f_head.peek_line()
        while not is_goal_end(line):
            goal += line
            line = f_head.advance_line()
        return goal

    def parse_decl(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_decl:before<{}>".format(f_head.peek_line()))

        # Parse declaration
        tac_st_hdr = self.parse_hdr()
        # self.parse_newline()
        ctx = self.parse_local_ctx()
        self.parse_pf_div()
        goal = self.parse_goal()
        return TacStDecl(tac_st_hdr, ctx, goal)

    def parse_begin_pf(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_begin_pf:before<{}>".format(f_head.peek_line()))
        
        # Parse
        line = f_head.consume_line()
        toks = line.split(TOK_SEP)
        lem_name = toks[2].strip()
        return lem_name

    def parse_begsubpf(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_begsubpf:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_endsubpf(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_endsubpf:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_qed(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_qed:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_begtacst(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_begtacst:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_endtacst(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_endtacst:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse(self):
        # Internal
        f_head = self.f_head
        self._mylog("parse<{}>".format(f_head.peek_line()))

        # Parse
        first_time = True
        cnt = 0
        line = f_head.raw_peek_line()
        while line != "":
            line = line.rstrip()
            if line.startswith("COQDEP"):
                f_head.consume_line()
            elif line.startswith("COQC"):
                print("Processing...", line)
                f_head.consume_line()
                
                lemmas = self.lems
                if not first_time:
                    print("HERE", first_time)
                    for lemma in lemmas:
                        lemma_p = cleanup_lemma(lemma)
                    print(basic_have_stats(lemmas))
                else:
                    first_time = True
                self.lems = []
                return lemmas
            elif line.startswith(TOK_BEG_PF):
                lem_name = self.parse_begin_pf()
                # TODO(deh): this does not handle opening a proof within a proof
                self.decls = []
            elif line.startswith(TOK_END_PF):
                self.parse_qed()
                # Accumulate lemma
                self.lems.append(LemTacSt(lem_name, self.decls))
            elif line.startswith(TOK_BEG_SUB_PF):
                self.parse_begsubpf()
                # TODO(deh): keep track of this?
            elif line.startswith(TOK_END_SUB_PF):
                self.parse_endsubpf()
                # TODO(deh): keep track of this?
            elif line.startswith(TOK_BEG_TAC_ST):
                self.parse_begtacst()
                decl = self.parse_decl()
                self.decls += [decl]
            elif line.startswith(TOK_END_TAC_ST):
                self.parse_endtacst()
            else:
                raise NameError("Parsing error at line {}: {}".format(f_head.line, f_head.peek_line()))
            line = f_head.raw_peek_line()
        return self.lems


class MyIter(object):
    def __init__(self, data):
        self.data = data
        self.idx = 0

    def __iter__(self):
        return self

    def __next__(self):
        if self.idx < len(self.data):
            elem = self.data[self.idx]
            self.idx += 1
            return elem
        else:
            raise StopIteration

    def has_next(self):
        return self.idx < len(self.data)

    def peek(self):
        return self.data[self.idx]

def cleanup_lemma(lemma):
    decls = []
    for decl in lemma.decls:
        if decl.hdr.mode == "after1":
            continue
        if decl.hdr.tac == "intro":
            # print("REMOVING", decl)
            continue
        if decl.hdr.tac == "have (ssrhavefwdwbinders)":
            # print("REMOVING", decl)
            continue
        decls += [decl]
    lemma.decls = decls
    return lemma

def recon_tac_tree(lemma, f_draw=False):
    decls = lemma.decls
    
    # 1) Connect before/after tactics
    bfaf = []
    stk = []
    it = iter(MyIter(decls))
    while it.has_next():
        decl = next(it)
        if decl.hdr.mode == TOK_BEFORE:
            stk.append(decl)
        else:
            bf_decl = stk.pop()
            if decl.hdr.tac != bf_decl.hdr.tac:
                # TODO(deh): kludge, need to signal terminal state
                bfaf += [(bf_decl, bf_decl)]
                bf_decl = stk.pop()

            bfaf += [(bf_decl, decl)]
            for _ in range(0, decl.hdr.ngs - bf_decl.hdr.ngs):
                decl_p = next(it)
                bfaf += [(bf_decl, decl_p)]

            # TODO(deh): old code
            """
            while it.has_next():
                decl_p = it.peek()
                if decl_p.hdr.tac == bf_decl.hdr.tac:
                    bfaf += [(bf_decl, decl_p)]
                    next(it)
                else:
                    break
            """

    """
    print("BEFORE/AFTER")
    for b, a in bfaf:
        print(b, a)
    """

    # 2) Build tree
    tree = nx.DiGraph()
    it = iter(MyIter(bfaf))
    root = it.peek()[1]
    tree.add_edge(mk_root_decl(), root)
    while it.has_next():
        curr_before, curr_after = next(it)
        it2 = iter(MyIter(bfaf))
        while it2.has_next():
            next_before, next_after = next(it2)
            if curr_after.hdr.gid == next_before.hdr.gid:
                tree.add_edge(curr_after, next_after)
                # print("ADDING", curr_after, next_after)

    # 3) Display tree
    #pos = nx.spring_layout(G)
    # nx.drawing.nx_pylab.draw_kamada_kawai(G, with_labels=True, font_weight='bold')
    # nx.draw(G, with_labels=True, font_weight='bold')
    if f_draw:
        nx.drawing.nx_pylab.draw_kamada_kawai(tree, with_labels=True)
        plt.show()

    return root, tree

class TacStStats(object):
    def __init__(self, root, tree):
        self.root = root
        self.tree = tree

    def cnt_tac_sts(self):
        return len(self.tree.nodes)

    def cnt_have(self):
        cnt = 0
        for decl in self.tree.nodes:
            if decl.hdr.tac == "<ssreflect_plugin::ssrhave@0> $fwd":
                cnt += 1
            else:
                print("Skipping", decl)
        return cnt

    def cnt_term_tac_sts(self):
        # TODO(deh): broken
        term = []
        for node in self.tree.nodes:
            if len(self.tree.adj[node]) == 0:
                term += [node]
        return term

    def foobar(self):
        return nx.algorithms.simple_paths.all_simple_paths(self.tree, root=self.root)

def test_foo():
    filename = "./foo.dump"
    with open(filename, 'r') as f:
        tsparser = TacStParser(f, True)
        lemmas = tsparser.parse()
        lemmas_clean = []
        for lemma in lemmas:
            print(lemma)
            lemma_p = cleanup_lemma(lemma)
            print(lemma_p)
            
            root, tree = recon_tac_tree(lemma_p, f_draw=True)
            ts_stats = TacStStats(root, tree)
            print("# tactic states: {}".format(ts_stats.cnt_tac_sts()))
            print("# have: {}".format(ts_stats.cnt_have()))
            print("chains: {}".format(ts_stats.cnt_term_tac_sts()))

def test_odd_order():
    filename = "/Users/dehuang/Documents/research/pnh/mathcomp-odd-order-1.6.1/mathcomp/odd_order/build.log"
    with open(filename, 'r') as f:
        tsparser = TacStParser(f, False)
        for i in range(0, 34):
            lemmas = tsparser.parse()
            lemmas_clean = []
            for lemma in lemmas:
                # print(lemma)
                lemma_p = cleanup_lemma(lemma)
                # print(lemma_p)
            print(basic_have_stats(lemmas))

if __name__=="__main__":
    test_foo()
    # test_odd_order()


"""
def count_pf_length(lemma):
    cnt = 0
    for decl in lemma.decls:
        if decl.hdr.mode == TOK_BEFORE:
            cnt += 1
    return cnt
"""