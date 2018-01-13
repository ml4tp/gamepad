from collections import defaultdict
import random
import numpy as np

"""
Generate lemma statements, parameterized by length.
"""

prefix = """(*Set Printing All.*)
Require Import Omega.

(* The set of the group. *)
Axiom G : Set.

(* The left identity for +. *)
Axiom e : G.

(* The right identity for +. *)
Axiom m : G.

(* + binary operator. *)
Axiom f : G -> G -> G.

(* For readability, we use infix <+> to stand for the binary operator. *)
Infix "<+>" := f (at level 50).

(* [m] is the right-identity for all elements [a] *)
Axiom id_r : forall a, a <+> m = a.

(* [e] is the left-identity for all elements [a] *)
Axiom id_l : forall a, e <+> a = a.

Hint Rewrite id_r id_l : ids.

Ltac my_rewrite :=
  match goal with
  | [ |- ?X <+> m = ?Y ] => rewrite id_r
  | [ |- e <+> ?X = ?Y ] => rewrite id_l
  end.
"""

proof = """intros.
repeat my_rewrite.
reflexivity.
Qed.
"""

def weighted_choice(weights):
    rnd = random.random() * sum(weights)
    for i, w in enumerate(weights):
	rnd -= w
	if rnd < 0:
	    return i

class CFG(object):
    def __init__(self):
        self.prod_rec = defaultdict(list)
        self.prod_term = defaultdict(list)
        self.counter = 1

    def add_prod_rec(self, lhs, rhs):
        """ Add production rule (recursive) to the grammar. """
        prods = rhs.split('|')
        for prod in prods:
            self.prod_rec[lhs].append(tuple(prod.split()))

    def add_prod_term(self, lhs, rhs):
        """ Add production rule (terminal) to the grammar. """
        prods = rhs.split('|')
        for prod in prods:
            self.prod_term[lhs].append(tuple(prod.split()))

    def gen_random(self, symbol, lengthSentence, isRec):
        """ Generate a random theorem statement with length of lengthSentence. """
        sentence = ''

        # select production rule (according to isRec) randomly
        if isRec:
            rand_prod = random.choice(self.prod_rec[symbol])
        else:
            rand_prod = random.choice(self.prod_term[symbol])

        # store a boolean array indicating if production rule element is recursive or terminal
        recArray = np.ones(len(rand_prod), )

        internalCounter = 0
        for sym in rand_prod:
            # record if recursive or terminal 
            if sym in self.prod_rec:
                recArray[internalCounter] = 1
            else:
                recArray[internalCounter] = 0
            internalCounter += 1

        for index, elem in enumerate(recArray):
             if (elem == 1):
                if(self.counter >= lengthSentence):
                    sentence += self.gen_random(rand_prod[index], lengthSentence, 0)
                else:
                    self.counter += 1
                    sentence += self.gen_random(rand_prod[index], lengthSentence, 1)
             else: 
                sentence += rand_prod[index] + ' '

        return sentence

    def gen_random_wrapper(self, symbol, lengthSentence):
        retStr = self.gen_random(symbol, lengthSentence, 1)
        self.counter = 1
        return retStr 

cfg = CFG()
cfg.add_prod_rec('EXPR', 'e <+> ( EXPR )')
cfg.add_prod_rec('EXPR', '( EXPR ) <+> m')
cfg.add_prod_term('EXPR', 'b')

# print(prefix)

counter = 0
numTheorems = 10
lengthSentence = 5 

while(True):
    genStr = cfg.gen_random_wrapper('EXPR', lengthSentence)
    if (genStr == "b "): 
        continue
    print("Theorem rewrite_eq_" + str(counter) + ":")
    counter = counter + 1
    writeStr = "forall b, " + genStr + "= b."
    print(writeStr)
#    print(proof)
    if(counter == numTheorems):
        break
