from collections import defaultdict
import random

prefix = """(*Set Printing All.*)
Require Import Omega.

Section Group.
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
        self.prod = defaultdict(list)


    def add_prod(self, lhs, rhs):
        """ Add production to the grammar. 'rhs' can
            be several productions separated by '|'.
            Each production is a sequence of symbols
            separated by whitespace.

            Usage:
                grammar.add_prod('NT', 'VP PP')
                grammar.add_prod('Digit', '1|2|3|4')
        """
        prods = rhs.split('|')
        for prod in prods:
            self.prod[lhs].append(tuple(prod.split()))

    def gen_random(self, symbol):
        """ Generate a random sentence from the
            grammar, starting with the given
            symbol.
        """
        sentence = ''

        # select one production of this symbol randomly
        rand_prod = random.choice(self.prod[symbol])

        for sym in rand_prod:
            # for non-terminals, recurse
            if sym in self.prod:
                sentence += self.gen_random(sym)
            else:
                sentence += sym + ' '

        return sentence

    def gen_random_convergent(self,
	  symbol,
	  cfactor=0.25,
	  pcount=defaultdict(int)
      ):
      """ Generate a random sentence from the
	  grammar, starting with the given symbol.

	  Uses a convergent algorithm - productions
	  that have already appeared in the
	  derivation on each branch have a smaller
	  chance to be selected.

	  cfactor - controls how tight the
	  convergence is. 0 < cfactor < 1.0

	  pcount is used internally by the
	  recursive calls to pass on the
	  productions that have been used in the
	  branch.
      """
      sentence = ''

      # The possible productions of this symbol are weighted
      # by their appearance in the branch that has led to this
      # symbol in the derivation
      #
      weights = []
      for prod in self.prod[symbol]:
	  if prod in pcount:
	      weights.append(cfactor ** (pcount[prod]))
	  else:
	      weights.append(1.0)

      rand_prod = self.prod[symbol][weighted_choice(weights)]

      # pcount is a single object (created in the first call to
      # this method) that's being passed around into recursive
      # calls to count how many times productions have been
      # used.
      # Before recursive calls the count is updated, and after
      # the sentence for this call is ready, it is rolled-back
      # to avoid modifying the parent's pcount.
      #
      pcount[rand_prod] += 1

      for sym in rand_prod:
	  # for non-terminals, recurse
	  if sym in self.prod:
	      sentence += self.gen_random_convergent(
				  sym,
				  cfactor=cfactor,
				  pcount=pcount)
	  else:
	      sentence += sym + ' '

      # backtracking: clear the modification to pcount
      pcount[rand_prod] -= 1
      return sentence

cfg = CFG()
cfg.add_prod('EXPR', 'e ADD ( EXPR )')
cfg.add_prod('EXPR', '( EXPR ) ADD m')
cfg.add_prod('EXPR', 'b')
cfg.add_prod('ADD', '<+>')

print(prefix)

counter = 0
numTheorems = 10

while(True):
    genStr = cfg.gen_random('EXPR')
    if (genStr == "b "): 
        continue
    print("Theorem rewrite_eq_" + str(counter) + ":")
    counter = counter + 1
    writeStr = "forall b, " + genStr + "= b."
    print(writeStr)
    print(proof)
    if(counter == numTheorems):
        break
