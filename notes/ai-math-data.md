# Dataset

Our modification to Coq produces a (Lemma, TacticTree) tuple, where
TacticTree = Tree<TacticState, Tactic>. (See Example.) We have data
for:
1. Coq Standard Library
2. Mathematical Componenents Library
3. Feit-Thompson Library 
It should also be possible to get this data for Compcert (and any
other Coq Library).

Here are some statistics we might want to compute about such datasets.
1. Dependency graph of lemmas (how many times each lemma is used)
2. Length of user tactic script by number of tactics. (how to deal with backtracking?)
3. Number of existentials in each lemma. 
   - Size of existential terms in each lemma. 
   - Complexity of existentials in each lemma---length of tactic script used to construct existential. 
4. Branching factor in each proof.
5. Proportion of computational to non-computational steps in each proof.
   - simple versus non-simple?
   - probably want number
6. Proportion of forward-chaining versus backward-chaining steps in each proof.
   - existentials are forward, apply is backward, rewrite is like analogous
7. Graph of depth in tactic tree versus size of local context during a proof
8. Size of goal in each tactic state as function of depth
   - other proxies for complexity?
9. Histogram of tactics used per lemma
10. Proportion of tactics that don't require arguments (per lemma?)
11. Histogram of length of tactic state from root to terminal states
12. Number of terminal tactic states in each proof
13. Number of actions in local context immediately applicable to goal
14. Taking a backward-chaing view, possibility of introducing existential
15. Portion of global context used in each tactic state
16. Is the structure of the proof independent of the order of the lemmas (w.r.t. dependency graph)
	- correlation?
17. Tactic used as a function of depth of tree
	- expect induction to be at top, reflexivity to be at bottom
18. Relationship between size of lemma term vs. each of its terminal states
	- other proxies for complexity?
19. Relationship between size of lemma and tactic script
20. How does inlining affect these statistics?
21. relationship between root states of tactic tree and lemma

## Example

Suppose we have a top-level Coq proof script as below.
```
Require Import mathcomp.ssreflect.ssreflect.

Lemma foo2 : forall n: nat, n + 0 = n.
Proof.
  intro.
  induction n. {
    simpl.
    reflexivity.
  } {
    simpl.
    have ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +  n + 0 = n by assumption.
    rewrite -> IHn.
    reflexivity.
  }
Qed.
```
Note that we only use simple tactics, i.e., there is no backtracking.

Our modification to Coq produces a (Lemma, TacticTree) tuple, where
TacticTree = Tree<TacticState, Tactic>. This is given as sequences of
text as below.
```
BEFORE | AFTER {!} <tactic> {!} <full tactic> {!} <goal id> {!} <number of goals>

Local Context
===========================
Goal
```
1. BEFORE | AFTER indicates whether it is before or after the
   execution of a tactic.
2. <tactic> is the name of the tactic to be run or executed
3. <full tactic> provides the full invocation of the tactic
4. <goal id> provides the current goal to be proven. You can connect
   the goal id's from AFTER to BEFORE states to determine the tree
   structure.
5. <number of goals> provides the current number of goals to be
   proven. For example, tactics such as induction can increase the
   number of goals for the inductive cases.

```
Pf(Classic, foo2)
BEFORE {!} intro {!} intro {!} 2 {!} 1

============================
forall n : nat, n + 0 = n
BEFORE {!} <coretactics::intro@0> {!} <coretactics::intro@0> {!} 2 {!} 1

============================
forall n : nat, n + 0 = n
AFTER {!} <coretactics::intro@0> {!}  {!} 3 {!} 1

n : nat
============================
n + 0 = n
AFTER {!} intro {!}  {!} 3 {!} 
n : nat
============================
n + 0 = n
BEFORE {!} induction n {!} induction n {!} 3 {!} 1

n : nat
============================
n + 0 = n
AFTER {!} induction n {!}  {!} 7 {!} 2

============================
0 + 0 = 0
AFTER {!} induction n {!}  {!} 10 {!} 2

n : nat
IHn : n + 0 = n
============================
S n + 0 = S n
BegSubPf
BEFORE {!} simpl {!} simpl {!} 7 {!} 1

============================
0 + 0 = 0
AFTER {!} simpl {!}  {!} 12 {!} 1

============================
0 = 0
BEFORE {!} reflexivity {!}  {!} 12 {!} 1

============================
0 = 0
AFTER {!} reflexivity {!}  {!} 12 {!} 1

============================
0 = 0
BEFORE {!} <coretactics::reflexivity@0> {!} <coretactics::reflexivity@0> {!} 12 {!} 1

============================
0 = 0
EndSubPf
BegSubPf
BEFORE {!} simpl {!} simpl {!} 10 {!} 1

n : nat
IHn : n + 0 = n
============================
S n + 0 = S n
AFTER {!} simpl {!}  {!} 15 {!} 1

n : nat
IHn : n + 0 = n
============================
S (n + 0) = S n
BEFORE {!} have (ssrhavefwdwbinders) {!} have ihn:
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + n + 0 = n by assumption {!} 15 {!} 1

n : nat
IHn : n + 0 = n
============================
S (n + 0) = S n
BEFORE {!} <ssreflect_plugin::ssrhave@0> $fwd {!} <ssreflect_plugin::ssrhave@0> $fwd {!} 15 {!} 1

n : nat
IHn : n + 0 = n
============================
S (n + 0) = S n
BEFORE {!} assumption {!}  {!} 17 {!} 1

n : nat
IHn : n + 0 = n
============================
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + n + 0 = n
AFTER {!} assumption {!}  {!} 17 {!} 1

n : nat
IHn : n + 0 = n
============================
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + n + 0 = n
BEFORE {!} <coretactics::assumption@0> {!} <coretactics::assumption@0> {!} 17 {!} 1

n : nat
IHn : n + 0 = n
============================
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + n + 0 = n
AFTER {!} <ssreflect_plugin::ssrhave@0> $fwd {!}  {!} 19 {!} 1

n : nat
IHn : n + 0 = n
ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      n + 0 = n
============================
S (n + 0) = S n
AFTER {!} have (ssrhavefwdwbinders) {!}  {!} 19 {!} 1

n : nat
IHn : n + 0 = n
ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      n + 0 = n
============================
S (n + 0) = S n
BEFORE {!} rewrite IHn {!} rewrite IHn {!} 19 {!} 1

n : nat
IHn : n + 0 = n
ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      n + 0 = n
============================
S (n + 0) = S n
AFTER {!} rewrite IHn {!}  {!} 20 {!} 1

n : nat
IHn : n + 0 = n
ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      n + 0 = n
============================
S n = S n
BEFORE {!} reflexivity {!}  {!} 20 {!} 1

n : nat
IHn : n + 0 = n
ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      n + 0 = n
============================
S n = S n
AFTER {!} reflexivity {!}  {!} 20 {!} 1

n : nat
IHn : n + 0 = n
ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      n + 0 = n
============================
S n = S n
BEFORE {!} <coretactics::reflexivity@0> {!} <coretactics::reflexivity@0> {!} 20 {!} 1

n : nat
IHn : n + 0 = n
ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +
      n + 0 = n
============================
S n = S n
EndSubPf
Qed
```

Properties/Issues:
1. Lemma \iff Tactic Tree
2. Have dependency graph of definition/lemma
3. How do we take care of global context?
   * It is dynamic across lemmas, but constant within the proof of a lemma.
   * It is sensitive to the order in which lemmas are proven.
4. How do we handle existentials in proofs?
   * It can read from global context and read/write to local context.
   * It is sensitive to the order in which other existentials are introduced.
5. How do we handle generalization to unseen symbols?
   - the embedding of a symbol and the embedding of its properties are close
6. How should we just interact with Coq? This is not needed for an initial analysis.


# Possible Tasks

## Premise selection
- data: (initial tactic state, lemmas mentioned in tactic tree)
- condition: each data point comes from a lemma, also need negative examples
- unknown: given unseen initial tactic state, predict lemmas that will be mentioned in its proof
  * globals? use entire repo
  * existentials? don't care
  * generalization?

This is just a baseline that others have done.

## Tactic prediction
- data: (tactic state, tactic) tuples
- condition: each data point comes from a well-formed tactic tree, do we need negative examples?
- unknown: given unseen tactic state, produce distribution on next tactic to take
  * global? use entire repo
  * existentials? treat them abstractly
  * generalization?

This produces a function that can be used to predict the next tactic to use.
What about with sequences of [(tactic state, tactic)]?

## Tactic tree reconstruction
- data: tactic tree
- condition: each tactic tree is well-formed
- unknown: learn parameterized function that can reconstruct the input tactic tree
  * globals? use entire repo
  * existentials? treat them abstractly
  * generalization?

This produces a tactic tree embedding.
Reconstruct in abstract feature space?
This could be used for tactic prediction?
What else can this be used for?

## Existential reconstruction
- data: (tactic state, existential tactic)
- condition: each data point comes from a well-formed tactic tree
- unknown: learn parameterized function that can reconstruct the existential
  * globals?
  * existentials?
  * generalization?
  
Reconstruct in abstract feature space?
In theory, the purpose of an existential is to say that some object exists with the desired properties. Perhaps we can treat these synthetically, i.e., abstract the proof from the details of the actual proof objects
  
## Lemma prediction
- data: (terminal tactic states, lemma)
- condition: each data point comes from a proven lemma
- unknown: construct a predictor that selects which lemma from the entire repo has the same terminal states from the lemma
  * globals? use entire repo
  * existentials? don't care
  * generalization?
  
## Reconstructing lemmas
- data: (terminal tactic states, lemma)
- condition: each data point comes from a proven lemma
- unknown: reconstruct the original lemma (what you could prove given those facts)
  * globals? use entire repo
  * existentials? don't care
  * generalization?
  
This could be used to find analogous lemmas because the terminal states look the same.
What other ways can we divide this up?
  
## Tactic state similarity:
- data: tactic trees
- condition: each tactic tree is well-formed
- unknown: two tactic states are similar if they use similar proof techniques

## Tactic state evaluation:
- data: tactic state
- condition: each data point comes from a well-formed tactic tree, also need negative examples
- unknown: given a tactic state, produce a number indicating how promising the tactic state is
  * globals?
  * existentials?
  * generalization?

This requires us to be able to use Coq.
Train via reinforcement learning with inner-loop MCTS?
How do we represent the action space?
Can we do the inner-loop tree search with plausible inference?


## Reconstruct Tactics from Proof Terms

This is like explaining / decompiling?
