/- @@@
# CS2120 F25 Midterm Test

Instructions: Once you have downloaded and opened the exam,
and before you start on the exam, turn off your wifi. Turn
it back on again only when you are finished with the exam
and ready to upload the finished document to Canvas. Put all
devices other than your laptop in offline mode and put away
(watches, earbuds, or whatever). You may use your own notes.
You may *not* use any form of "AI" assistance to take this
exam. Be absolutely sure that you do not have any kind of
code completion, AI-generated suggestion generators, or any
other "helpers" running on or connected to your computer.
The penalty for cheating on this exam is a zero on this exam,
which will cascade to produce an F in the class, as one can't
pass with a zero on either exam. (Sorry but had to be clear
about that.)

This test has questions covering three main areas plus an
opportunity for some extra credit. For extra credit you do
have to correctly answer both parts of that question. The
point total for this test is 100, with an additiona 10 for
the extra credit. The first areas tests your understanding
of classical logical reasoning, including coming up with
counterexamples if there are any for a given proposition.
The second area tests your understanding of *constructive*
logic proof construction for propositions involving all of
the connectives we've covered to date: ∧, ∨, ¬, →, ∀, & ↔.
The third question again tests your understanding of proofs
in Lean, focusing on one that requires classical reasoning.


## 1. Truth Based Reasoning [4 points each = 20 pts]

This question lets you show your understanding of basic
truth-theoretic reasoning in propositional logic (which is
equivalent to Boolean algebra).

Question: Remember: a proposition is valid if and only if
it's true in all possible worlds: i.e., for all combinations
of truth values of the propositional variables (e.g., P and Q)
in a given proposition. To be NOT valid, there must be some
assignment of Boolean values to variables that makes the overall
proposition evaluate to false. We call such an assignment of
values to variables a *counterexample*. (As an aside, we call
an assignment of value to variables that makes a proposition
true a *model,* the opposite of a *counterexample*.)

To answer, first write VALID or NOT VALID after each proposition.
Then, for those you identify as NOT valid, give a counterexample.
Write counterexamples, if any, as so: ⟦P⟧ = true ∧ ⟦Q⟧ = true. To
get the ⟦⟧ brackets, use \[[ and \]]. If that doesn't work for you,
just write [[P]], [[Q]], etc. It's all plain text, not Lean, so
it's ok either way.

Hint: You can always determine the validity of a proposition in
propositional logic, by writing out a truth table. In most cases
here you can probably figure out the right answer without one, so
truth tables are NOT required here.

- A. (P → Q) → (Q → P) NOT VALID if P is false and Q is true

- B. (¬Q → ¬P) → (P → Q) VALID

- C. ¬(P ∧ Q) → ¬Q ∨ ¬P VALID

- D. (P ∧ Q) → (P ∨ Q) VALID

- E. (P ∨ Q) → (P ∧ Q) NOT VALID if P is true and Q is false


## 2. Proof-Based Reasoning [20 points each = 60 points]

Finish the following three formal proof constructions
in Lean. Replace *sorry* with the remainder of a proof
that Lean accepts.
@@@ -/

example (P Q : Prop) : (P ∨ Q) → (¬P → ¬Q) → False :=
(
  fun porq np2nq =>
  (
    match porq with
    | Or.inl p => _
    | Or.inr q => _
  )
)
/- @@@

We cannot prove the above proposition constructively. This is because
from a proof of P ∨ Q, we can't determine which of P ∨ Q is true.
If P is true, we can derive ¬Q from ¬P → ¬Q because from ¬P and P
we can derive False, and from False we can derive anything, including ¬Q,
however, we do not have a ¬P to use in this case. On the other hand,
if Q is true, we cannot derive ¬P from ¬P → ¬Q. Therefore, we cannot
constructively prove that False follows from the given premises.

@@@ -/

example (P Q : Prop) : P → ¬P → Q :=
(
  fun p =>
    fun np => nomatch np p
)


example (P Q R : Prop) : (P ∨ Q) ∧ (¬P → Q) :=
(
  And.intro
  (
    _
  )
  (
    _
  )
)

/- @@@

We can't prove the above proposition constructively. This is because
from a proof of P ∨ Q, again we can't determine which of P ∨ Q is true.
If P is true, we can't derive Q from ¬P → Q, and if Q is true,
we can't derive Q from ¬P → Q either. Therefore, we cannot constructively
prove that (P ∨ Q) ∧ (¬P → Q) holds.

@@@ -/


/- @@@
## 3. Something About Implication [20 points]

The standard reading of P → Q is "if P is true
then Q must be true."  A different view starts
with a case analysis of P. If it's false, then
P → Q is true (for either value of Q). If P is
true, on the other hand, then P → Q is true if
and only if Q is true. In other words, P → Q
seems to mean ¬P ∨ Q. Is that really true (in
classical logic)? Your job here is to prove
that it is *valid classically*. We give you
a good bit of the proof so that you can focus
on proofs of each *case*. Finish it off by
replacing all *sorry* placeholders with correct
proof terms.
@@@ -/

example (P Q : Prop) : (P → Q) ↔ (¬P ∨ Q) :=
let pornp := Classical.em P   -- from P derive proof of P ∨ ¬P
let qornq := Classical.em Q   -- from Q derive proof of Q ∨ ¬Q
Iff.intro

--  Forward: (P → Q) ↔ (¬P ∨ Q)   [10 points]
(
  fun h =>
    match pornp with
    | Or.inl p =>
      match qornq with
      | Or.inl _ => Or.inr (h p)
      | Or.inr nq =>
        let q : Q := h p
        False.elim (nq q)
    | Or.inr np =>
      match np with
      | np => Or.inl np
)

-- Backward: (¬P ∨ Q) → (P → Q)   [10 points]
(
  fun nporq =>
  (
    match nporq with
    | Or.inl np => fun p => nomatch np p
    | Or.inr q => fun _ => q
  )
)


/- @@@
## Extra Credit [10 points]

Formally state and prove the following proposition
in Lean. Let P and Q be any propositions. Prove by
*classical reasoning* that: if whenever P is true so
is Q,  and then if whenever P is true so is ¬Q, then
P must be false.
@@@ -/

-- Answer here:
example (P Q : Prop) :
  (P → Q) → (P → ¬Q) → ¬P :=
(
  fun p2q p2nq =>
    fun p =>
      let q : Q := p2q p
      let nq : ¬Q := p2nq p
      False.elim (nq q)
)

/- @@@
Now try a constructive proof of this proposition.
Take it as far as you can until you can make no
further progress. Study where you get stuck, and
then explain in precise natural language (English)
why this formula is not valid constructively even
though it is valid classically.

@@@ -/

-- Lean answer here:

example (P Q : Prop) :
  (P → Q) → (P → ¬Q) → ¬P :=
(
  fun p2q p2nq =>
    fun p =>
      _
)

/- @@@
Brief English explanation here:

Using classical logic, we can use the law of excluded middle or proof by contradiction
to show that P must be false if both implications hold. However, in constructive logic,
we can't derive ¬P directly from the implications without a direct proof or a counterexample.
Constructive logic needs explicit evidence for negation, but since we can't constructively
prove ¬P from the given premises, the proposition is not valid constructively.

@@@ -/
