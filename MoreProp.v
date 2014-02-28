(** * MoreProp: More about Propositions and Evidence *)

Require Export "Prop".


(* ####################################################### *)
(** * Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.


(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation) *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)
Inductive total_relation : nat -> nat -> Prop :=
  tot_rel : forall (n m:nat), total_relation n m.
(** [] *)

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)
Inductive empty_relation : nat -> nat -> Prop :=
  empt_rel : empty_relation 0 0.
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2. apply H1. apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [|n]. apply le_n. apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H. apply le_n. apply le_S in IHle. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m. generalize n. clear n. induction m as [|m].
  Case "m=0". intros n H. inversion H. apply le_n. inversion H1.
  Case "m=Sm". intros n H. inversion H. apply le_n. apply IHm in H1. apply le_S in H1. apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b as [|b].
  rewrite -> plus_comm. simpl. apply le_n.
  rewrite -> plus_comm. simpl. rewrite -> plus_comm. apply le_S. apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H. apply conj.
  Case "n1 <= m".
  induction H. apply n_le_m__Sn_le_Sm. apply le_plus_l. apply le_S. apply IHle.
  Case "n2 <= m".
  induction H. apply n_le_m__Sn_le_Sm. rewrite -> plus_comm. apply le_plus_l. apply le_S. apply IHle.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros n m H. apply le_S. apply H.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros n. induction n as [|n].
  intros m H. apply O_le_n.
  intros m H. destruct m. simpl in H. inversion H. apply n_le_m__Sn_le_Sm. apply IHn. simpl in H. apply H.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros n m. generalize n. clear n. induction m.
  intros n H. inversion H.  simpl. reflexivity.
  intros n H. destruct n. simpl. reflexivity. simpl. apply IHm.
  apply Sn_le_Sm__n_le_m.  apply H.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros n m o H1 H2. apply le_ble_nat. apply ble_nat_true in H1.
  apply ble_nat_true in H2. apply le_trans with (n:=m) (m:=n) (o:=o). apply H1. apply H2.
Qed.

(** **** Exercise: 3 stars (R_provability) *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function.
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)
Lemma succ_inj : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H. rewrite -> H. reflexivity.
Qed.

Lemma succ_inj2 : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Theorem R_implies_plus : forall n m o,
  R n m o -> n + m = o.
Proof.
  intros n m o HR. induction HR.
  simpl. reflexivity.
simpl. rewrite -> IHHR. reflexivity.
rewrite -> plus_comm. simpl. rewrite -> plus_comm.
rewrite -> IHHR. reflexivity. apply succ_inj2. apply succ_inj2. simpl in IHHR. rewrite -> plus_comm in IHHR.
simpl in IHHR. rewrite -> plus_comm in IHHR.
apply IHHR.
rewrite -> plus_comm. apply IHHR.
Qed.


Theorem plus_implies_R : forall n m o,
  n + m = o -> R n m o.
Proof.
  intros n m o. generalize n m. clear n m. induction o.
  intros n m H. destruct n. destruct m. apply c1.
  simpl in H. inversion H. destruct m. simpl in H. inversion H. simpl in H. inversion H.
  intros n m H. destruct n. simpl in H. rewrite -> H. apply c3. apply IHo. simpl. reflexivity.
  apply c2. apply IHo. simpl in H. apply succ_inj2 in H. apply H.
Qed.
(** [] *)

End R.


(* ##################################################### *)
(** * Programming with Propositions *)

(** A _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop].  Although we haven't discussed this
    explicitly, we have already seen numerous examples. *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** We've seen several ways of constructing propositions.

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)

(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even.
(* ===> even : nat -> Prop *)

(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** Here are two more examples of passing parameterized propositions
    as arguments to a function.

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P ->
    true_for_all_numbers P.



(** **** Exercise: 3 stars (combine_odd_even) *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) (n:nat) : Prop :=
  (evenb n = true /\ Peven n) \/ (oddb n = true /\ Podd n).


(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2. unfold combine_odd_even. remember (evenb n) as evenb. destruct evenb.
  Case "left". left. split. reflexivity. apply H2. unfold oddb. rewrite <- Heqevenb. simpl. reflexivity.
  Case "right". right. split. unfold oddb. rewrite <- Heqevenb. simpl. reflexivity. apply H1.
  unfold oddb. rewrite <- Heqevenb. simpl. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2. inversion H1. inversion H. unfold oddb in H2. rewrite -> H0 in H2. simpl in H2. inversion H2.
  inversion H. apply H3.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n H1 H2. inversion H1. inversion H. apply H3. inversion H. rewrite -> H2 in H0. inversion H0.
Qed.

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere) *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)


Fixpoint true_upto_n__true_everywhere (n:nat) (P : nat -> Prop) : Prop :=
  match n with
    | O => forall (m:nat), P m
    | S n' => P n -> true_upto_n__true_everywhere n' P
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. simpl. reflexivity.  Qed.
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)
