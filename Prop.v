(** * Prop: Propositions and Evidence *)

Require Export MoreCoq.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions
    ([forall x, P]).

    This chapter will take us on a first tour of the
    propositional (logical) side of Coq.
    In particular, we will expand our repertoire of primitive
    propositions to include _user-defined_ propositions, not just
    equality propositions (which are more-or-less "built in" to Coq).
*)


(* ##################################################### *)
(** * Inductively Defined Propositions *)

(**  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful].
       - Rule [b_5]: The number [5] is [beautiful].
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0

                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion hold unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8
*)

(** **** Exercise: 1 star (varieties_of_beauty) *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(* FILL IN HERE *)
(** [] *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.

    The rules introduced this way have the same status as proven
    theorems; that is, they are true axiomatically.
    So we can use Coq's [apply] tactic with the rule names to prove
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.


(** **** Exercise: 2 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m. induction m as [|m'].
  Case "m=0". simpl. intro H. apply b_0.
  Case "m=S m'". intro H. simpl. apply b_sum. apply H. apply IHm'. apply H. Qed.
(** [] *)


(* ####################################################### *)
(** ** Induction Over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    two constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]),
      - [E] is [b_5] (and [n] is [5]), or
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)

(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree) *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.

(* FILL IN HERE *)
[]
*)


(** **** Exercise: 1 star (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n H. apply g_plus5. apply g_plus5. apply g_plus3. apply H.
Qed.
(** [] *)

(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)

Theorem gorgeous__beautiful : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3".
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous.
Qed.

(** Notice that the argument proceeds by induction on the _evidence_ [H]! *)

(** Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)

Theorem gorgeous__beautiful_FAILED : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)




(** **** Exercise: 2 stars (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m H1 H2. induction H1 as [|n'|n'].
  Case "n=0". simpl. apply H2.
  Case "n=n'+3". rewrite <- plus_assoc. apply g_plus3. apply IHgorgeous.
  Case "n=n'+5". rewrite <- plus_assoc. apply g_plus5. apply IHgorgeous.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous) *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H. induction H as [ | | | k l]. apply g_0. apply g_plus3. apply g_0. apply g_plus5. apply g_0.
  apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (g_times2) *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
  intros x y z. rewrite -> plus_comm. rewrite <- plus_assoc. replace (y+x) with (x+y). rewrite -> plus_assoc.
  reflexivity. apply plus_comm.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl.
   induction H.
   simpl. apply g_0. simpl. apply g_plus3. replace (n + S (S (S (n+0)))) with (n + (3 + n)). rewrite -> helper_g_times2.
   simpl. apply g_plus3. replace (n + n) with (n + (n + 0)). apply IHgorgeous. rewrite <- plus_n_O. reflexivity.
   rewrite <- plus_n_O. reflexivity.
   simpl. apply g_plus5. rewrite <- plus_n_O. replace (n + (S (S (S (S (S n)))))) with (n + (5 + n)). rewrite -> helper_g_times2.
   simpl. apply g_plus5. replace (n + n) with (n + (n + 0)). apply IHgorgeous. rewrite <- plus_n_O. reflexivity.
   simpl. reflexivity.
Qed.
(** [] *)


(* ####################################################### *)
(** ** From Boolean Functions to Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop :=
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."

    Note that here we have given a name
    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)


(** **** Exercise: 1 star (double_even) *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  intro n. induction n as [|n].
  simpl. apply ev_0.
  simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)


(** *** Discussion: Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(** **** Exercise: 1 star (ev__even) *)
(** Here is a proof that the inductive definition of evenness implies
    the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'.
Qed.

(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* No, because induction over n would require that we show the property
   holds for (S n) given that it holds for n, but this is not the case.
   It might be possible to do for equivalence.*)
(** [] *)

(** The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)

(** **** Exercise: 1 star (l_fails) *)
(** The following proof attempt will not succeed. **)
Theorem l : forall n,
  ev n.
Proof.
  intros n. induction n.
    Case "O". simpl. apply ev_0.
    Case "S".
Abort.

(*           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

   It fails because we would neet to show ev (S n) given that ev n.
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars (ev_sum) *)
(** Here's another exercise requiring induction. *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m H1 H2. induction H2 as [ | m'].
  Case "m=0". simpl. rewrite <- plus_n_O. apply H1.
  Case "m=S (S m')". rewrite -> plus_comm. simpl. apply ev_SS. rewrite -> plus_comm. apply IHev.
Qed.
(** [] *)


(* ####################################################### *)
(** ** [Inversion] on Evidence *)

(** Another situation where we want to analyze evidence for evenness
    is when proving that, if [n] is even, then [pred (pred n))] is
    too.  In this case, we don't need to do an inductive proof.  The
    right tactic turns out to be [inversion].  *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'.
Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n) *)
(** What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

(* FILL IN HERE *)
(** [] *)


(** Another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'. Qed.

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [|n' E']. apply SSev__even in E'. apply E'.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intro E. inversion E as [|n' E']. inversion E' as [|n'' E'']. inversion E'' as [|n''' E'''].
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H1 H2. induction H2. simpl in H1. apply H1.
  simpl in H1. apply SSev__even in H1. apply IHev. apply H1.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Lemma double_n : forall n:nat,
  double n = n + n.
Proof.
  induction n as [|n']. simpl. reflexivity.
  simpl. rewrite <- plus_comm. simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H1 H2. assert (ev ((n + m) + (n + p))). apply ev_sum with (n:=n+m) (m:=n+p). apply H1. apply H2.
  assert (ev (double n)). apply double_even. replace (n + m + (n + p)) with ((double n) + (m + p)) in H.
  apply ev_ev__ev with (n:=double n) (m:=(m+p)). apply H. apply H0.
  replace (n + m + (n + p)) with ((n + n) + m + p). assert (double n = n + n). apply double_n. rewrite <- H3. rewrite -> plus_assoc. reflexivity.
  replace (n+n+m) with (n + m + n). replace (n + m + n + p) with (n + m + (n + p)). reflexivity. rewrite -> plus_assoc. reflexivity. rewrite -> plus_comm. apply plus_assoc.
Qed.
(** [] *)


(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)

    - Prove that
       forall l, pal (l ++ rev l).
    - Prove that
       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_single : forall x:X, pal [x]
  | pal_cons : forall (x:X) (l:list X) , pal l -> pal (x :: snoc l x).

Theorem pal_mirror : forall (X:Type) (l:list X),
  pal (l ++ rev l).
Proof.
  intros X l. induction l as [|h t]. simpl. apply pal_nil.
  simpl. rewrite <- snoc_with_append. apply pal_cons. apply IHt.
Qed.

Theorem pal_rev : forall (X:Type) (l:list X),
  pal l -> l = rev l.
Proof.
  intros X l H. induction H. simpl. reflexivity. simpl. reflexivity.
  simpl. rewrite -> rev_snoc. simpl. rewrite <- IHpal. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)
Theorem rev_eq_head_last : forall (X:Type) (x y:X) (l:list X),
  (x :: snoc l y) = rev (x :: snoc l y) -> x = y.
Proof.
  intros X x y l H. simpl in H. rewrite -> rev_snoc in H. simpl in H. inversion H. reflexivity.
Qed.

Theorem rev_injective : forall (X:Type) (l1 l2:list X),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H. rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive. reflexivity.
Qed.

Theorem snoc_injective : forall (X:Type) (x y:X) (l1 l2:list X),
  snoc l1 x = snoc l2 y -> l1 = l2.
Proof.
  intros X x y l1. induction l1 as [|h t].
  Case "l1 = []". intros l2 H. destruct l2. reflexivity. simpl in H.
  inversion H. destruct l2. simpl in H2. inversion H2. simpl in H2. inversion H2.
  Case "l1 = h::t". intros l2 H. destruct l2. simpl in H. destruct t. simpl in H. inversion H. simpl in H. inversion H.
  simpl in H. inversion H. apply IHt in H2. rewrite -> H2. reflexivity.
Qed.

Theorem rev_subl : forall (X:Type) (x y:X) (l:list X),
  (x :: snoc l y) = rev (x :: snoc l y) -> l = rev l.
Proof.
  intros X x y l H. simpl in H. rewrite -> rev_snoc in H. simpl in H. inversion H.
  apply snoc_injective in H2. apply H2.
Qed.

Theorem pal_subl : forall (X:Type) (x y:X) (l:list X),
  pal (x :: snoc l y) -> pal l.
Proof.
  intros X x y l H. inversion H. destruct l. simpl in H2. inversion H2. simpl in H2. inversion H2.
  apply snoc_injective in H2. rewrite <- H2. apply H1.
Qed.

Fixpoint halve (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S m) => S (halve m)
  end.

Fixpoint take {X:Type} (n:nat) (l:list X) : list X :=
  match n with
    | O => []
    | S n => match l with
               | [] => []
               | h::t => h :: take n t
             end
    end.

Theorem list_inj : forall (X:Type) (x:X) (l1 l2:list X),
  x::l1 = x::l2 -> l1 = l2.
Proof.
  intros X x l1.
  induction l1 as [|h t].
  Case "l1=[]". intros l2 H. inversion H. reflexivity.
  Case "l1=h::t". intros l2 H. inversion H. reflexivity.
Qed.

Theorem snoc_length : forall (X:Type) (v:X) (n:nat) (l:list X),
  length (snoc l v) = S n -> length l = n.
Proof.
  intros X v n.
  induction n as [|n].
  Case "n=O". intros l H. destruct l as [|h t]. simpl. reflexivity. simpl in H. inversion H.
    SCase "l=h::t". destruct t. simpl in H1. inversion H1. simpl in H1. inversion H1.
  Case "n=Sn". intros l H. destruct l as [|h t]. simpl in H. inversion H.
    SCase "l=h::t". simpl. simpl in H. inversion H. rewrite -> H1. apply IHn in H1. rewrite -> H1. reflexivity.
Qed.


Theorem take_snoc : forall (X:Type) (x:X) (n m:nat) (l:list X),
   n = length l -> ble_nat m n = true -> take m (snoc l x) = take m l.
Proof.
  intros X x n.
  induction n as [|n].
  Case "n=0".
    intros m l Hlen Hleq. destruct m as [|m]. simpl. reflexivity.
    simpl in Hleq. inversion Hleq.
  Case "n=Sn".
    intros m l Hlen Hleq. destruct l as [|h t]. simpl in Hlen. inversion Hlen.
    simpl in Hlen. inversion Hlen. destruct m as [|m]. simpl. reflexivity.
    simpl. assert (take m (snoc t x) = take m t).
    apply IHn. apply H0. simpl in Hleq. apply Hleq. rewrite -> H. reflexivity.
Qed.

Theorem ble_succ : forall (m n:nat),
  ble_nat n m = true -> ble_nat n (S m) = true.
Proof.
  intro m.
  induction m as [|m].
  intros n Hleq. destruct n as [|n]. simpl. reflexivity. simpl in Hleq. inversion Hleq.
  intros n Hleq. destruct n as [|n]. simpl. reflexivity.
  simpl. apply IHm. simpl in Hleq. apply Hleq.
Qed.

Theorem ble_double : forall (n:nat),
  ble_nat n (double n) = true.
Proof.
  intro n.
  induction n as [|n].
  simpl. reflexivity.
  simpl. apply ble_succ. apply IHn.
Qed.

Theorem rev_split_ev : forall (X:Type) (l hl:list X) (n:nat),
  double n = length l -> l = rev l -> hl = take n l -> l = hl ++ rev hl.
Proof.
  intros X l hl n.
  generalize l hl.
  induction n as [|n].
  (*induction Hev as [|E].*)
  Case "n=0".
   intros l0 hl0 Hlen Hrev Hhl. destruct l0.
   SCase "l0=[]". simpl in Hhl. rewrite -> Hhl. simpl. reflexivity.
   SCase "l0=h::t". simpl in Hlen. inversion Hlen.
  Case "n=Sn".
    (* Need to prove that l0 = h :: snoc t h, then I can apply the IH to t. *)
   intros l0 hl0 Hlen_l0 Hrev_l0 Hhl0. remember l0 as l0'. destruct l0' as [|h t].
   SCase "l0=[]". simpl in Hlen_l0. inversion Hlen_l0.
   SCase "l0=h::t". rewrite -> Heql0' in Hrev_l0. remember (rev l0) as rev_l0. destruct rev_l0 as [|rh rt].
    SSCase "rev l0=[]". rewrite -> Heql0' in Hlen_l0. rewrite -> Hrev_l0 in Hlen_l0. simpl in Hlen_l0. inversion Hlen_l0.
    SSCase "rev l0=rh::rt". rewrite <- Heql0' in Heqrev_l0. simpl in Heqrev_l0. rewrite <- Hrev_l0 in Heqrev_l0.
      remember (rev t) as rev_t. destruct (rev_t) as [|rth rtt].
      SSSCase "rev t=[]". simpl in Heqrev_l0. rewrite -> Heqrev_l0 in Heql0'.
        inversion Heql0'. rewrite -> H0 in Hlen_l0. simpl in Hlen_l0. inversion Hlen_l0.
      SSSCase "rev t=rth::rtt". simpl in Heqrev_l0.
        (* Now still need to show that rth = h *)
        rewrite <- Heql0' in Heqrev_l0. inversion Heqrev_l0. rewrite <- H0 in Heqrev_l0.
        (* Now we have l0 = h :: snoc rtt h, we need to prepare the goal for the IH *)
        rewrite <- H0. simpl in Hhl0. rewrite -> Hhl0. simpl. rewrite <- snoc_with_append.
        assert (rtt = (take n t ++ rev (take n t))).
        apply IHn.
        (* Show: double n = length rtt *)
        simpl in Hlen_l0. inversion Hlen_l0. rewrite -> H1 in H2.
        symmetry in H2. apply snoc_length in H2. symmetry. apply H2.
        (* Show: rtt = rev rtt *)
        rewrite -> H1 in Heqrev_t. rewrite -> rev_snoc in Heqrev_t. inversion Heqrev_t. rewrite -> rev_involutive. symmetry. apply H2.
        (* Show: take (halve E) t = take (halve E) rtt *)
        rewrite -> H1. apply take_snoc with (n:=length rtt). reflexivity.
        (* Show: ble_nat (havle E) (length rtt) = true *)
        simpl in Hlen_l0. inversion Hlen_l0. rewrite -> H1 in H2. symmetry in H2. apply snoc_length in H2.
        rewrite -> H2. apply ble_double.
        (* Show: h :: snoc rtt h = h :: snoc (take (halve E) t ++ rev (take (halve E) t)) h *)
        rewrite <- H. reflexivity.
Qed.


Theorem rev_split_ev_pal : forall (X:Type) (l:list X) (n:nat),
  double n = length l -> l = rev l -> pal l.
Proof.
  intros X l n Hlen Hrev.
  remember (take n l) as hl.
  assert (l = hl ++ rev hl).
  apply rev_split_ev with (n:=n). apply Hlen. apply Hrev. apply Heqhl.
  assert (pal (hl ++ rev hl)). apply pal_mirror.  rewrite <- H in H0. apply H0.
Qed.

Fixpoint drop {X:Type} (n:nat) (l:list X) : list X :=
  match n with
    | O => l
    | S n' => match l with
                | [] => []
                | h::t => drop n' t
              end
  end.

Theorem take_drop : forall (X:Type) (n m:nat) (h:X) (t:list X),
  drop (S n) (take (S m) (h::t)) = drop n (take m t).
Proof.
  intros X n m h t.
  replace (take (S m) (h::t)) with (h :: take m t).
  replace (drop (S (S n)) (h :: take m t)) with (drop (S n) (take m t)). reflexivity.
  remember (take m t) as tt. remember (S n) as sn. simpl. reflexivity. simpl. reflexivity.
Qed.

Theorem rev_split_odd : forall (X:Type) (l hl ctr:list X) (n:nat),
  S (double n) = length l -> l = rev l -> hl = take n l -> ctr = drop n (take (S n) l) -> l = hl ++ ctr ++ rev hl.
Proof.
  intros X l hl ctr n.
  generalize l hl ctr. clear l hl ctr.
  induction n as [|n].
  Case "n=0". intros l hl ctr Hlen Hrev Hhl Hctr. simpl in Hlen. simpl in Hhl. simpl in Hctr.
    destruct l as [|h t].
    SCase "l=[]". simpl in Hlen. inversion Hlen.
    SCase "l=h::t".  rewrite -> Hhl. rewrite -> Hctr. simpl. simpl in Hlen.
      destruct t as [|ht tt]. reflexivity. simpl in Hlen. inversion Hlen.
  Case "n=Sn".
    (* Need to prove that l = h :: snoc t h, then I can apply the IH to t. *)
   intros l hl ctr Hlen Hrev Hhl Hctr. remember l as l'. destruct l' as [|h t].
   SCase "l=[]". simpl in Hlen. inversion Hlen.
   SCase "l=h::t". rewrite -> Heql' in Hrev. remember (rev l) as rev_l. destruct rev_l as [|rh rt].
    SSCase "rev l=[]". rewrite -> Heql' in Hlen. rewrite -> Hrev in Hlen. simpl in Hlen. inversion Hlen.
    SSCase "rev l0=rh::rt". rewrite <- Heql' in Heqrev_l. simpl in Heqrev_l. rewrite <- Hrev in Heqrev_l.
      remember (rev t) as rev_t. destruct (rev_t) as [|rth rtt].
      SSSCase "rev t=[]". simpl in Heqrev_l. rewrite -> Heqrev_l in Heql'.
        inversion Heql'. rewrite -> H0 in Hlen. simpl in Hlen. inversion Hlen.
      SSSCase "rev t=rth::rtt". simpl in Heqrev_l.
        (* Now still need to show that rth = h *)
        rewrite <- Heql' in Heqrev_l. inversion Heqrev_l. rewrite <- H0 in Heqrev_l.
        (* Now we have l0 = h :: snoc rtt h, we need to prepare the goal for the IH *)
        rewrite <- H0. simpl in Hhl. rewrite -> Hhl. simpl. rewrite <- snoc_with_append. rewrite <- snoc_with_append.
        assert (rtt = (take n t ++ ctr ++ rev (take n t))).
        apply IHn.
        (* Show: double n = length rtt *)
        simpl in Hlen. inversion Hlen. rewrite -> H1 in H2.
        symmetry in H2. apply snoc_length in H2. symmetry. apply H2.
        (* Show: rtt = rev rtt *)
        rewrite -> H1 in Heqrev_t. rewrite -> rev_snoc in Heqrev_t. inversion Heqrev_t. rewrite -> rev_involutive. symmetry. apply H2.
        (* Show: take n t = take n rtt *)
        rewrite -> H1. apply take_snoc with (n:=length rtt). reflexivity.
        (* Show: ble_nat n (length rtt) = true *)
        simpl in Hlen. inversion Hlen. rewrite -> H1 in H2. symmetry in H2. apply snoc_length in H2.
        rewrite -> H2. apply ble_succ. apply ble_double.
        (* Show: ctr = drop n (take (S n) rtt) *)
        rewrite -> H1 in Hctr.
        assert (drop (S n) (take (S (S n)) (h :: snoc rtt rth)) = drop n (take (S n) (snoc rtt rth))). apply take_drop.
        rewrite -> H in Hctr. assert (take (S n) (snoc rtt rth) = take (S n) rtt).
        simpl in Hlen. assert (length rtt = S (double n)). rewrite -> H1 in Hlen. inversion Hlen. symmetry in H3. apply snoc_length in H3. apply H3.
        apply take_snoc with (n:=S (double n)). symmetry. apply H2. simpl. apply ble_double.  rewrite -> H2 in Hctr. apply Hctr.
         (* Show: h :: snoc rtt h = h :: snoc (take (halve E) t ++ rev (take (halve E) t)) h *)
        rewrite <- H. reflexivity.
Qed.

Theorem pal_mirror_single : forall (X:Type) (l ctr:list X),
  length ctr = 1 -> pal (l ++ ctr ++ rev l).
Proof.
  intros X l.
  induction l as [|h t].
  Case "l=[]". intros ctr Hlen. simpl. destruct ctr as [|hc tc]. simpl. apply pal_nil. destruct tc as [|htc ttc].
    simpl. apply pal_single. simpl in Hlen. inversion Hlen.
  Case "l=h::t". intros ctr Hlen. simpl. rewrite <- snoc_with_append. rewrite <- snoc_with_append. apply pal_cons.
  apply IHt. apply Hlen.
Qed.

Fixpoint min_nat (n m:nat) : nat :=
  match n with
    | O => O
    | S n' => match m with
                | O => O
                | S m' => S (min_nat n' m')
              end
  end.

Theorem ble_nat_min : forall (n m:nat),
  ble_nat n m = true -> min n m = n.
Proof.
  intros n. induction n as [|n].
  Case "n=0". intros m H. simpl. reflexivity.
  Case "n=Sn". intros m H. destruct m as [|m]. simpl in H. inversion H.
  simpl. assert (min n m = n). apply IHn. simpl in H. apply H. rewrite -> H0. reflexivity.
Qed.

Theorem length_take : forall (X:Type) (n:nat) (l:list X),
  length (take n l) = min_nat n (length l).
Proof.
  intros X n.
  induction n as [|n].
  Case "n=0". intros l. simpl. reflexivity.
  Case "n=Sn". intros l. destruct l as [|h t]. simpl. reflexivity.
    simpl. assert (length (take n t) = min_nat n (length t)). apply IHn. rewrite -> H. reflexivity.
Qed.

Theorem length_drop_take : forall (X:Type) (n m:nat) (l:list X),
  ble_nat n (length l) = true -> ble_nat m n = true -> length (drop m (take n l)) = n - m.
Proof.
  intros X n.
  induction n as [|n].
  Case "n=0". intros m l Hlen Hleq.
    simpl. destruct m as [|m]. simpl. reflexivity. simpl. reflexivity.
  Case "n=Sn". intros m l Hlen Hleq.
    destruct l as [|h t].
      SCase "l=[]". simpl in Hlen. inversion Hlen.
      SCase "l=h::t". simpl. destruct m as [|m].
        SSCase "m=0". simpl. simpl in Hlen. assert (length (take n t) = n).
        rewrite -> length_take. apply ble_nat_min with (m:=length t). apply Hlen.
        rewrite -> H. reflexivity. simpl. apply IHn. simpl in Hlen. apply Hlen. simpl in Hleq. apply Hleq.
Qed.

Theorem minus_redux : forall (n m:nat),
  (S n) - (S m) = n - m.
Proof.
  intros n m. simpl. reflexivity.
Qed.

Theorem minus_Sn_n_eq_1 : forall (n:nat),
  (S n) - n = 1.
Proof.
  intro n. induction n as [|n'].
  simpl. reflexivity.
  rewrite <- IHn'. apply minus_redux with (n:=S n') (m:= n').
Qed.

Theorem rev_split_odd_pal : forall (X:Type) (l:list X) (n:nat),
  S (double n) = length l -> l = rev l -> pal l.
Proof.
  intros X l n Hlen Hrev.
  remember (take n l) as hl. remember (drop n (take (S n) l)) as ctr.
  replace l with (hl ++ ctr ++ rev hl).
  apply pal_mirror_single.
  rewrite -> Heqctr. replace 1 with ((S n) - n).
  apply length_drop_take with (m:=n) (n:=S n) (l:=l).
  rewrite <- Hlen. simpl. apply ble_double. apply ble_succ. symmetry. apply ble_nat_refl.
  apply minus_Sn_n_eq_1.
  symmetry. apply rev_split_odd with (n:=n). apply Hlen. apply Hrev. apply Heqhl. apply Heqctr.
Qed.


Theorem even_ev : forall (n:nat),
  true = evenb n -> ev n.
Proof.
  intros n H. induction n as [|n'].
  Case "n=0". apply ev_0.
  Case "n=Sn".
Admitted.

Theorem nat_inj : forall (n m:nat),
  S n = S m -> n = m.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Theorem nat_inj': forall (n m:nat),
  n = m -> S n = S m.
Proof.
  intros n m H. rewrite -> H. reflexivity.
Qed.

Theorem double_halve : forall (n:nat),
  ev n -> n = double (halve n).
Proof.
  intros n E. induction E as [|E].
  Case "ev0". simpl. reflexivity.
  Case "evSS". simpl. apply nat_inj'. apply nat_inj'. apply IHE.
Qed.

Definition one_if_odd (n:nat) : nat :=
  if (evenb n) then 0 else 1.

Definition pred_if_odd (n:nat) : nat :=
  if (evenb n) then n else (pred n).

Fixpoint pred_if_odd' (n:nat) : nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (S (pred_if_odd' n'))
  end.

Theorem even_double_halve : forall (n:nat),
  (pred_if_odd' n) = double (halve (pred_if_odd' n)).
Proof.
  intro n. induction n as [|n].
  Case "n=0". simpl. reflexivity.
  Case "n=Sn". remember (evenb n) as even. destruct even.
    SCase "even". unfold pred_if_odd'.
Admitted.
(* unfold pred_if_odd in IHn. rewrite <- Heqeven in IHn.
      assert (false = evenb (S n)). rewrite <- negb_involutive. rewrite <- evenb_n__oddb_Sn. rewrite <- Heqeven. simpl. reflexivity.
      rewrite <- H. simpl. apply IHn.
    SCase "odd". unfold pred_if_odd. assert (true = evenb (S n)). rewrite <- negb_involutive. rewrite <- evenb_n__oddb_Sn. rewrite <- Heqeven. simpl. reflexivity.
      rewrite <- H. simpl
*)
(*
  intro n. induction n as [|n].
  Case "n=0". simpl. reflexivity.
  Case "n=Sn".

simpl. unfold one_if_odd. remember (evenb (S n)) as evenb_Sn. destruct evenb_Sn.
    SCase "evenb (S n) = true".  destruct n as [|n'].
      SSCase "n=0". simpl in Heqevenb_Sn. inversion Heqevenb_Sn.
      SSCase "n=Sn".
*)

Theorem ev_pred : forall (n:nat),
  false = evenb n -> ev (pred n).
Proof.
Admitted.

Theorem rev_pal : forall (X:Type) (l:list X),
  l = rev l -> pal l.
Proof.
Admitted.
(*
  intros X l H. remember (length l) as n. remember (ev n) as ev_n.  remember (evenb n) as even_n. destruct (even_n).
  Case "even_n = true". apply even_ev in Heqeven_n. remember (halve n) as m. assert (double m = length l).
    rewrite -> Heqm. rewrite <- Heqn. symmetry. apply double_halve. apply Heqeven_n.
    apply rev_split_ev_pal with (n:=m). apply H0. apply H.
  Case "even_n = false". remember (pred n) as pred_n. assert (ev pred_n). rewrite -> Heqpred_n. apply ev_pred. remember (halve pred_n) as m.
    apply rev_split_odd_pal with (n:=m). apply l. apply l. rewrite -> Heqm. assert (double (halve pred_n) = pred_n).
    symmetry. apply double_halve. apply H0. rewrite -> H1. rewrite ->Heqpred_n. simpl. destruct n.
    SCase "n=O". simpl in Heqeven_n. inversion Heqeven_n.
    SCase "n=Sn".  simpl. apply Heqn.
    apply H.
Qed.
*)

(** [] *)

(** **** Exercise: 4 stars, advanced (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

(* FILL IN HERE *)
(** [] *)


(** **** Exercise: 2 stars, optional (R_provability) *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(** [] *)


(* $Date: 2013-07-01 18:48:47 -0400 (Mon, 01 Jul 2013) $ *)
