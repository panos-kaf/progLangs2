Lemma id_equality : forall (A : Type) (x : A), id A x = x.
Proof.
  intros A x.
  unfold id. 
  reflexivity. 
Qed.

Lemma or_true_false : true || false = true.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma de_morgan_law : forall (x y : bool), 
    (negb x) && (negb y) = negb (x || y).
Proof.
  intros x y.
  destruct x.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma add_O_n :
  forall n : nat, O + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Lemma eq_transitive :
  forall x y z : nat,
    x = y -> y = z -> x = z.
Proof.
  intros x y z.
  intros Heq1 Heq2.
  rewrite Heq1.
  rewrite <- Heq1.
  rewrite <- Heq1 in Heq2.
  assumption.
Qed.

Lemma add_eq_example:
  forall n1 n2 n3 n4,
    n1 = n2 ->
    n3 = n4 ->
    n1 + n3 = n2 + n4.
Proof.
  intros n1 n2 n3 n4 Heq1 Heq2.
  rewrite Heq1, Heq2.
  reflexivity.
Qed.

Lemma succ_not_zero:
    forall n, 1 + n =? 0 = false.
Proof.
  intros n.
  simpl. 
  reflexivity.
Qed.

Lemma succ_not_zero_prop:
    forall n, 1 + n = 0 -> False.
Proof.
    intros n H1. simpl in *.

Abort. 

Lemma S_injective :
  forall n m,
    S n = S m ->
    n = m.
Proof.
  intros n m Heq.

  injection Heq as Heq'.
  assumption.
Qed.

Lemma S_injective_prim :
  forall n m,
    S n = S m ->
    n = m.
Proof.
  intros n m Heq.

  assert (Heq' : pred (S n) = pred (S m)).
  { rewrite Heq. reflexivity. }

  simpl in Heq'. assumption.
Qed.


Lemma O_eq_S_absurd :
  forall x,
    O = S x ->
    3 = 4.
Proof.
  intros x H.
  discriminate H.
Qed.

Lemma true_eq_false_absurd :
  true = false -> 3 = 4.
Proof.
  intros H.
  discriminate H.
Qed.

Lemma succ_not_zero_prop:
    forall n, 1 + n = 0 -> False.
Proof.
    intros n H1. simpl in *. discriminate H1.
Qed.


Lemma add1_not_zero:
  forall n, n + 1 = 0 -> False.
Proof.
  intros n Heq. simpl in Heq.

  Fail discriminate Heq.

  destruct n as [ | n'] eqn:Heq'.

  - (* case [n = 0] *)
    simpl in *. discriminate Heq.

  - (* case [n = S n'] *)
    simpl in *. discriminate Heq.
Qed.

Lemma add_n_O : forall n : nat, n + 0 = n.
Proof.
  intros n. simpl. (* does nothing *)

  destruct n as [ | n' ].

    reflexivity.

    simpl.

    assert (Heq' : n' + 0 = n').
    { 
      admit.
    }

    rewrite Heq'. reflexivity.

Abort. 

Lemma add_n_O : forall n : nat, n + 0 = n.
Proof.
  intros n. simpl.

  induction n as [ | n' IHn' ].

  - simpl. reflexivity.

  - 
    simpl.

    rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros n m.
  induction n as [ | n' IHn' ].
  - 
    simpl. rewrite add_n_O. reflexivity.
  - 
    simpl.
    rewrite IHn'.
    rewrite <- PeanoNat.Nat.add_succ_r.
    reflexivity.
Qed.

Lemma fst_snd_eq :
  forall A B (x : A * B) y,
    fst x = fst y ->
    snd x = snd y ->
    x = y.
Proof.
  intros A B x y Heq1 Heq2.
  destruct x as [a1 b1] eqn:Heqa.
  destruct y as [a2 b2].
  simpl in *.
  subst.
  reflexivity.
Qed.

Lemma length_app :
  forall A (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2. induction l1 as [ | x l1' IHl1 ]; simpl.
  - (* case l1 = [] *)
    reflexivity.
  - (* case l1 = x :: l1' *)
    rewrite IHl1. reflexivity.
Qed.

Lemma map_compose :
  forall A B C (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (comp g f) l.
Proof.
  intros A B C f g l.

  induction l as [ | x l' IHl].
  - reflexivity.
  - simpl. rewrite IHl.
    reflexivity.
Qed.

Lemma rev_rev_fast :
  forall A (l : list A), rev l = rev_fast l.
Proof.
  intros A l. unfold rev_fast.
  induction l as [| x l' IHl']; unfold rev_fast; simpl.
  - reflexivity.
  - unfold rev_fast in *.
Abort.

Lemma rev_rev_fast_aux_first_try :
  forall A (l : list A) (acc : list A),
    rev l ++ acc = rev_fast_aux l acc.
Proof.
  intros A l acc.  induction l as [| x l' IHl']; simpl.
  - (* case l = [] *)
    reflexivity.
  - (* case l = x :: l' *)
    simpl.
    Fail rewrite <- IHl'. (* Why? *)
Abort.

Lemma rev_rev_fast_aux :
  forall A (l : list A) (acc : list A),
    rev l ++ acc = rev_fast_aux l acc.
Proof.
  intros A l acc. revert acc.
  induction l as [| x l' IHl']; simpl.
  - (* case l = [] *)
    intros acc. reflexivity.
  - (* case l = x :: l' *)
    intros acc.
    rewrite <- IHl'.
    rewrite <- app_assoc. simpl. reflexivity.
Qed.

Theorem rev_rev_fast :
  forall A (l : list A), rev l = rev_fast l.
Proof.
  intros A l.
  unfold rev_fast.
  rewrite <- rev_rev_fast_aux.
  rewrite app_nil_r. reflexivity.
Qed.
