From Stdlib Require Import Strings.String Arith.Arith Lia.
(* Suppress warnings when overriding notations *)
Set Warnings "-notation-overriden, -parsing".

Require Import imp.

(** Στοιχεία Σπουδαστή
Όνομα:  
ΑΜ: 
*)


(** * Εργασία 3 (100 μονάδες + 20 μονάδες bonus) *)

(** Ο σκοπός αυτής της εργασίας είναι να εξοικειωθείτε με τους
    σημασιολογικούς ορισμούς απλών γλωσσών και τις αποδείξεις
    σημασιολογικής ορθότητας.

    Οδηγίες:

    - Μην αλλάζετε τα ονόματα των αρχείων που σας δίνονται.

    - [NEW] Μπορεί να σας φανεί χρήσιμο το tactic [lia] που υλοποιεί μια διαδικασία 
      που επιλύει goals linear integer arithmetic.

    - [NEW] Μπορείτε να χρησιμοποιείτε όποια tactics θέλετε. Τα tactics που
      έχουμε κάνει στο μάθημα αρκούν για την επίλυση των προβλημάτων.

    - [NEW] Μπορείτε να χρησιμοποιήσετε θεωρήματα από τη βιβλιοθήκη.

    - Εάν κολλήσετε σε κάποιο ενδιάμεσο λήμμα, μπορείτε να χρησιμοποιήσετε
      [admit] ώστε να ολοκληρώσετε την άσκηση και να βαθμολογηθείτε για ό,τι
      έχετε λύσει.

    - Το παραδοτέο αρχείο θα πρέπει να κάνει compile. Αυτό μπορείτε να το
      ελέγξετε στο terminal σας με την εντολή `rocq assignment3.v`. Τα αρχεία
      που δεν κάνουν compile δεν θα βαθμολογούνται.

    - Όταν ολοκληρώνετε κάποια απόδειξη, αντικαταστήστε το τελικό [Admitted] με
      [Qed].

    - Μην αλλάζετε τον κώδικα και το κείμενο που σας έχουν δοθεί. Μην γράφετε
      μέσα στα σχόλια της βαθμολόγησης. Αυτό είναι απαραίτητο για την ομαλή και
      έγκαιρη βαθμολόγηση των εργασιών. Μπορείτε να γράψετε όπου υπάρχει η
      οδηγία (*  ___ FILL IN HERE ___ *). Εάν σας εξυπηρετεί, μπορείτε
      να ορίζετε βοηθητικές συναρτήσεις, λήμματα, ορισμούς, κ.α.

    - Συμπληρώστε σωστά τα στοιχεία σας στην αρχή του αρχείου. Αυτό είναι
      απαραίτητο για τη σωστή βαθμολόγηση των εργασιών. *)


(** ** Άσκηση 1: Προθέρμανση (10 μονάδες + 10 μονάδες bonus) *)

(** Η άσκηση σας ζητά να γράψετε ένα πρόγραμμα Imp που να κάνει swap
    δύο μεταβλητές **χωρίς** τη χρήση ενδιάμεσων μεταβλητών και να
    αποδείξετε μία προδιαγραφή για αυτό το πρόγραμμα. *)

(** Ονόματα μεταβλητών *)
Definition X : string := "X".
Definition Y : string := "Y".

Definition SWAP : com
(* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

(* [swap] grade 0/2 *)

(* Hint: Θα σας φανούν χρήσιμά τα λήμματα [Nat.leb_gt] και [leb_complete] *)

Lemma swap_correct :
  forall st,
  exists st', st =[ SWAP ]=> st' /\ st' X = st Y /\ st' Y = st X.
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [swap_correct] grade 0/5 *)

(** Είναι αυτή η προδιαγραφή αρκετή; Πως θα μπορούσαμε να αποδείξουμε
    ότι το πρόγραμμα δεν επηρεάζει άλλες μεταβλητές; Απαντήστε
    σύντομα.

    Απάντηση: ___ FILL IN HERE ___

 *)

(* [swap_spec] grade 0/3 *)

(** Bonus: Αποδείξτε και τυπικά ότι το πρόγραμμα [SWAP] δεν επηρεάζει
    άλλες μεταβλητές. θα σας φανεί χρήσιμο το λήμμα [eqb_neq]. *)

Lemma swap_frame :
  forall (st : imp_state), False (* ___ FILL IN HERE ___ *).
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [swap_frame] bonus grade 0/10 *)

(** ** Άσκηση 2: Ορθότητα Constant Folding (50 μονάδες) *)

(** Το constant folding είναι μια βελτιστοποίηση κώδικα που
    χρησιμοποιούν οι μεταγλωττιστές κατά την οποία υπολογίζεται η τιμή
    σταθερών εκφράσεων και εφαρμόζονται απλοποιήσεις.

    Η άσκηση σας ζητάει να γράψετε ένα πέρασμα constant folding για
    την Imp και να το αποδείξετε σωστό.

    Θα ξεκινήσουμε με τις αριθμητικές εκφράσεις.

    Ο στόχος είναι να υπολογιστούν στατικά οι τιμές εκφράσεων που δεν
    περιέχουν μεταβλητές και να εφαρμοστούν συγκεκριμένες
    αριθμητικές απλοποιήσεις. Οι απλοποιήσεις είναι οι εξής:

    e + 0 = e
    0 + e = e
    0 - e = 0
    e - 0 = e
    e * 1 = e
    1 * e = e
    e * 0 = 0
    0 * e = 0

 *)

(** Γράψτε μια (μη αναδρομική) συνάρτηση [simplify_aexp] που απλοποιεί
    μια αριθμητική έκφραση σύμφωνα με τα παραπάνω.

    Για παράδειγμα ο όρος [<{ 0 + e }>] (δηλαδή το [APlus (ANum 0) e])
    θα πρέπει να απλοποιείται στο [e] ενώ ο όρος [<{ 11 + 31 }>] στο
    [42] *)

Definition simplify_aexp (e : aexp) : aexp
(* := ___ FILL IN HERE ___ *).
Admitted.

(* [simplify_aexp] grade 0/4 *)

(** Στη συνέχεια, γράψτε μια αναδρομική συνάρτηση [optimize_aexp] που να
    εφαρμόζει τη συνάρτηση [simplify_aexp] σε κάθε κόμβο του αφηρημένου
    συνακτικού δέντρου [aexp] με bottom-up τρόπο (δηλαδή από τους 
    εσωτερικούς κόμβους προς τους εξωτερικούς). *)

Fixpoint optimize_aexp (e : aexp) : aexp
(* := ___ FILL IN HERE ___ *).
Admitted.

(* [optimize_aexp] grade 0/4 *)

(** Sanity check: Εάν οι παραπάνω ορισμοί είναι σωστοί και πλήρεις,
    τότε τα παρακάτω tests θα πρέπει να επιτυγχάνουν. *)
Example test_optimize_aexp1: (optimize_aexp <{ 3 + (X * 1) - (1 * 4) * (1 * Y - 0) }> = <{ 3 + X - 4 * Y }>).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_optimize_aexp2: (optimize_aexp <{ 3 + (X * 1) - Z * (0 * Y + (11 - 2)) }> = <{ 3 + X - Z * 9 }>).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_optimize_aexp3: (optimize_aexp <{ (0 + (0 * X + 0)) - Z }> = <{ 0 }>).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)


(** Κάντε το ίδιο για τις λογικές εκφράσεις. Βρείτε ποιες εκφράσεις
    μπορείτε να αποτιμήσετε στατικά και ποιες απλοποιήσεις μπορείτε να
    κάνετε.*)

Definition simplify_bexp (e : bexp) : bexp
(* := ___ FILL IN HERE ___ *).
Admitted.

(* [simplify_bexp] grade 0/4 *)

Fixpoint optimize_bexp (e : bexp) : bexp
(* := ___ FILL IN HERE ___ *).
Admitted.

(* [optimize_bexp] grade 0/4 *)

(** Sanity check: Εάν οι παραπάνω ορισμοί είναι σωστοί και πλήρεις,
    τότε τα παρακάτω tests θα πρέπει να επιτυγχάνουν. *)
Example test_optimize_bexp1: (optimize_bexp <{ 17 <= 42 || 0 < X }> = <{ true }>).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_optimize_bexp2: (optimize_bexp <{ 42 < Y && 12 = 4 }> = <{ false }>).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

(* Τέλος, εφαρμόστε αυτές τις απλοποιήσεις στους κόμβους του
   αφηρημένου συνακτικού δέντρου της Imp. Απλοποιήστε ότι εντολές
   μπορούν μετά τις απλοποιήσεις να αποτιμηθούν στατικά. *)

Fixpoint optimize_com (c : com) : com
(* := ___ FILL IN HERE ___ *).
Admitted.

(* [optimize_com] grade 0/4 *)

(** Sanity check: Εάν ο παραπάνω ορισμός είναι σωστός και πλήρης,
    τότε το παρακάτω test θα πρέπει να επιτυγχάνει. *)

Example test_optimize_com: (optimize_com <{ if (0 <= X * 0) then X := 0 else X := 1 end }> = <{ X := 0 }>).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)


(** Αποδείξτε ότι οι παραπάνω συναρτήσεις είναι σωστές, δηλαδή
    διατηρούν τη σημασιολογία της αρχικής έκφρασης. *)

(** Ξεκινήστε αποδεικνύοντας ότι [ainterp st (simplify_aexp e) = ainterp st e].

    Σημείωση 1: Εφόσον ο ορισμός της παραπάνω συνάρτησης δεν είναι
    αναδρομικός, δεν θα χρειαστεί να κάνετε απόδειξη με επαγωγή.

    Σημείωση 2: Η παρακάτω απόδειξη έχει πολλές παρόμοιες περιπτώσεις.
    Μπορείτε να χρησιμοποιήσετε τις τεχνικές που μάθαμε στο μάθημα ώστε
    να ομαδοποιήσετε διαφορετικές περιπτώσεις της απόδειξης.

    Προκειμένου αυτό να γίνει πιο εύκολο, σας δίνεται το tactic
    [simpl_arith] το οποίο εφαρμόζει τους παραπάνω κανόνες απλοποίησης
    στους φυσικούς αριθμούς. To tactic αυτό ομαδοποιεί διάφορες
    απλοποιήσεις που θα χρειαστεί να κάνετε στο αποτέλεσμα του
    interpreter σε διάφορες περιπτώσεις της απόδειξής σας. Θα σας
    φανεί χρήσιμο ώστε να γράψετε proof scripts που να μπορούν να
    εφαρμοστούν σε πολλές παρόμοιες περιπτώσεις της απόδειξης.  *)

Ltac simpl_arith :=
  try rewrite <- plus_n_O; try rewrite plus_O_n;
  try rewrite PeanoNat.Nat.mul_1_r; try rewrite PeanoNat.Nat.mul_1_l;
  try rewrite PeanoNat.Nat.mul_0_r; try rewrite PeanoNat.Nat.mul_0_l;
  try rewrite PeanoNat.Nat.sub_0_l; try rewrite PeanoNat.Nat.sub_0_r.


Lemma simplify_aexp_correct :
  forall st (e : aexp), ainterp st (simplify_aexp e) = ainterp st e.
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [simplify_aexp_correct] grade 0/8 *)

(** Στη συνέχεια κάντε το ίδιο για την [simplify_bexp] *)

Ltac simpl_bool :=
  try rewrite Bool.orb_true_r; try rewrite Bool.orb_true_l;
  try rewrite Bool.andb_true_l;  try rewrite Bool.andb_true_r;
  try rewrite Bool.orb_false_r; try rewrite Bool.orb_false_l;
  try rewrite Bool.andb_false_l;  try rewrite Bool.andb_false_r.

Lemma simplify_bexp_correct :
  forall st (e : bexp), binterp st (simplify_bexp e) = binterp st e.
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [simplify_bexp_correct] grade 0/8 *)

(** Χρησιμοποιώντας το παραπάνω λήμμα αποδείξτε ότι
    [ainterp st (optimize_aexp e) = ainterp st e] και ότι
    [binterp st (optimize_bexp e) = binterp st e]. *)

(** Οι ακόλουθες εντολές θα αποτρέψουν τους ορισμούς των συναρτήσεων
    από το να γίνουν expand όταν κάνετε [simpl]. Αυτό είναι χρήσιμο
    ώστε να μην αντικατασταθούν οι κλήσεις στην [simplify] με το σώμα
    της συνάρτησης και να μπορέσετε να εφαρμόσετε τα λήμματα που έχετε
    δείξει. *)

Opaque simplify_aexp.
Opaque simplify_bexp.

Lemma optimize_aexp_correct :
  forall (st : imp_state) (e : aexp), ainterp st e = ainterp st (optimize_aexp e).
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [optimize_aexp_correct] grade 0/3 *)


Lemma optimize_bexp_correct :
  forall (st : imp_state) (e : bexp), binterp st e = binterp st (optimize_bexp e).
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [optimize_bexp_correct] grade 0/3 *)

(** Τέλος, διατυπώστε και αποδείξτε ένα θεώρημα για την ορθότητα
    αυτoύ μετασχηματισμού [optimize_com]. Χρησιμοποιήστε τον ορισμό
    [ceval] της big-step σημασιολογίας. *)

Opaque optimize_bexp.
Opaque optimize_aexp.

Theorem optimize_com_correct :
  forall st c st',
    st =[ c ]=> st' ->
    st =[ optimize_com c ]=> st'.
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [optimize_com_correct] grade 0/8 *)

Theorem optimize_com_correct_rev :
  forall st c st',
    st =[ optimize_com c ]=> st' ->
    st =[ c ]=> st'.
Proof.
(*  ___ FILL IN HERE ___ *)
Admitted.

Transparent simplify_aexp.
Transparent simplify_bexp.
Transparent optimize_bexp.
Transparent optimize_aexp.

(** ** Άσκηση 3: For Loops (40 μονάδες) *)

(** Σε αυτή την άσκηση σας ζητείται να προσθέσετε for loops στον
    ορισμό των εντολών [com] της Imp.

    Ένα for loop επεκτείνει τη γραμματική των εντολών <com> ως εξής:

    <com> := ... | for <com>; <bexp>; <com> do <com>

    Η πρώτη παράμετρος <com> εκτελείται μια φορά στην αρχή της εκτέλεσης
    του loop.

    Η δεύτερη παράμετρος <bexp> είναι η συνθήκη που καθορίζει αν η
    εκτέλεση του loop θα συνεχιστεί.

    Η τρίτη παράμετρος <com> εκτελείται μετά το τέλος κάθε επανάληψης
    του σώματος του loop.

    Τέλος, η τέταρτη παράμετρος <com> είναι το σώμα του loop.

    Για παράδειγμα το παρακάτω πρόγραμμα προσθέτει 5 στην τιμή της
    μεταβλητής [Y].

    <{ for (Z = 0, Z < 5, Z := Z + 1) { Y := Y + 1; } }> *)

Module ForLoops.

  (** Επεκτείνετε τον ορισμό του [com] με έναν κόμβο [CFor] που
      αναπαριστά το for loop *)
  Inductive com : Set :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (** __ FILL IN HERE __ **)
  .

  (* [com] grade 0/2 *)
  
  (** Επαναορίζουμε τα σχετικά notations ώστε να αναφέρονται στον νέο
      ορισμό [com]. *)

  Notation "'skip'" :=
    CSkip (in custom com at level 0) : com_scope.
  Notation "x := y" :=
    (CAsgn x y)
      (in custom com at level 0, x constr at level 0,
          y at level 85, no associativity) : com_scope.
  Notation "x ; y" :=
    (CSeq x y)
      (in custom com at level 90,
          right associativity) : com_scope.
  Notation "{ x }" := x (in custom com, x at level 50) : com_scope.
  Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
      (in custom com at level 88, x at level 89,
          y at level 89, z at level 89) : com_scope.
  Notation "'while' x 'do' y" :=
    (CWhile x y)
      (in custom com at level 88, x at level 89,
          y at level 89) : com_scope.

 Notation "'for' i ';' b ';' f 'do' c" :=
 (* Προσοχή!!! Αυτός ο ορισμός είναι λάθος.  *)
   (CIf b (CSeq i f) c)
     (in custom com at level 88, b at level 89,
         i at level 89, f at level 89, c at level 89) : com_scope.
 (* Aφού συμπληρώσετε τους παραπάνω ορισμούς, διαγράψτε τον παραπάνω
    ορισμό του notation και κάντε uncomment τον παρακάτω κώδικα.*)
 (*   (CFor i b f c) *)
 (*     (in custom com at level 88, b at level 89, *)
 (*         i at level 89, f at level 89, c at level 89) : com_scope. *)
  
  Reserved Notation "st '=[' c ']=>' st'"
    (at level 40, c custom com at level 99, st constr, st' constr at next level).

 (** Επεκτείνετε τον ορισμό [ceval] των big-step semantics με τις
     απαραίτητες περιπτώσεις για την εκτέλεση του For. Ίσως σας
     βοηθήσει να γράψετε πρώτα στο χαρτί τα inference rules για τα for
     loops και μετά να τα μετατρέψετε σε κώδικα. *)
  
  Inductive ceval : imp_state -> com -> imp_state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      ainterp st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      binterp st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      binterp st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      binterp st b = false ->
      st =[ while b do c ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      binterp st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c ]=> st'' ->
      st =[ while b do c ]=> st''
  (** __ FILL IN HERE __ **)
                                                                  
  where "st =[ c ]=> st'" := (ceval st c st').

  (* [ceval] grade 0/10 *)
  (** Κάντε uncomment το παρακάτω πρόγραμμα. *)
  Definition powY3 : com
  . Admitted.
  (* :=  <{ for Z := 0; Z < 3 ; Z := Z + 1 do Y := Y * Y }>.  *)

  (** Αποδείξτε την παρακάτω προδιαγραφή για το πρόγραμμα [powY3]. Σας
      δίνεται το tactic [simplify_state] που απλοποιεί τα states που
      προκύπτουν από το παραπάνω πρόγραμμα.

      Συγκεκριμένα κάνει τις εξής απλοποιήσεις, για κάθε [st] και [v]:

       (Ζ !-> v; st) Y = st y
       (Y !-> v; st) Y = v

      Μπορείτε να το χρησιμοποιήσετε για να απλοποιήσετε τα ενδιάμεσα
      και το τελικό state. Για να το εφαρμόσετε πολλές φορές
      χρησιμοποιήστε το μαζί με το tactical [repeat]. *)

  
  Ltac simplify_state :=
    match goal with
    | |- context[update_st ?st1 Z ?v Y] => 
        replace (update_st st1 Z v Y) with (st1 Y) by reflexivity
    | |- context[update_st ?st1 Y ?v Y] => 
        replace (update_st st1 Y v Y) with v by reflexivity
    end.

  
  Lemma powY3_correct :
    forall st,
    exists st', st =[ powY3 ]=> st' /\ st' Y = st Y ^ 8. 
  Proof.
  (*  ___ FILL IN HERE ___ *)
  Admitted.
  (* [powY3_correct] grade 0/8 *)
  
  (** Επεκτείνετε την απόδειξη ότι το [ceval] είναι μια ντετερμινιστική σχέση. *) 
  Lemma ceval_deterministic :
    forall st c st1 st2, 
      st =[ c ]=> st1 ->
      st =[ c ]=> st2 ->
      st1 = st2.
  Proof.
    intros st c st1 st2 Heval1. revert st2.
    induction Heval1; intros st2 Heval2.
    - (* E_Skip *)
      inversion Heval2; subst. reflexivity. 
    - (* E_Asgn *)
      inversion Heval2; subst. reflexivity. 
    - (* E_Seq *)
      inversion Heval2; subst. apply IHHeval1_2.
      
      rewrite IHHeval1_1 with (st2 := st'0). 
      + assumption.
      + assumption.

    - (* E_IfTrue *)
      inversion Heval2; subst. (* can be either [E_IfTrue] or [E_IfFalse] *)
      + apply IHHeval1. assumption.
      + congruence. (* contradiction *)

    - (* E_IfFalse *)
      inversion Heval2; subst. (* can be either [E_IfTrue] or [E_IfFalse] *)
      + congruence. (* contradiction *)
      + apply IHHeval1. assumption.

    - (* E_WhileFalse *)
      inversion Heval2; subst. (* can be either [E_WhileFalse] or [E_WhileTrue] *)
      + reflexivity.
      + congruence. (* contradiction *)

    - (* E_WhileTrue *)
      inversion Heval2; subst. (* can be either [E_WhileFalse] or [E_WhileTrue] *)
      + congruence. (* contradiction *)
      + apply IHHeval1_2.
        
        rewrite IHHeval1_1 with (st2 := st'0). 
        * assumption.
        * assumption.
  (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [ceval_deterministic] grade 0/20 *)

  (** Bonus ερωτήματα: αποδείξτε ότι το [for] μπορεί να γραφεί ισοδύναμα ως while. *)

  (** Αποδείξτε πρώτα ότι αν ξεκινώντας από ένα state το for
      τερματίζει σε ένα τελικό state, τότε η εκτέλεση του while στο
      ίδιο αρχικό state τερματίζει στο ίδιο τελικό state *)


  Lemma for_while :
    forall (st st' : imp_state) (i : com) (b : bexp) (f c : com),
      st =[ for i ; b ; f do c ]=> st' ->
      st =[ i; while b do { c ; f } ]=> st'.
  Proof.
    intros st st' i b f c Heval.
    (* προκειμένου να κάνουμε επαγωγή στο derivation Ηeval πρέπει όλα
       τα ορίσματα του να είναι μεταβλητές. Για το λόγο αυτό
       θέτουμε μια καινούρια μεταβλητή [c'] με την τιμή [for i ; b ; f do c ]
       και την αντικαθιστούμε στον τύπο του [Heval]. *)

    remember (<{ for i; b; f do c }>) as c' eqn:Heq.

    (* γενικεύουμε όλες τις μεταβλητές που δεν εμφανίζονται στο [Heval] *)
    revert i b c f Heq.

    (* κάνουμε επαγωγή στο derivation [Heval] *)
    induction Heval.
    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [for_while] bonus grade 0/5 *)


  (** Για να δείξετε την άλλη κατεύθυνση, αποδείξτε πρώτα ότι ένα
      while ισοδυναμεί με ένα for χωρίς εντολή αρχικοποίησης. *)

  Lemma while_for_aux :
    forall (st st' : imp_state) (i : com) (b : bexp) (f c : com),
      st =[ while b do { c ; f } ]=> st' ->
      st =[ for skip ; b ; f do c ]=> st'.
  Proof.
    intros st st' i b f c Heval.
    (* για την επαγωγή ακολουθούμε την ίδια τεχνική με το παραπάνω λήμμα *)
    remember (<{ while b do { c ; f } }> ) as c' eqn:Heq.
    revert b c f Heq.
    induction Heval.
    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [while_for_aux] bonus grade 0/4 *)


  (** Χρησιμοποιώντας το παραπάνω λήμμα, μπορούμε να δείξουμε το τελικό λήμμα. *)

  Lemma while_for :
    forall (st st' : imp_state) (i : com) (b : bexp) (f c : com),
      st =[ i; while b do { c ; f } ]=> st' ->
      st =[ for i ; b ; f do c ]=> st'.
  Proof.
    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [while_for] bonus grade 0/1 *)

End ForLoops.
