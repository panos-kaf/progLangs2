From Stdlib Require Import Init.Nat Arith Bool.Bool.

(** Στοιχεία Σπουδαστή
Όνομα:  Παναγιώτης Νεκτάριος Κατσαλίφης  
ΑΜ:     03118939
*)


(** * Εργασία 1 (100 μονάδες + 10 μονάδες bonus) *)

(** Ο σκοπός αυτής της εργασίας είναι να εξοικειωθείτε με συναρτησιακό
    προγραμματισμό και την ανάπτυξη αποδείξεων στο Rocq Proof Assistant.

    Οδηγίες:

    - Μπορείτε να χρησιμοποιείτε μόνο τα tactics που έχουμε κάνει στο μάθημα.  

    - Δεν μπορείτε να χρησιμοποιήσετε θεωρήματα από τη βιβλιοθήκη, εκτός και αν
      αυτό υποδεικνύεται από την άσκηση.

    - Εάν κολλήσετε σε κάποιο ενδιάμεσο lemma ή proof goal, μπορείτε να
      χρησιμοποιήσετε [admit] ώστε να ολοκληρώσετε την άσκηση και να βαθμολογηθείτε
      για ό,τι έχετε λύσει.
    
    - Το παραδοτέο αρχείο θα πρέπει να κάνει compile. Αυτό μπορείτε να το ελέγξετε 
      στο terminal σας με την εντολή `rocq assignment1.v`. Τα αρχεία που δεν κάνουν
      compile δεν θα βαθμολογούνται.

    - Όταν ολοκληρώνετε κάποια απόδειξη, αντικαταστήστε το τελικό [Admitted] με
      [Qed].

    - Μην αλλάζετε τον κώδικα και το κείμενο που σας έχουν δοθεί. Μην γράφετε
      μέσα στα σχόλια της βαθμολόγησης. Αυτό είναι απαραίτητο για την ομαλή
      και έγκαιρη βαθμολόγηση των εργασιών. Μπορείτε να γράψετε όπου υπάρχει η
      οδηγία (*  ___ FILL IN HERE ___ *). Εάν σας εξυπηρετεί, μπορείτε
      να ορίζετε βοηθητικές συναρτήσεις, λήμματα, ορισμούς, κ.α.
      
    - Συμπληρώστε σωστά τα στοιχεία σας στην αρχή του αρχείου. Αυτό είναι 
      απαραίτητο για την σωστή βαθμολόγηση των εργασιών. *)

(** ** Άσκηση 1 (προθέρμανση): Booleans (20 μονάδες) *)

(** Από την Boolean άλγεβρα γνωρίζουμε τους παρακάτω βασικούς κανόνες.

    - ~ ~ x = x                             (απαλοιφή της διπλής άρνησης)
    - ~ (x && y) = (~ x) || (~ y)           (νόμος De Morgan)
    - x || y || z = x || (y || z)           (προσεταιριστικότητα)
    - (x || y) && z = (x && z) || (y && z)  (επιμεριστική ιδιότητα)


   Η άσκηση σάς ζητά να αποδείξετε τους παραπάνω κανόνες.

*)

Lemma double_negation_elimination:
  forall x, negb (negb x) = x.
Proof.
    intros x.
    unfold negb.
    destruct x.
    - reflexivity.
    - reflexivity.
Qed.

(* [double_negation_elimination] Grade: 0/3 *)

Lemma DeMorgan_neg_or:
  forall x y, negb (x && y) = (negb x) || (negb y).
Proof.
    intros x y.
    unfold negb.
    destruct x, y.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(* [DeMorgan_neg_or] Grade: 0/5 *)

Lemma or_assoc:
  forall x y z, x || y || z = x || (y || z).
Proof.
    intros x y z.
    destruct x.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(* [or_assoc] Grade: 0/6 *)

(* Helper lemmas *)
Lemma x_and_true:
    forall x, x && true = x.
Proof.
    destruct x.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Lemma x_and_false:
    forall x, x && false = false.
Proof.
    destruct x.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.
(* - - - - - - - - *)

Lemma or_and_distr:
  forall x y z, (x || y) && z = (x && z) || (y && z).
Proof.
    intros x y z.
    destruct z.
    - repeat(rewrite x_and_true). reflexivity.
    - repeat(rewrite x_and_false). simpl. reflexivity.
Qed.

(* [or_and_distr] Grade: 0/6 *)

(** ** Άσκηση 2: Φυσικοί Αριθμοί (35 μονάδες) *)

(** Η συνάρτηση βιβλιοθήκης [mul] ορίζει τον πολλαπλασιασμό. Ο ορισμός της
    είναι ο ακόλουθος. *)

Print mul. 

(** Η άσκηση σας ζητά να αποδείξετε ότι το [0] είναι το απορροφητικό στοιχείο
    του πολλαπλασιασμού. *) 

Lemma mul_zero_abs_l :
  forall (m : nat), 0 * m = 0.
Proof.
    intros m.
    unfold mul.
    reflexivity.
Qed.
(* [mul_zero_abs_l] Grade: 0/5 *)

Lemma mul_zero_abs_r :
  forall (m : nat), m * 0 = 0.
Proof.
    intros m.
    induction m.
    - rewrite(mul_zero_abs_l). reflexivity.
    - simpl. 
    (*
    (Για δικη μου κατανοηση του simplification)
    εχουμε S m * 0 => 
    match S m with 0 + m*0 => 
    match 0 + m*0 with m*0 => 
    m*0 = 0 
    *)
    rewrite IHm. reflexivity.
Qed.

(* [mul_zero_abs_r] Grade: 0/10 *)

(** Παρατηρήστε ότι το ένα από τα δύο λήμματα έχει αρκετά πιο εύκολη
    απόδειξη από το άλλο. Γιατί συμβαίνει αυτό; Εξηγήστε σύντομα.

    Απάντηση: 
        Στο mul_zero_abs_l έχουμε το 0 
        στην αριστερή μεριά του πολλαπλασιασμού
        οπότε εφαρμόζεται απ'ευθείας το match 0 => 0
        από τον ορισμό του mul.

        Στο mul_zero_abs_r έχουμε το 0
        στην δεξιά μεριά του πολλαπλασιασμού
        οπότε τώρα πρέπει με επαγωγή να δείξουμε
        οτι 0*0 = 0 (βάση), το οποίο δείχνουμε είτε με
        το προηγούμενο lemma είτε απλά με simpl.
        και οτι m * 0 = 0 => S m * 0 = 0 (βήμα)
        (το οποίο εξηγείται σε παραπάνω σχόλιο)
    *)

    
(** Χρησιμοποιήστε την [mul] για να γράψετε μια συνάρτηση [exp] που
    υψώνει το πρώτο της όρισμα [base] στη δύναμη που δίνεται από το
    δεύτερο όρισμα, [power] *) 

Fixpoint exp (base power : nat) : nat :=
match power with
| 0 => S 0
| S rpower => base * exp base rpower
end
.


(* [exp] Grade: 0/5 *)


(** Αποδείξτε ότι η ύψωση σε δύναμη με εκθέτη m + n ισούται με το
    γινόμενο της ίδιας βάσης υψωμένης στους εκθέτες m και n
    αντίστοιχα.

    Μπορείτε να χρησιμοποιήσετε τα θεωρήματα της βιβλιοθήκης που
    αποδεικνύουν ότι το 0 είναι το ουδέτερο στοιχείο της πρόσθεσης και
    ότι ο πολλαπλασιασμός είναι προσεταιριστικός.

    Χρησιμοποιήστε την εντολή Search που είδαμε στο μάθημα για να τα
    αναζητήσετε στη βιβλιοθήκη. *)
Search (_*_ = _*_). (* Nat.mul_assoc *)
Search (_+0).       (* Nat.add_0_r *)

Lemma exponent_addition :
  forall base pow1 pow2,
    exp base (pow1 + pow2) = exp base pow1 * exp base pow2.
Proof.
    intros base pow1 pow2.
    induction pow1.
    - simpl. rewrite Nat.add_0_r. reflexivity.
    - simpl. rewrite IHpow1. rewrite Nat.mul_assoc. reflexivity.
Qed.

(* [exponent_addition] Grade: 0/15 *)


(** ** Άσκηση 3: Ισότητα Φυσικών Αριθμών (15 μονάδες) *)

(** Συμπληρώστε τον ορισμό μιας συνάρτησης που ελέγχει αν δύο φυσικοί
    αριθμοί είναι ίσοι και επιστρέφει την τιμή [true] αν τα δύο
    ορίσματα είναι ίσα και [false] διαφορετικά *)

Fixpoint test_eq (n1 n2 : nat) : bool :=
match n1, n2 with
| 0 , 0 => true
| 0 , S _ => false
| S _ , 0 => false
| S n1' , S n2' => test_eq n1' n2'
end
. 


(* [test_eq] Grade: 0/5 *)

(** Αποδείξτε ότι ο ορισμός της [test_eq] είναι συνεπής. Ότι δηλαδή η
    κλήση [test_eq n1 n2] επιστρέφει [true] μόνο αν [n1 = n2]. *)

Lemma test_eq_sound :
  forall n1 n2, test_eq n1 n2 = true -> n1 = n2. 
Proof.
  intros n1; induction n1; intros n2.
  - simpl. destruct n2.
    -- reflexivity.
    -- discriminate.
  - simpl. destruct n2.
    -- discriminate.
    -- intros H. 
       apply IHn1 in H. 
       rewrite H. 
       reflexivity. 
Qed.

(* [test_eq_sound] Grade: 0/10 *)


(* Bonus ερώτημα: Είναι αυτή η απόδειξη αρκετή ώστε να εξασφαλίσουμε
   ότι ο ορισμός μας είναι ορθός; Αποδείξτε την αντίθετη κατεύθυνση
   που εξασφαλίζει πληρότητα.

   Προσοχή! Αυτή η απόδειξη μπορεί να χρειαστεί tactics που θα
   διδαχτούμε στο δεύτερο μάθημα.  *)

Lemma test_eq_complete :
forall n1 n2, n1 = n2 -> test_eq n1 n2 = true.
Proof.
  intros n1 n2 H.
  subst n2.
  induction n1.
    - simpl. reflexivity.
    - simpl. rewrite IHn1. reflexivity.
Qed.

(* [test_eq_complete] Bonus Grade: 0/10 *)


(** ** Άσκηση 4: Αναδρομικές Συναρτήσεις Υψηλής Τάξης – Η Συνάρτηση Ackermann (30 μονάδες) *)

(* Η [συνάρτηση Ackermann](https://en.wikipedia.org/wiki/Ackermann_function)
   είναι ένα από τα απλούστερα και διασημότερα παραδείγματα μιας καθολικής
   συνάρτησης (total function) που είναι υπολογίσιμη αλλά δεν μπορεί
   να οριστεί με [πρωτογενή αναδρομή](https://en.wikipedia.org/wiki/Primitive_recursive_function).

   Ο ορισμός της συνάρτησης είναι ο εξής:

   Ack(0, n) = n + 1
   Ack(m, 0) = Ack(m-1, 1) όταν m > 0
   Ack(m, n) = Ack(m-1, Ack(m, n-1)) όταν m > 0 και n > 0

 *)

(* Προσπαθήστε να ορίσετε αυτή τη συνάρτηση ως μια αναδρομική
   συνάρτηση δύο ορισμάτων. Είναι η προσπάθεια επιτυχής; Γιατί;
   Εξηγήστε σύντομα. *)

(*
    Οχι, δεν είναι επιτυχής ο ορισμός 
    επειδή το ack(m-1, ack(m, n-1))
    δεν είναι δομικά μικρότερο του ack(m, n)
*)

Fail Fixpoint ack (m n : nat):= 
match m, n with
| 0 , _ => S n
| S m' , 0 => ack m' 1
| S m' , S n' => ack m' (ack m n')
end
.

(* Απάντηση: ___ FILL IN HERE ___ *)

(* [ack_fail] Grade: 0/5 *)

(* Στη συνέχεια, δώστε έναν έγκυρο ορισμό της συνάρτησης Ackermann. *)

(* Υπόδειξη: Μπορείτε να ορίσετε τη συνάρτηση Ackermann ως μια
   αναδρομική συνάρτηση που λαμβάνει ένα όρισμα και επιστρέφει μια
   αναδρομική συνάρτηση που λαμβάνει το δεύτερο όρισμα. Και οι δύο
   συναρτήσεις είναι αναδρομικές ως προς το όρισμά τους.

   Για να ορίσετε την εσωτερική συνάρτηση αναδρομικά μπορείτε να
   χρησιμοποιήσετε ένα εμφωλευμένο fixpoint, όπως φαίνεται στο
   παρακάτω παράδειγμα. *)


Definition nested_fix (n : nat) :=
  fix inner (m : nat) :=
    match m with
    | 0 => n
    | S m' => S (inner m')
    end.

    (*
    Ack(0, n) = n + 1
    Ack(m, 0) = Ack(m-1, 1) όταν m > 0
    Ack(m, n) = Ack(m-1, Ack(m, n-1)) όταν m > 0 και n > 0
    *)

Fixpoint ack (m : nat) : nat -> nat :=
 match m with
 | 0 => fun n => S n
 | S m' => fix ack_helper (n : nat) :=
            match n with
             | 0 => ack m' 1
             | S n' => ack m' (ack_helper n')
             end
end
.
  
(* [ack] Grade: 0/10 *)

(* Τέλος, αποδείξτε ότι [ack 1 n = n + 2]. Μπορείτε να χρησιμοποιήσετε
   το θεώρημα [Nat.add_comm] του standard library. *)

Lemma ackermann_1_n :
forall n, ack 1 n = n + 2.
Proof.
 intros n.
 simpl.
 induction n.
  - simpl. reflexivity.
  - rewrite IHn. reflexivity.
Qed.

(* [ackermann_1_n] Grade: 0/15 *)
