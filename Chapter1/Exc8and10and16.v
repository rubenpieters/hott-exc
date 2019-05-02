Inductive Nat : Set :=
| Z : Nat
| S : Nat -> Nat.

Check Nat_rect.
Check Nat_rec.
Check Nat_ind.

(* Path induction not provided by default in Coq *)
(* Taken from http://blog.ezyang.com/2013/06/homotopy-type-theory-chapter-one/ *)
Definition eq_ind'
     : forall (A : Type), forall (C : forall (x y : A), x = y -> Type),
       (forall (x : A), C x x (eq_refl x)) -> forall (x y : A), forall (p : x = y), C x y p.
Proof. intros; subst; auto. Qed.

(* Congruence for Eq *)
Definition f_equal' {A B : Type} (f : A -> B) {a b : A} : a = b -> f a = f b :=
  fun (p : a = b) =>
  eq_ind' A (fun m n (p : m = n) => f m = f n) (fun x => eq_refl (f x)) a b p.
Check f_equal'.

(****************************)
Section OneSixteen.             (* Related to exercise 1.16 *)
Fixpoint Add (x : Nat) : Nat -> Nat :=
   match x with
   | Z => fun y => y
   | S x' => fun y => S (Add x' y)
   end.

Definition Add' :=
  Nat_rec
    (fun x => Nat -> Nat)           (* Constant type family *)
    (fun y => y)                   (* Case Zero *)
    (fun (x : Nat) => fun (g : Nat -> Nat) => fun (y : Nat) => S (g y)). (* Case Succ *)
Eval compute in (Add' (S Z) (S Z)).

Definition Add_lunit_zero' :=
  Nat_rec
    (fun n => Add' Z n = n)
    (eq_refl Z)
    (fun n => fun (p : Add' Z n = n) => f_equal' S p).

Definition Add_runit_zero' :=
  Nat_rec
    (fun n => Add' n Z = n)
    (eq_refl Z)
    (fun n => fun (p : Add' n Z = n) => f_equal' S p).

Definition Add_succ_right' :=
  Nat_rec
    (fun m => forall n, Add' m (S n) = S (Add' m n))
    (fun n => eq_refl (S n))
    (fun m p n => f_equal' S (p n)).
Check Add_succ_right'.

(* Needs eq_trans and eq_sym and f_equal'*)
Definition Add_comm' :=
  Nat_rec
    (fun m => forall n, Add' m n = Add' n m)
    (fun n => eq_trans (Add_lunit_zero' n) (eq_sym (Add_runit_zero' n)))
    (fun m p n => eq_trans (f_equal' S (p n)) (eq_sym (Add_succ_right' n m))).
Check Add_comm'.
End OneSixteen.

(****************************)
(* Exercise 1.8 
 * Partial solution : not all properties of semiring are proven.
 *)
Section OneEight.
Fixpoint Mult (m: Nat) : Nat -> Nat :=
  match m with
  | Z => fun x => Z
  | S m' => fun n => Add' n (Mult m' n)
  end.

Definition Mult' :=
  Nat_rec
    (fun m => Nat -> Nat)
    (fun n => Z)
    (fun (m : Nat) => fun (g : Nat -> Nat) => fun (n : Nat) => Add' n (g n)).
Eval compute in (Mult' (S (S Z)) (S (S Z))).
Eval compute in (Mult' (S (S Z)) Z).

Fixpoint Expon (b e : Nat) {struct e} : Nat := 
  match e with
  | Z => S Z
  | S e' => Mult' b (Expon b e')
  end.

(* Decreasig argument must be the first one, 
 * so argument order is swapped in Expon'. *)
Definition Expon' := Nat_rec
                      (fun e => Nat -> Nat)
                      (fun b => S Z)
                      (fun (e : Nat) => fun (g : Nat -> Nat) => fun (b : Nat) => Mult' b (g b)).
Eval compute in (Expon' (S (S Z)) (S (S (S Z)))).

Fixpoint Add_assoc (m n l : Nat) : Add' m (Add' n l) = Add' (Add' m n) l :=
  match m with
  | Z => eq_refl (Add' n l)
  | S m' => f_equal S (Add_assoc m' n l)
  end.

(* I also need f_equal' *)
Definition Add_assoc' :=
  Nat_rec
    (fun m => forall n l, Add' m (Add' n l) = Add' (Add' m n) l)
    (fun n l => eq_refl (Add' n l))
    (fun m => fun p => fun n l => f_equal' S (p n l)).
Check Add_assoc'.

Definition Mult_lunit_one' :=
  Nat_rec
    (fun n => Mult' (S Z) n = n)
    (eq_refl Z)
    (fun n p => f_equal' S p).
Check Mult_lunit_one'.

Definition Mult_runit_one' :=
  Nat_rec
    (fun n => Mult' n (S Z) = n)
    (eq_refl Z)
    (fun n p => f_equal' S p).
Check Mult_runit_one'.

Definition Mult_right_zero :=
  Nat_rec
    (fun n => Mult n Z = Z)
    (Add_lunit_zero' Z)
    (fun n p => p).
Check Mult_right_zero.

Definition Mult_comm' :=
  Nat_rec
    (fun n => forall m, Mult' m n = Mult' n m)
    (fun m => Mult_right_zero m).
Check Mult_comm'.
End OneEight.

Section Ackermann.              (* Exercise 1.10 *)
Fixpoint Ack1' (f : Nat -> Nat) (n : Nat) :=
  match n with
  | Z => f (S Z)
  | S n' => f (Ack1' f n')
  end.

Fixpoint Ack1 m := fun n =>
  match m with
  | Z => (S n)
  | S m' => Ack1' (Ack1 m') n
  end.


Definition Ack' (f : Nat -> Nat) := 
  Nat_rec
    (fun m => Nat)
    (f (S Z))
    (fun m n => f n).
Check Ack'.

Definition Ack :=
  Nat_rec
    (fun m => Nat -> Nat)
    (fun n => S n)
    (fun m g n => Ack' g n).


Check Ack.
Eval compute in (Ack Z (S Z)).
Eval compute in (Ack (S Z) Z).
Eval compute in (Ack (S (S Z)) (S (S Z))).
Eval compute in (Ack (S (S Z)) (S Z)).
End Ackermann.

Inductive Eq {A: Type} : A -> A ->  Prop :=
| refl' (x : A) : Eq x x.

Inductive BasedEq' {A : Type} (a : A) : A -> Prop :=
  | brefl' : BasedEq' a a.