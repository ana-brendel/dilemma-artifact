From Dilemma Require Import Dilemma.
From QuickChick Require Import QuickChick.

Require Import Nat Arith.

Inductive Nat : Type := succ : Nat -> Nat |  zero : Nat.

Inductive Lst : Type := nil : Lst | cons : Nat -> Lst -> Lst.

(* ************************** [ QuickChick Stuff ] *************************** *)
Derive Show for Nat.
Derive Arbitrary for Nat.
Instance Dec_Eq_Nat : Dec_Eq (Nat).
Proof. dec_eq. Qed.

Derive Show for Lst.
Derive Arbitrary for Lst.
Instance Dec_Eq_lst : Dec_Eq (Lst).
Proof. dec_eq. Qed.

Fixpoint plus (plus_arg0 : Nat) (plus_arg1 : Nat) : Nat
           := match plus_arg0, plus_arg1 with
              | zero, n => n
              | succ n, m => succ (plus n m)
              end.

Fixpoint mult (mult_arg0 : Nat) (mult_arg1 : Nat) : Nat
           := match mult_arg0, mult_arg1 with
              | zero, n => zero
              | succ n, m => plus (mult n m) m
              end.

Fixpoint qmult (qmult_arg0 : Nat) (qmult_arg1 : Nat) (qmult_arg2 : Nat) : Nat
           := match qmult_arg0, qmult_arg1, qmult_arg2 with
              | zero, n, m => m
              | succ n, m, p => qmult n m (plus p m)
              end.

Lemma plus_assoc : forall (x y z : Nat), plus (plus x y) z = plus x (plus y z).
Proof. Admitted.

Lemma plus_commut : forall (x y : Nat), plus x y = plus y x.
Proof. Admitted.

Lemma goal34_by_plus_assoc_2 : forall (x y z a : Nat), plus (qmult x y z) a = qmult x y (plus z a).
Proof.
  intro.
  induction x.
  - intros. simpl. rewrite IHx. rewrite plus_assoc. 
  rewrite (plus_commut y a). 
  dilemma. Admitted.
  (* rewrite <- plus_assoc. reflexivity.
  - reflexivity.
Qed. *)
