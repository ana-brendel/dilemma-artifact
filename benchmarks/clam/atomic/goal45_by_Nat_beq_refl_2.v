From Dilemma Require Import Dilemma.
From QuickChick Require Import QuickChick.

Require Import Nat Arith Bool.

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

Scheme Equality for Nat.

Fixpoint less (less_arg0 : Nat) (less_arg1 : Nat) : bool
           := match less_arg0, less_arg1 with
              | x, zero => false
              | zero, succ x => true
              | succ x, succ y => less x y
              end.

Fixpoint mem (mem_arg0 : Nat) (mem_arg1 : Lst) : bool
           := match mem_arg0, mem_arg1 with
              | x, nil => false
              | x, cons y z => orb (Nat_beq x y) (mem x z)
              end.

Fixpoint insort (insort_arg0 : Nat) (insort_arg1 : Lst) : Lst
           := match insort_arg0, insort_arg1 with
              | i, nil => cons i nil
              | i, cons x y => if less i x then cons i (cons x y) else cons x (insort i y)
              end.

Fixpoint sort (sort_arg0 : Lst) : Lst
           := match sort_arg0 with
              | nil => nil
              | cons x y => insort x (sort y)
              end.

Lemma Nat_beq_refl : forall (n : Nat), Nat_beq n n = true.
Proof. Admitted.

Theorem goal45_by_Nat_beq_refl_2 : forall (x : Nat) (y : Lst), eq (mem x (insort x y)) true.
Proof.
  intros.
  induction y.
  - simpl. rewrite Nat_beq_refl. reflexivity.
  - simpl. destruct (less x n).
    + simpl. 
    dilemma. Admitted.
    (* rewrite Nat_beq_refl. reflexivity.
    + simpl. rewrite IHy. apply orb_true_r.
Qed. *)
