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

Fixpoint eqb (n m: Nat) : bool :=
  match n, m with
    | zero, zero => true
    | zero, succ _ => false
    | succ _, zero => false
    | succ n', succ m' => eqb n' m'
  end.

Fixpoint less (less_arg0 : Nat) (less_arg1 : Nat) : bool
           := match less_arg0, less_arg1 with
              | x, zero => false
              | zero, succ x => true
              | succ x, succ y => less x y
              end.

Fixpoint len (len_arg0 : Lst) : Nat
           := match len_arg0 with
              | nil => zero
              | cons x y => succ (len y)
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

Theorem insort_len: forall (n: Nat) (x : Lst), len (insort n x) = succ (len x).
Proof. intro. induction x.
  + simpl. reflexivity.
  + simpl. destruct (less n n0). ++ simpl. reflexivity. ++ simpl. rewrite IHx. reflexivity.
Qed.

Theorem goal48_by_insort_len : forall (x : Lst), eq (len (sort x)) (len x).
Proof.
  induction x; simpl; try reflexivity.
  dilemma. Admitted.
  (* rewrite insort_len.
  f_equal; assumption.
Qed. *)
