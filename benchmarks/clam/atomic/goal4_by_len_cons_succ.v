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

Fixpoint double (double_arg0 : Nat) : Nat
           := match double_arg0 with
              | zero => zero
              | succ n => succ (succ (double n))
              end.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint len (len_arg0 : Lst) : Nat
           := match len_arg0 with
              | nil => zero
              | cons x y => succ (len y)
              end.

Lemma len_cons_succ: forall l1 l2 n, succ (len (append l1 l2)) = len (append l1 (cons n l2)).
Proof. Admitted.

Theorem goal4_by_len_cons_succ : forall (x : Lst), eq (len (append x x)) (double (len x)).
Proof.
induction x.
   - reflexivity.
   - simpl. rewrite <- IHx. f_equal. 
   dilemma. Admitted.
   
   (* rewrite (len_cons_succ x x n). reflexivity.
Qed. *)
              
