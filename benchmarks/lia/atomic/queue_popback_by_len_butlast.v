From Dilemma Require Import Dilemma.
From QuickChick Require Import QuickChick.

Require Import Bool.
Require Import Arith.
Require Import Nat.

Inductive lst : Type :=
  | Nil : lst
  | Cons : nat -> lst -> lst.

Inductive queue : Type :=
| Queue : lst -> lst -> queue.

Open Scope string.

(* ************************** [ LST ] *************************** *)
Instance show_lst : Show lst := 
{| show := 
    let fix aux l :=
      match l with
      | Nil => "Nil"
      | Cons x y => "Cons (" ++ show x ++ ") (" ++ aux y ++ ")"
      end
    in aux
|}.

Derive Arbitrary for lst.
Instance Dec_Eq_lst : Dec_Eq lst.
Proof. dec_eq. Qed.

(* ************************** [ QUEUE ] *************************** *)
Instance show_queue : Show queue := 
{| show := 
    let fix aux l :=
      match l with
      | Queue x y => "Queue (" ++ show x ++ ") (" ++ show y ++ ")"
      end
    in aux
|}.

Derive Arbitrary for queue.
Instance Dec_Eq_queue : Dec_Eq queue.
Proof. dec_eq. Qed.

(* ************************** [ OPTION ] *************************** *)
Instance show_option {T} `{_ : Show T} : Show (option T) := 
{| show := 
    let fix aux l :=
      match l with
      | None => "None"
      | Some x => "Some (" ++ show x ++ ")"
      end
    in aux
|}.

Close Scope string.

Scheme Equality for lst.

Fixpoint len (len_arg0 : lst) : nat
           := match len_arg0 with
              | Nil => 0
              | Cons x y => plus 1 (len y)
              end.

Definition qlen (qlen_arg0 : queue) : nat
           := let 'Queue x y := qlen_arg0 in
              plus (len x) (len y).

Fixpoint append (append_arg0 : lst) (append_arg1 : lst) : lst
           := match append_arg0, append_arg1 with
              | Nil, x => x
              | Cons x y, z => Cons x (append y z)
              end.

Fixpoint butlast (butlast_arg0 : lst) : lst
           := match butlast_arg0 with
              | Nil => Nil
              | Cons n x => if lst_beq x Nil then Nil else Cons n (butlast x)
              end.

Definition qpopback (qpopback_arg0 : queue) : queue
           := match qpopback_arg0 with
              | Queue x (Cons n y) => Queue x y
              | Queue x Nil => Queue (butlast x) Nil
              end.

Definition isAmortized (isAmortized_arg0 : queue) : bool
           := let 'Queue x y := isAmortized_arg0 in
              leb (len y) (len x).

Definition isEmpty (isEmpty_arg0 : queue) : bool
           := let 'Queue x y := isEmpty_arg0 in
              andb (lst_beq x Nil) (lst_beq y Nil).

Lemma len_butlast : forall (l : lst) (n : nat), S (len (butlast (Cons n l))) = len (Cons n l).
Proof.
  intros.
  generalize dependent n.
  induction l.
  - reflexivity.
  - intros. simpl. simpl in IHl. rewrite IHl. reflexivity.
Qed.

Theorem theorem0 : forall (q : queue) (n : nat), isAmortized q && negb (isEmpty q) = true -> eq (plus 1 (qlen (qpopback q))) (qlen q).
Proof.
  intros.
  destruct q.
  destruct l0.
  - simpl. rewrite <- plus_n_O. destruct l.
    + simpl in H. discriminate.
    + dilemma. Admitted.
    
    (* rewrite len_butlast. apply plus_n_O.
  - simpl. apply plus_n_Sm.
Qed. *)
