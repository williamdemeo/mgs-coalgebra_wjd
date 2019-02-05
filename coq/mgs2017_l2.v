(*
   MIDLANDS GRADUATE SCHOOL 2017
   Coalgebras and Infinite Data Structures
      Venanzio Capretta

   Lecture 2: Bisimulation
*)

Require Import List.
Require Import Arith.
Require Import Wf_nat.

Set Implicit Arguments.

(* STREAMS *)

CoInductive Stream (A:Set): Set :=
  Cons : A -> Stream A -> Stream A.

Definition hd (A:Set): Stream A -> A :=
  fun s => match s with (Cons a _) => a end.

Definition tl (A:Set): Stream A -> Stream A :=
  fun s => match s with (Cons _ s') => s' end.

CoFixpoint str_repeat (A:Set): A -> Stream A :=
  fun a => Cons a (str_repeat a).

CoFixpoint str_from: nat -> Stream nat :=
  fun n => Cons n (str_from (n+1)).

Definition nat_stream : Stream nat :=
  str_from 0.

CoFixpoint str_map (A B:Set): (A->B) -> Stream A -> Stream B :=
fun f s => Cons (f (hd s)) (str_map f (tl s)).

(* This doesn't work because it is not guarded:

CoFixpoint nat: Stream nat :=
  Cons 0 (str_map S nat).
*)

(* Coq doesn't automatically unfold streams. *)
Definition str_unfold (A:Set): Stream A -> Stream A :=
fun s => Cons (hd s) (tl s).

Eval compute in nat_stream.
Eval compute in (str_unfold nat_stream).

Fixpoint str_unfold_n (A:Set)(s:Stream A)(n:nat): Stream A :=
match n with 0 => s | S n' => Cons (hd s) (str_unfold_n (tl s) n') end.

Eval compute in (str_unfold_n nat_stream 10).

Theorem str_unfold_eq:
  forall (A:Set)(s:Stream A), s = str_unfold s.
Proof.
intros A s.
case s.
trivial.
Qed.

CoFixpoint interleave (A:Set):
  Stream A -> Stream A -> Stream A :=
fun s1 s2 => Cons (hd s1) (interleave s2 (tl s1)).

CoFixpoint evens (A:Set): Stream A -> Stream A :=
  fun s => Cons (hd s) (evens (tl (tl s))).

Definition odds (A:Set): Stream A -> Stream A :=
  fun s => evens (tl s).

CoFixpoint zip_with (A B C:Set): 
  (A->B->C) -> Stream A -> Stream B -> Stream C :=
  fun f sa sb => Cons (f (hd sa) (hd sb)) 
                      (zip_with f (tl sa) (tl sb)).

(* This is not guarded:

CoFixpoint fib : Stream nat :=
Cons 0 (zip_with plus (Cons 1 fib) fib).
*)

(* This is guarded *)
CoFixpoint fib_aux : nat -> nat -> Stream nat :=
fun n m => Cons n (fib_aux m (n+m)).

Definition fib : Stream nat :=
fib_aux 0 1.

Eval compute in (str_unfold_n fib 10).

(* The most general way to define a function to
   a coinductive type is by means of a coalgebra.
*)

Definition StrCoalgebra (A:Set)(X:Set) : Set := X -> A*X.

Definition sc_hd (A X:Set)(f:StrCoalgebra A X): X -> A :=
  fun x => fst (f x).

Definition sc_tl (A X:Set)(f:StrCoalgebra A X): X -> X :=
  fun x => snd (f x).

CoFixpoint str_anamorphism (A X :Set)(f:StrCoalgebra A X): 
  X -> Stream A :=
fun x => Cons (sc_hd f x) (str_anamorphism f (sc_tl f x)).

(* Definition of Fibonacci using a coalgebra. *)
Definition fib_str: Stream nat :=
str_anamorphism
  (fun p:nat*nat => let (n,m) := p in (n,(m,n+m)))
  (0,1).

Eval compute in (str_unfold_n fib_str 10).


(* If we start with the rejected definition:
    fib = Cons 0 (zip_with plus (Cons 1 fib) fib)
   we can justify it by defining a coalgebra
     of all expressions in the computation.
*)

Inductive fib_thunk: Set :=
  fibth: fib_thunk
| consth: nat -> fib_thunk -> fib_thunk
| zip_plusth: fib_thunk -> fib_thunk -> fib_thunk.

Fixpoint fib_coalgebra (e:fib_thunk): nat * fib_thunk :=
match e with
  fibth => (0, zip_plusth (consth 1 fibth) fibth)
| consth n e0 => (n, e0)
| zip_plusth e1 e2 => let (n1,e1') := fib_coalgebra e1 in
                      let (n2,e2') := fib_coalgebra e2 in
                        (n1+n2, zip_plusth e1' e2')
end.

Definition fibonacci : Stream nat :=
str_anamorphism fib_coalgebra fibth.

Eval compute in (str_unfold_n fibonacci 10).
Eval compute in (str_unfold_n fib_str 10).

Fixpoint str_take (A:Set)(n:nat)(s:Stream A): list A :=
match n with 0 => nil | S n => hd s :: str_take n (tl s) end.

Eval compute in (str_take 10 fibonacci).
Eval compute in (str_take 10 fib_str).

(* Exercise: Apply the same technique to the psi function *)

(* Unguarded attempt:

CoFixpoint psi (A:Set): Stream A -> Stream A :=
fun s => Cons (hd s) 
              (interleave (evens (psi (odds (tl s)))) 
                          (odds (psi (evens (tl s))))).
*)

(* Try trivially with constructors for interleave, evens and odds
   and show why the one for odds gives problems.
*)

Inductive psi_thunk (A:Set): Set :=
  pt_psi: Stream A -> psi_thunk A
| pt_ieo: psi_thunk A -> psi_thunk A -> psi_thunk A.

Fixpoint psi_coalgebra (A:Set)(e:psi_thunk A): 
  A * (psi_thunk A) :=
match e with
  pt_psi s => (hd s, 
               pt_ieo (pt_psi (odds (tl s))) 
                      (pt_psi (evens (tl s)))
              )
| pt_ieo e1 e2 => let (he1, te1) := psi_coalgebra e1 in
                  let (he2, te2) := psi_coalgebra e2 in
                    (he1, pt_ieo te2 te1)
end.

Definition psi (A:Set) : Stream A -> Stream A :=
fun s => str_anamorphism (psi_coalgebra (A:=A)) (pt_psi s).

Eval compute in (str_take 5 (psi nat_stream)).

(* TREES *)

CoInductive BTree (A:Set) :=
  Bnode : A -> BTree A -> BTree A -> BTree A.

Definition label (A:Set): BTree A -> A :=
fun t => match t with (Bnode a t1 t2) => a end.

Definition left (A:Set): BTree A -> BTree A :=
fun t => match t with (Bnode a t1 t2) => t1 end.

Definition right (A:Set): BTree A -> BTree A :=
fun t => match t with (Bnode a t1 t2) => t2 end.

Definition btree_unfold (A:Set): BTree A -> BTree A :=
fun t => match t with
  Bnode a l r => Bnode a l r
end.

Lemma btree_unfold_eq:
  forall (A:Set)(t:BTree A), t = btree_unfold t.
Proof.
intros A t; case t; auto.
Qed.

CoFixpoint mirror (A:Set): BTree A -> BTree A :=
fun t => Bnode (label t)
               (mirror (right t))
               (mirror (left t)).

(* BISIMULATION *)

(* Bisimilarity *)

CoInductive Bisim (A:Set): Stream A -> Stream A -> Prop :=
  bisim: forall a s1 s2, 
            Bisim s1 s2 -> Bisim (Cons a s1) (Cons a s2).

Lemma bisim_hd:
  forall (A:Set)(s1 s2: Stream A),
    Bisim s1 s2 -> hd s1 = hd s2.
Proof.
intros A s1 s2 H; case H; auto.
Qed.

Lemma bisim_tl:
  forall (A:Set)(s1 s2: Stream A),
    Bisim s1 s2 -> Bisim (tl s1) (tl s2).
Proof.
intros A s1 s2 H; case H; auto.
Qed.

(* Bisimilarity between any two coalgebras *)

CoInductive Coalg_Bisim 
  (A X Y:Set)(f:StrCoalgebra A X)(g:StrCoalgebra A Y):
  X -> Y -> Prop :=
  coalg_bisim: forall x y, (fst (f x)) = (fst (g y)) ->
                 Coalg_Bisim f g (snd (f x)) (snd (g y)) ->
                   Coalg_Bisim f g x y.

(* Examples *)

Theorem evens_odds_eq:
  forall (A:Set)(s:Stream A),
    Bisim s (interleave (evens s) (odds s)).
cofix.
intros A s.
case s.
clear s; intros a s.
rewrite str_unfold_eq.
simpl.
apply bisim.
apply evens_odds_eq.
Qed.

(* Bisimulation for trees *)

CoInductive TBisim (A:Set): BTree A -> BTree A -> Prop :=
  tbisim : forall a l1 l2 r1 r2, TBisim l1 l2 -> TBisim r1 r2 -> TBisim (Bnode a l1 r1) (Bnode a l2 r2).

Theorem mirror_mirror_bisim:
forall (A:Set)(t:BTree A), TBisim t (mirror (mirror t)).
Proof.
cofix.
intros A t; case t; clear t; intros a l r.
rewrite btree_unfold_eq.
simpl.
apply tbisim.
apply mirror_mirror_bisim.
apply mirror_mirror_bisim.
Qed.

(* OTHER COINDUCTIVE PREDICATES AND RELATIONS *)

CoInductive Always (A:Set)(P:A->Prop): Stream A -> Prop :=
  always: forall s, 
            P (hd s) -> Always P (tl s) -> Always P s.

Inductive Eventually (A:Set)(P:A->Prop): Stream A -> Prop :=
  now: forall a s, P a -> Eventually P (Cons a s)
| later: forall a s, 
           Eventually P s -> Eventually P (Cons a s).

Theorem alx (A:Set): forall x:A, Always (fun a => a = x) (str_repeat x).
Proof.
cofix.
intro x.
(* rewrite str_unfold_eq. *)
apply always.
trivial.
apply alx.
Qed.

Theorem ev2: Eventually (fun y => y=2) nat_stream.
Proof.
(*
repeat (rewrite str_unfold_eq; [try (apply now); trivial | apply later]).
*)
rewrite str_unfold_eq.
apply later.
rewrite str_unfold_eq.
simpl.
apply later.
rewrite str_unfold_eq.
simpl.
apply now.
trivial.
Qed.

(*
Theorem evv2: forall s, Eventually (fun y => y=2) s.
Proof.
cofix.
intro s.
rewrite str_unfold_eq.
apply later.
apply evv2.
Qed.
*)



CoInductive StrAlways (A:Set)(P:Stream A -> Prop):
  Stream A -> Prop :=
  str_always: forall a s, 
                P (Cons a s) -> StrAlways P s -> StrAlways P (Cons a s).

Definition InfinitelyOften (A:Set)(P:A->Prop):
  Stream A -> Prop :=
  StrAlways (Eventually P).

Inductive StrEventually (A:Set)(P:Stream A -> Prop):
  Stream A -> Prop :=
  str_now: forall s, P s -> StrEventually P s
| str_later: forall s, StrEventually P (tl s) -> StrEventually P s.

Definition InfOft (A:Set)(P:Stream A->Prop): 
  Stream A -> Prop :=
  StrAlways (StrEventually P).

Definition incr : Stream nat -> Prop :=
  fun s => (hd s) <= (hd (tl s)).

Lemma eventually_incr: forall s, StrEventually incr s.
Proof.
cut (forall n s, StrEventually incr (Cons n s)).
intros H s; case s; apply H.
intro n.
apply gt_wf_ind with 
  (P := fun n => forall s, StrEventually incr (Cons n s)).
clear n; intros n Hn s.
case (le_gt_dec n (hd s)).
intro Hle; apply str_now.
exact Hle.
intro Hgt; apply str_later.
simpl.
rewrite (str_unfold_eq s).
apply Hn.
exact Hgt.
Qed.

Theorem inf_oft_incr: forall s, InfOft incr s.
Proof.
cofix.
intro s.
rewrite (str_unfold_eq s).
apply str_always.
apply eventually_incr.
apply inf_oft_incr.
Qed.
