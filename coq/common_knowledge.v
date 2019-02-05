(* THE COINDUCTIVE FORMULATION OF COMMON KNOWLEDGE *)
(*   by Colm Baston and Venanzio Capretta          *)

Require Import Relations.
Require Import Classical.

(* States, Events, and Notation *)

Parameter State : Set.

Definition Event := State -> Prop.

Notation "e1 '//\\' e2" := (fun w => e1 w /\ e2 w) (at level 15).
Notation "e1 '==>' e2" := (forall w:State, e1 w -> e2 w) (at level 20).
Notation "e1 '-->' e2" := (fun w =>  e1 w -> e2 w) (at level 15, right associativity).
Notation "¬ e"         := (fun w => ~ e w)         (at level 10).

Definition All (e:Event): Prop := forall w, e w.

Lemma Impl_All:
  forall e1 e2:Event, (e1 ==> e2) = All (e1 --> e2).
Proof.
auto.
Qed.

Definition mapE (K:Event->Event)(E:nat->Event): nat -> Event :=
  fun n => K (E n).

Definition InfImpl (E:nat->Event)(e:Event): Prop :=
  forall w, (forall n, E n w) -> e w.

Definition FamImpl {X:Type}(E:X->Event)(e:Event): Prop :=
  forall w, (forall x:X, E x w) -> e w.

Definition mapFam (K:Event->Event){X:Type}(E:X->Event): X->Event :=
  fun x => K (E x).

Definition KFam (K:Event->Event)(w:State): {e:Event | K e w} -> Event :=
  fun ek => K (proj1_sig ek).


Lemma eImplTrans: forall e1 e2 e3: Event, e1 ==> e2 -> e2 ==> e3 -> e1 ==> e3.
Proof.
intros e1 e2 e3 H12 H23 w.
intro H1; apply H23; apply H12; apply H1.
Qed.

Lemma InfImplTrans: forall E (e1 e2:Event), InfImpl E e1 -> e1 ==> e2 -> InfImpl E e2.
Proof.
intros E e1 e2 HE1 H12.
intros w HE.
apply H12.
apply HE1.
exact HE.
Qed.

(* Definition of preservation of semantic implication. *)

Definition SemImpl (K:Event->Event): Prop :=
  forall (X:Type)(E: X->Event)(e:Event), 
         FamImpl E e -> FamImpl (mapFam K E) (K e).

(* Knowledge Operators *)

Record KOp (K : Event -> Event) : Prop :=
 { (* System K Axioms *)
   axiomN : forall (e : Event), All e ->  All (K e) ;
   axiomK : forall (e1 e2 : Event), K (e1 --> e2) ==> K e1 --> K e2           ;

   (* System KT45 (S5) Axioms *)
   axiomT : forall (e : Event), K e ==> e               ;
   axiom4 : forall (e : Event), K e ==> K (K e)         ;
   axiom5 : forall (e : Event), ¬ (K e) ==> K (¬ (K e)) ;

   (* Infinitary deduction *)
   axiomInf: SemImpl K
}.

(* axiomN follows from axiomInf, using the empty family *)

Definition emptyFam: Empty_set -> Event :=
  fun x => match x with end.

Lemma all_emptyFam: forall e, All e -> FamImpl emptyFam e.
Proof.
intros e He.
intros w _.
apply He.
Qed.

Lemma emptyFam_all:
  forall e, FamImpl emptyFam e -> All e.
Proof.
intros e He.
intro w.
apply He.
intro x.
case x.
Qed.

Lemma inf_N (K : Event -> Event):
  SemImpl K -> forall (e : Event), All e ->  All (K e).
Proof.
intros KInf e He.
intro w.
apply KInf with (E:=emptyFam)(e:=e). 
apply all_emptyFam.
exact He.
intro x; case x.
Qed.

(* Similarly, axiomK follows from axiomInf using a family with two members:
   A "modus ponens" family.*)

Definition mpFam (e1 e2:Event): bool -> Event :=
  fun b => if b then e1 --> e2 else e1.

Lemma mpFam_K (K:Event -> Event):
  SemImpl K -> forall (e1 e2:Event), FamImpl (mapFam K (mpFam e1 e2)) (K e2).
Proof.
intros KInf e1 e2.
apply KInf.
intro w.
intro Hmp.
apply (Hmp true).
exact (Hmp false).
Qed.

Lemma inf_K (K : Event -> Event):
  SemImpl K -> forall (e1 e2 : Event), K (e1 --> e2) ==> K e1 --> K e2.
Proof.
intros KInf e1 e2.
intros w; simpl. 
intros H12 H1.
apply mpFam_K with (e1 := e1).
exact KInf.
intro b; case b; simpl; assumption.
Qed.

Lemma natK: forall K, KOp K ->
  forall (E: nat->Event)(e:Event), InfImpl E e -> InfImpl (mapE K E) (K e).
Proof.
intros K HK; apply (axiomInf K HK).
Qed.

Lemma K_impl: forall K, KOp K ->
  forall e1 e2: Event, e1 ==> e2 -> K e1 ==> K e2.
Proof.
intros K HK e1 e2 H12.
rewrite Impl_All in H12.
intros w K1w.
apply axiomK with (e1:=e1).
exact HK.
apply axiomN.
exact HK.
exact H12.
exact K1w.
Qed.

Lemma ne_nke: forall K, KOp K ->
  forall e:Event, ¬ e ==> K (¬ (K e)).
Proof.
intros K HK e.
intros w Hnew.
apply axiom5.
exact HK.
intro Kew.
apply Hnew.
apply axiomT with (K:=K).
exact HK.
exact Kew.
Qed.

(* COINDUCTIVE DEFINITION OF COMMON KNOWLEDGE *)

Parameter Agent: Set.
Parameter an_agent : Agent.

Section CoinductiveCK.

Variable K: Agent -> Event -> Event.
Hypothesis KKOp: forall a, KOp (K a).

Lemma K_Impl: forall (e1 e2:Event)(i:Agent), e1 ==> e2 -> K i e1 ==> K i e2.
Proof.
intros e1 e2 i H w H1.
apply (axiomK (K i) (KKOp i) e1).
apply (axiomN (K i) (KKOp i)).
exact H.
exact H1.
Qed.

(* Everybody Knows *)

Definition  EK (e:Event) : Event :=
 fun w => forall i, K i e w.

(* Common Knowledge *)
(* Coinductive Definition *)

CoInductive cCK : Event -> Event :=
  ck_intro e : EK e //\\ cCK (EK e) ==> cCK e.

Lemma cCK_EK : forall e, cCK e ==> EK e.
Proof.
 intros _ _ [e w [x _]]; exact x.
Qed.

Lemma cCK_cCKEK : forall e, cCK e ==> cCK (EK e).
Proof.
 intros _ _ [e w [_ y]]; exact y.
Qed.

(* knowledge operator properties of EK *)

Lemma EK_axiomInf: SemImpl EK.
Proof.
red.
intros X E e HEe.
intros w HEKE.
intro a.
apply axiomInf with (K := K a)(E:=E)(e:=e).
apply KKOp.
exact HEe.
intro x; apply HEKE.
Qed.

Lemma EK_axiomN : forall e : Event, All e  -> All (EK e).
  intros e f v i.
  apply (axiomN (K i) (KKOp i)).
  apply f.
Qed.

Lemma EK_axiomK : forall e1 e2 : Event, EK (e1 --> e2) ==> EK e1 --> EK e2.
  intros e1 e2; simpl.
  intros w ek12 ek1; red. 
  intro i.
  apply (axiomK (K i) (KKOp i)) with (e1 := e1).
  apply ek12.
  apply ek1.
Qed.

Lemma EK_axiomT : forall e : Event, EK e ==> e.
  intros e w ek.
  apply (axiomT (K an_agent) (KKOp an_agent)).
  apply ek.
Qed.

Lemma EK_Impl: forall e1 e2:Event, e1 ==> e2 -> EK e1 ==> EK e2.
Proof.
intros e1 e2 H w; simpl.
intros H1 i.
apply K_Impl with (e1 := e1).
exact H.
apply H1.
Qed.

(* EK_axiom4 doesn't hold - if it did, (EK e) would imply (EK (EK e)), and applying this ad infinitum would imply (cCK e) *)

Theorem EK_cCK: 
  forall e:Event, e ==> EK e -> e ==> cCK e.
Proof.
cofix.
intros e He.
intros w Hew.
apply ck_intro; split.

apply He.
exact Hew.

apply EK_cCK.
apply EK_Impl.
exact He.
apply He; exact Hew.
Qed.

Lemma nKnEK:
  forall (e:Event)(a:Agent), ¬ (K a e) ==> ¬ (EK e).
Proof.
intros e a w Hae.
simpl; intro EKe. 
apply Hae; apply EKe.
Qed.

Lemma KnKnEK:
  forall (e:Event)(a:Agent), K a (¬ (K a e)) ==> K a (¬ (EK e)).
Proof.
intros e a.
apply K_Impl with (1:= (nKnEK e a)).
Qed.

Lemma ne_eknek:
  forall e:Event, ¬ e ==> EK (¬ (EK e)).
Proof.
intros e.
intros w Hne.
intro a.
apply KnKnEK.
apply ne_nke.
apply KKOp.
exact Hne.
Qed.

(* cCK equivalent of recursive EK *)

Fixpoint recEK (e:Event)(n:nat): Event :=
  match n with
    0 => EK e
  | (S n) => EK (recEK e n)
  end.

Lemma recEK_EK: forall (e:Event)(n:nat), recEK (EK e) n = EK (recEK e n).
Proof.
induction n; auto.
simpl.
rewrite IHn; auto.
Qed.

Lemma cCK_recEK: forall n e, cCK e ==> recEK e n.
Proof.
induction n.
apply cCK_EK.
intro e.
apply eImplTrans with (e2 := cCK (EK e)).
apply cCK_cCKEK.
apply eImplTrans with (e2 := recEK (EK e) n).
apply IHn.
simpl.
rewrite recEK_EK.
auto.
Qed.

Lemma recEK_cCK: forall e, InfImpl (recEK e) (cCK e).
Proof.
cofix.
intros e w HEK.
apply ck_intro.
split.
apply (HEK 0).
apply recEK_cCK.
intro n.
rewrite recEK_EK.
apply (HEK (S n)).
Qed.

Lemma allEK_cCK:
  forall e w, (forall n, recEK e n w) -> cCK e w.
Proof.
apply recEK_cCK.
Qed. 

(* knowledge operator properties of cCK *)

Lemma EKcCK_cCKEK : forall e, EK (cCK e) ==> cCK (EK e).
Proof.
  intros e w ekck.
  apply cCK_cCKEK.
  apply EK_axiomT.
  assumption.
Qed.

Lemma cCKEK_EKcCK : forall e, cCK (EK e) ==> EK (cCK e).
Proof.
intros e w H i.
apply (natK (K i) (KKOp i) (recEK e)).
apply recEK_cCK.
intro n.
red.
cut (EK (recEK e n) w).
auto.
rewrite <- (recEK_EK e n).
apply cCK_recEK.
exact H.
Qed.

Lemma cCK_EKcCK: forall e, cCK e ==> EK (cCK e).
Proof.
intro e; apply eImplTrans with (e2 := cCK (EK e)).
apply cCK_cCKEK.
apply cCKEK_EKcCK.
Qed.

Lemma EKrecEK: forall (e1 e2:Event) n, e1 ==> EK e2 -> recEK e1 n ==> recEK e2 (S n).
Proof.
induction n.
intro H; simpl.
apply EK_Impl.
exact H.
simpl.
intro H.
apply EK_Impl.
apply IHn.
exact H.
Qed.

Lemma cCK_recEKcCK: forall n e, cCK e ==> recEK (cCK e) n.
Proof.
induction n; simpl.
intro e; apply eImplTrans with (e2 := cCK (EK e)).
apply cCK_cCKEK.
apply cCKEK_EKcCK.

intro e; apply eImplTrans with (e2 := EK (cCK e)).
apply cCK_EKcCK.
apply EK_Impl.
apply IHn.
Qed.


Lemma cCK_axiomInf: SemImpl cCK.
Proof.
red.
cofix.
intros X E e HEe.
intro w.
intro HcKE.
apply ck_intro; split.

apply (EK_axiomInf X E).
exact HEe.
intro x; red.
apply cCK_EK.
apply HcKE.

apply cCK_axiomInf with (E := fun x => (EK (E x))).
apply (EK_axiomInf X E).
exact HEe.
intro x; red.
apply cCK_cCKEK.
apply HcKE.
Qed.

Lemma cCK_axiom4 : forall e : Event, cCK e ==> cCK (cCK e).
Proof.
intros e w H.
apply recEK_cCK.
intro n; apply cCK_recEKcCK.
exact H.
Qed.

Lemma cCK_axiomN : forall e : Event, All e -> All (cCK e).
Proof.
  cofix coIH.
  intros e f v.
  apply ck_intro.
  split.
  apply EK_axiomN.
  apply f.
  apply coIH.
  apply EK_axiomN.
  apply f.
Qed.

Lemma cCK_axiomT : forall e : Event, cCK e ==> e.
  intros e w cck.
  destruct cck as [e w [ek cck]].
  apply EK_axiomT.
  apply EK_axiomT.
  apply cCK_EK.
  assumption.
Qed.

Lemma cCK_axiomK : 
  forall e1 e2 : Event, cCK (e1 --> e2) ==> cCK e1 --> cCK e2.
Proof.
exact (inf_K cCK cCK_axiomInf).
Qed.

Lemma nCK_EK:
  forall e, ¬(cCK e) ==> EK (¬(cCK e)).
Proof.
intros e w nHe.
cut (~ forall n, recEK e n w).
intros HnEK.
apply not_all_ex_not in HnEK.
case HnEK.
intros n Hne.
apply EK_Impl with (e1 := ¬ (recEK e (S n))).
intros v HSn Hck.
apply HSn.
apply cCK_recEK.
exact Hck.
simpl.
apply ne_eknek.
exact Hne.
intro  Hall.
apply nHe.
apply recEK_cCK.
exact Hall.
Qed.

Lemma cCK_axiom5 : forall e : Event, ¬ (cCK e) ==> cCK (¬ (cCK e)).
Proof.
intro e.
apply EK_cCK.
apply nCK_EK.
Qed.

Theorem cCK_KOp: KOp cCK.
Proof.
split.
apply cCK_axiomN.
apply cCK_axiomK.
apply cCK_axiomT.
apply cCK_axiom4.
apply cCK_axiom5.
apply cCK_axiomInf.
Qed.

End CoinductiveCK.

(* Equivalence Relations *)

Definition Rel (A : Set) := A -> A -> Prop.

Record EqRel {A : Set} (R : Rel A) : Prop :=
 { eq_refl  : forall (x : A), R x x                       ;
   eq_symm  : forall (x y : A), R x y -> R y x            ;
   eq_trans : forall (x y z : A), R x y -> R y z -> R x z }.


(* Transformations Between Relations and K Operators *)

Definition Rel_to_K (R : Rel State) (e : Event) : Event :=
 fun w => forall v, R w v -> e v.

Definition K_to_Rel (K : Event -> Event) : Rel State :=
 fun w v => forall e, K e w -> K e v.

(* Proof that Rel_to_K on an equivalence relation yields a K satisfying S5 *)

Lemma axiomN' : forall (R : Rel State), EqRel R -> forall (e : Event), (forall (v : State), e v) -> forall (w : State), (Rel_to_K R) e w.
Proof.
 intros R _ e f w v Rwv.
 apply f.
Qed.

Lemma axiomK' : forall (R : Rel State), EqRel R -> forall (e1 e2 : Event), (Rel_to_K R) (e1 --> e2) ==> (Rel_to_K R) e1 --> (Rel_to_K R) e2.
Proof.
 intros R _ e1 e2 w ke1e2w. simpl; intros ke1w v Rwv.
 apply ke1e2w.
 assumption.
 apply ke1w.
 assumption.
Qed.

Lemma axiomT' : forall (R : Rel State), EqRel R -> forall (e : Event), (Rel_to_K R) e ==> e.
Proof.
 intros R eqH e w kew.
 apply kew.
 apply eq_refl.
 assumption.
Qed.

Lemma axiom4' : forall (R : Rel State), EqRel R -> forall (e : Event), (Rel_to_K R) e ==> (Rel_to_K R) ((Rel_to_K R) e).
Proof.
 intros R eqH e w kew v Rwv u Rvu.
 apply kew.
 apply eq_trans with (y := v).
 assumption.
 assumption.
 assumption.
Qed.

Lemma axiom5' : forall (R : Rel State), EqRel R -> forall (e : Event), ¬ ((Rel_to_K R) e) ==> (Rel_to_K R) (¬ ((Rel_to_K R) e)).
Proof.
 intros R eqH e w nknew v Rwv knev.
 apply nknew.
 intros u Rwu.
 apply (knev u).
 apply eq_symm.
 assumption.
 apply eq_trans with (y := w).
 assumption.
 apply eq_symm.
 assumption.
 assumption.
 assumption.
Qed.

Lemma axiomInf':
  forall (R : Rel State), EqRel R -> 
    SemImpl (Rel_to_K R).
Proof.
intros R ewR X E e Hinf.
intros w Hx.
red in Hx.
intros v Rwv.
apply Hinf.
intro x.
apply Hx.
exact Rwv.
Qed.

Theorem KOp_Rel_to_K : forall (R : Rel State), EqRel R -> KOp (Rel_to_K R).
Proof.
 intros R eqH.
 split.
 exact (axiomN' R eqH).
 exact (axiomK' R eqH).
 exact (axiomT' R eqH).
 exact (axiom4' R eqH).
 exact (axiom5' R eqH).
 exact (axiomInf' R eqH).
Qed.

(* Proof that K_to_Rel on a K satisfying S5 yields an equivalence relation *)

Lemma eq_refl' : forall (K : Event -> Event), KOp K -> forall (w : State), (K_to_Rel K) w w.
Proof.
 intros K HK w e kew.
 assumption.
Qed.

Lemma eq_symm' : forall (K : Event -> Event),
  KOp K -> forall (w v : State), (K_to_Rel K) w v -> (K_to_Rel K) v w.
Proof.
 intros K kH w v f e Kev.
 apply NNPP.
 intro nkew.
 apply axiom5 in nkew.
 apply f in nkew.
 apply axiomT with (e:= ¬(K e))(w:=v) in nkew.
 apply nkew.
 assumption.
 assumption.
 assumption.
Qed.

Lemma eq_trans' : forall (K : Event -> Event), KOp K -> forall (w v u : State), (K_to_Rel K) w v -> (K_to_Rel K) v u -> (K_to_Rel K) w u.
Proof.
 intros K _ w v u Rwv Rvu e kew.
 apply Rvu.
 apply Rwv.
 assumption.
Qed.

Theorem EqRel_K_to_Rel : forall (K : Event -> Event), KOp K -> EqRel (K_to_Rel K).
Proof.
 intros K kH.
 split.
 exact (eq_refl'  K kH).
 exact (eq_symm'  K kH).
 exact (eq_trans' K kH).
Qed.

(* The two transformations are an isomorphism *)

Theorem EqRel_K_Iso1:
  forall K:Event->Event,
    KOp K ->  
    forall e, K e ==> Rel_to_K (K_to_Rel K) e.
Proof.
intros K HK e w Kew v Rvw.
red in Rvw.
apply (axiomT K HK).
apply Rvw.
exact Kew.
Qed.

Lemma K_Rel_Fam:
  forall K, forall e w, Rel_to_K (K_to_Rel K) e w -> FamImpl (KFam K w) e.
Proof.
intros K e w Hew.
red in Hew.
red.
intros v Hv.
apply Hew.
red.
intros e' He'.
apply (Hv (exist (fun e' => K e' w) e' He')).
Qed.

Lemma Fam_K_Rel:
  forall K,forall e w, FamImpl (KFam K w) e -> Rel_to_K (K_to_Rel K) e w.
Proof.
intros K e w Hew.
red in Hew.
red.
intros v Rwv.
red in Rwv.
apply Hew.
intros [e' He'].
red; simpl.
apply Rwv.
exact He'.
Qed.

Theorem EqRel_K_Iso2:
  forall K, KOp K ->
  forall e, Rel_to_K (K_to_Rel K) e ==> K e.
Proof.
intros K HK e w Hew.
apply K_Rel_Fam in Hew.
apply (axiomInf K HK) in Hew.
apply Hew.
intros [e' He'].
red.
unfold KFam; simpl.
apply (axiom4 K HK).
exact He'.
Qed.

Theorem K_EqRel_Iso1:
  forall (R : Rel State), EqRel R -> forall w v, R w v -> K_to_Rel (Rel_to_K R) w v.
Proof.
intros R eqR w v Rwv.
red.
intros e He.
red.
red in He.
intros u Rvu.
apply He.
apply eq_trans with (y:= v).
exact eqR.
exact Rwv.
exact Rvu.
Qed.

Theorem K_EqRel_Iso2:
  forall (R : Rel State), EqRel R -> forall w v, K_to_Rel (Rel_to_K R) w v -> R w v.
Proof.
intros R eqR w v H.
red in H.
apply (H (R w)).
red.
auto.
apply eq_refl.
exact eqR.
Qed.

(* RELATIONAL DEFINITION OF COMMON KNOWLEDGE *)

Section RelationalCK.

Variable KR : Agent -> Rel State.
Hypothesis kr_equivalence : forall a, EqRel (KR a).

Lemma kr_refl  : forall i, reflexive State (KR i).
Proof.
intro i; red.
apply (eq_refl (KR i) (kr_equivalence i)).
Qed.

Lemma kr_symm  : forall i, symmetric  State (KR i).
Proof.
intro i; red.
apply (eq_symm (KR i) (kr_equivalence i)).
Qed.


Lemma kr_trans : forall i, transitive State (KR i).
Proof.
intro i; red.
apply (eq_trans (KR i) (kr_equivalence i)).
Qed.

Let K (i:Agent): Event -> Event :=
  Rel_to_K (KR i).

Theorem Ke_e : forall i e w, K i e w -> e w.
Proof.
 intros i e w k.
 apply (k w).
 apply kr_refl.
Qed.

Theorem Ke_KKe : forall i e w, K i e w -> K i (K i e) w.
Proof.
 intros i e w k v kr1 u kr2.
 apply k.
 apply (kr_trans i w v u kr1 kr2).
Qed.

Let  EKR : Event -> Event := EK K.

Let cCKR : Event -> Event := cCK K.

Lemma cCKR_EKR: forall e w, cCKR e w -> EKR e w.
Proof.
apply cCK_EK.
Qed.

Lemma cCKKR_EKRcCKKR: forall e w, cCKR e w -> EKR (cCKR e) w.
Proof.
apply cCK_EKcCK.
intro a; apply KOp_Rel_to_K.
apply kr_equivalence.
Qed.

Inductive CKR : relation State :=
 | ckr_base  : forall i w v, KR i w v -> CKR w v
 | ckr_trans : forall w v u, CKR w v -> CKR v u -> CKR w u.

Theorem ckr_refl : reflexive State CKR.
Proof.
 intro w.
 apply (ckr_base an_agent).
 apply kr_refl.
Qed.

Theorem ckr_symm : symmetric State CKR.
Proof.
 intros w v ckr.
 induction ckr.
 apply kr_symm in H.
 apply (ckr_base i).
 exact H.
 apply (ckr_trans u v w IHckr2 IHckr1).
Qed.

Theorem ckr_eqrel: EqRel CKR.
Proof.
split.
apply ckr_refl.
apply ckr_symm.
apply ckr_trans.
Qed.

Let CK: Event -> Event := Rel_to_K CKR.

Lemma CK_EKR : forall e w, CK e w -> EKR e w.
Proof.
 intros e w ck i v kr.
 apply ck.
 apply (ckr_base i).
 exact kr.
Qed.

Lemma CK_EKRCK : forall e w, CK e w -> EKR (CK e) w.
Proof.
 intros e w ck' i v kr u ckr.
 apply ck'.
 apply (ckr_trans w v u).
 apply (ckr_base i).
 apply kr.
 apply ckr.
Qed.

Lemma CK_CKEKR : forall e w, CK e w -> CK (EKR e) w.
Proof.
intros e w Hew.
compute in Hew.
red.
red.
intros v Rwv i u Rivu.
apply Hew.
apply ckr_trans with (v:=v).
exact Rwv.
apply ckr_base with (i:=i).
exact Rivu.
Qed.

Theorem CK_cCKR : forall e w, CK e w -> cCKR e w.
Proof.
 cofix coIH.
 intros e w ck'.
 apply ck_intro.
 split.
 apply CK_EKR.
 exact ck'.
 apply coIH.
 apply CK_CKEKR.
 exact ck'.
Qed.

Lemma ck_transport : forall e w v, cCKR e w -> CKR w v -> cCKR e v.
Proof.
 intros e w v cckew.
 induction 1.

 apply (Ke_e i).
 apply (Ke_KKe i (cCKR e) w).
 apply (cCKKR_EKRcCKKR e w).

 exact cckew.
 exact H.

 apply IHCKR2.
 apply IHCKR1.
 exact cckew.
Qed.

Theorem cCKR_CK: forall e w, cCKR e w -> CK e w.
Proof.
 intros e w ckew v ckr.
 induction ckr.
 generalize i v H.
 apply (cCKR_EKR e w ckew).
 apply IHckr2.
 apply (ck_transport e w v).
 apply ckew.
 apply ckr1.
Qed.

End RelationalCK.

