Require Import HOLLight_Real_With_N.mappings HOLLight.mappings.
Require Import Coq.NArith.BinNat.

Set Bullet Behavior "Strict Subproofs".

(*****************************************************************************)
(* Miscelaneous, set theory *)
(*****************************************************************************)
Require Import Classical_sets.

Arguments Union {U}.
Arguments Setminus {U}.
Arguments Subtract {U}.
Arguments Strict_Included {U}.
Arguments Disjoint {U}.
Arguments Singleton {U}.
Arguments Add {U}.

(* Eliminating useless GSPEC and SETSPEC combination *)
Lemma SPEC_elim {A : Type'} {x : A} {P} : (GSPEC (fun x => exists x', SETSPEC x (P x') x') x) = P x.
Proof.
  apply prop_ext ; intro H. destruct H as (x', (HP , e)). now subst x.
  now exists x.
Qed.

Lemma o_def {A B C : Type'} : Basics.compose = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Proof. reflexivity. Qed.

Lemma I_def {A : Type'} : id = (fun x : A => x).
Proof. reflexivity. Qed.

Lemma let_clear {A B} : forall (f : A -> B) x, Basics.apply f x = (let y := x in f y).
Proof. reflexivity. Qed.

Ltac let_clear := repeat rewrite let_clear.

Lemma LET_def {A B : Type'} : Basics.apply = (fun f : A -> B => fun x : A => f x).
Proof. ext f x. reflexivity. Qed.

Lemma LET_END_def {A : Type'} : id = (fun t : A => t).
Proof. reflexivity. Qed.

Lemma UNION_def {A : Type'} : Union = (fun _32385 : A -> Prop => fun _32386 : A -> Prop => @GSPEC A (fun GEN_PVAR_0 : A => exists x : A, @SETSPEC A GEN_PVAR_0 ((@IN A x _32385) \/ (@IN A x _32386)) x)).
Proof.
  ext B C x. rewrite SPEC_elim. apply prop_ext;inversion 1;auto.
  now apply Union_introl. now apply Union_intror.
Qed.

Definition INTERS {A : Type'} : Ensemble (Ensemble A) -> Ensemble A := fun E x => forall y, In E y -> In y x.
Lemma INTERS_def {A : Type'} : INTERS = (fun _32414 : (A -> Prop) -> Prop => @GSPEC A (fun GEN_PVAR_3 : A => exists x : A, @SETSPEC A GEN_PVAR_3 (forall u : A -> Prop, (@IN (A -> Prop) u _32414) -> @IN A x u) x)).
Proof.
  ext E x. symmetry. exact SPEC_elim.
Qed.

Lemma DIFF_def {A : Type'} : Setminus = (fun _32419 : A -> Prop => fun _32420 : A -> Prop => @GSPEC A (fun GEN_PVAR_4 : A => exists x : A, @SETSPEC A GEN_PVAR_4 ((@IN A x _32419) /\ (~ (@IN A x _32420))) x)).
Proof.
  ext B C x. symmetry. exact SPEC_elim.
Qed.

Lemma DELETE_def {A : Type'} : Subtract = (fun _32431 : A -> Prop => fun _32432 : A => @GSPEC A (fun GEN_PVAR_6 : A => exists y : A, @SETSPEC A GEN_PVAR_6 ((@IN A y _32431) /\ (~ (y = _32432))) y)).
Proof.
  ext E x0 x. rewrite SPEC_elim. apply prop_ext;intros (H1,H2).
  - split. exact H1.
    intro H. apply H2. rewrite H. apply In_singleton.
  - split. assumption.
    inversion 1. rewrite sym in H0. destruct (H2 H0).
Qed.

Lemma PSUBSET_def {A : Type'} : Strict_Included = (fun _32455 : A -> Prop => fun _32456 : A -> Prop => (@Ensembles.Included A _32455 _32456) /\ (~ (_32455 = _32456))).
Proof. reflexivity. Qed.

Lemma DISJOINT_def {A : Type'} : Disjoint = (fun _32467 : A -> Prop => fun _32468 : A -> Prop => (@Ensembles.Intersection A _32467 _32468) = (@Ensembles.Empty_set A)).
Proof.
  ext B C. apply prop_ext;intro H.
  - destruct H. ext x. specialize (H x). rewrite <- is_False in H. now rewrite EMPTY_def.
  - apply Disjoint_intro. intro x. rewrite H. destruct 1.
Qed.

Definition is_Singleton {A : Type} (E : Ensemble A) := exists x, E=Singleton x.

Lemma Singleton_from_Empty {A : Type} (x : A) : Singleton x = Add Empty_set x.
Proof.
  ext y. apply prop_ext;intro H;destruct H. right. apply In_singleton.
  destruct H. exact H.
Qed.

Lemma SING_def {A : Type'} : is_Singleton = (fun _32479 : A -> Prop => exists x : A, _32479 = (@INSERT A x (@Ensembles.Empty_set A))).
Proof.
  ext E. apply prop_ext ; intros (x , H) ; exists x ;
  rewrite H ; now rewrite Singleton_from_Empty.
Qed.

Definition IMAGE {A B : Type'} (f : A -> B) (E : Ensemble A) : Ensemble B :=
  fun y => exists x, In E x /\ y = f x.

Lemma IMAGE_def {A B : Type'} : (@IMAGE A B) = (fun _32493 : A -> B => fun _32494 : A -> Prop => @GSPEC B (fun GEN_PVAR_7 : B => exists y : B, @SETSPEC B GEN_PVAR_7 (exists x : A, (@IN A x _32494) /\ (y = (_32493 x))) y)).
Proof.
  ext f E y. symmetry. exact SPEC_elim.
Qed.

Fixpoint list_Union {A : Type'} (l : list (A -> Prop)) : A -> Prop :=
  match l with
  | nil => Empty_set
  | cons E l => Union E (list_Union l) end.

Lemma LIST_UNION_def {_184792 : Type'} : list_Union = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> (list (_184792 -> Prop)) -> _184792 -> Prop) (fun LIST_UNION' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> (list (_184792 -> Prop)) -> _184792 -> Prop => forall _204636 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))), ((LIST_UNION' _204636 (@nil (_184792 -> Prop))) = (@Ensembles.Empty_set _184792)) /\ (forall h : _184792 -> Prop, forall t : list (_184792 -> Prop), (LIST_UNION' _204636 (@cons (_184792 -> Prop) h t)) = (@Ensembles.Union _184792 h (LIST_UNION' _204636 t)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))))))).
Proof.
  total_align.
Qed.

(*****************************************************************************)
(* Multisets *)
(*****************************************************************************)

(* Did not manage to map to coq multisets : recquires boolean decidable equality *)

Definition Multiset (A : Type') := arr A N.

Definition multiset {A : Type'} : (A -> N) -> Multiset A := id.
Definition multiplicity {A : Type'} : Multiset A -> A -> N := id.

Definition mempty {A : Type'} : Multiset A := fun _ => 0.
Lemma mempty_def {_183533 : Type'} : mempty = (@multiset _183533 (fun b : _183533 => NUMERAL N0)).
Proof. reflexivity. Qed.

Definition mmember {A : Type'} (a : A) (m : Multiset A) := m a <> 0.
Lemma mmember_def {_183543 : Type'} : mmember = (fun _203992 : _183543 => fun _203993 : Multiset _183543 => ~ ((@multiplicity _183543 _203993 _203992) = (NUMERAL N0))).
Proof. reflexivity. Qed.

Definition msing {A : Type'} : A -> Multiset A := fun a a' => COND (a'=a) 1 0.

Lemma msing_def {_183559 : Type'} : msing = (fun _204004 : _183559 => @multiset _183559 (fun b : _183559 => @COND N (b = _204004) (NUMERAL (BIT1 N0)) (NUMERAL N0))).
Proof. reflexivity. Qed.

Definition munion {A : Type'} := fun (m m' : Multiset A) a => m a + (m' a). 

Lemma munion_def {_183578 : Type'} : (@munion _183578) = (fun _204009 : Multiset _183578 => fun _204010 : Multiset _183578 => @multiset _183578 (fun b : _183578 => N.add (@multiplicity _183578 _204009 b) (@multiplicity _183578 _204010 b))).
Proof. reflexivity. Qed.

Definition mdiff {A : Type'} := fun (m m' : Multiset A) a => m a - (m' a). 

Lemma mdiff_def {_183597 : Type'} : (@mdiff _183597) = (fun _204021 : Multiset _183597 => fun _204022 : Multiset _183597 => @multiset _183597 (fun b : _183597 => N.sub (@multiplicity _183597 _204021 b) (@multiplicity _183597 _204022 b))).
Proof. reflexivity. Qed.

Lemma WFP_def {_184264 : Type'} : @Acc _184264 = (fun lt2' : _184264 -> _184264 -> Prop => fun a : _184264 => forall WFP' : _184264 -> Prop, (forall a' : _184264, (forall y : _184264, (lt2' y a') -> WFP' y) -> WFP' a') -> WFP' a).
Proof.
  ext R a. apply prop_ext;intro H.
  - intros Acc' H'. induction H. now apply H'.
  - apply H. intro x. exact (Acc_intro _).
Qed.

(* given an order relation R on A, define the order relation Rm on Multiset A by :
   Rm m m' <-> (exists a in m, forall a' in m', a' is in m\{a} or R a a'.) *)
Definition morder {A : Type'} : (A -> A -> Prop) -> (Multiset A) -> (Multiset A) -> Prop := 
  fun R m m' => exists m0 a m1, (m' = munion m0 (msing a)) /\ 
  (m = munion m0 m1) /\ forall a', mmember a' m1 -> R a' a.
Lemma morder_def {_184446 : Type'} : (@morder _184446) = (fun _204323 : _184446 -> _184446 -> Prop => fun _204324 : Multiset _184446 => fun _204325 : Multiset _184446 => exists M0 : Multiset _184446, exists a : _184446, exists K : Multiset _184446, (_204325 = (@munion _184446 M0 (@msing _184446 a))) /\ ((_204324 = (@munion _184446 M0 K)) /\ (forall b : _184446, (@mmember _184446 b K) -> _204323 b a))).
Proof. reflexivity. Qed.

(*****************************************************************************)
(* Aligning the type of first order terms *)
(*****************************************************************************)

Require Import Coq.Lists.List.

Unset Elimination Schemes.
Inductive term : Set := V (_ : N) | Fn (_ : N) (_ : list term).
Set Elimination Schemes.

Definition term' := {| type := term; el := V 0 |}.
Canonical term'.

Definition list_204637 := list term.

(* defining induction principles and tactics *)
Section term_rect.

Variables
  (P : term -> Type)
  (Q : list term -> Type)
  (H1 : forall x, P (V x))
  (H2 : forall n l, Q l -> P (Fn n l))
  (H3 : Q nil)
  (H4 : forall t l, P t -> Q l -> Q (t :: l)).

Fixpoint term_rect t : P t :=
  match t as t return P t with
    | V x => H1 x
    | Fn n l => H2 n _
      ((fix tl_rect (l : list term) : Q l :=
        match l as l return Q l with
          | nil => H3
          | cons t' l' => H4 _ _ (term_rect t') (tl_rect l')
        end) l)
  end.

End term_rect.

Definition term_ind_full (P : term -> Prop) (Q : (list term) -> Prop) := 
  term_rect P Q.

Definition term_ind : forall (P : term -> Prop),
       (forall n, P (V n)) ->
       (forall n l, Forall P l -> P (Fn n l)) ->
       forall t, P t :=
  (fun P Hv HFn => term_ind_full P (Forall P) Hv HFn (Forall_nil _) (Forall_cons (P := P))).

Ltac Forall_induction t :=
  revert t ; match goal with
    |- forall t, ?P => apply (term_ind (fun t => P)) ; [
      let n := fresh "n" in
      intro n
    | let n := fresh "n" in
      let t := fresh "t" in
      let l := fresh "l" in
      let IHt := fresh "IHt" in
      intros n l IHt ]
  end.

Definition term_rec (P : term -> Set) (Q : list term -> Set) := term_rect P Q.

(* _dest_term and _dest_list are codefined but coq doesn't accept it so it is split in two with
   a fix inside. *)
Fixpoint _dest_term t : recspace N :=
  match t with
  | V n => CONSTR 0 n (fun _ => BOTTOM)
  | Fn n l => let fix _dest_tl l := match l with
    | nil => CONSTR 2 (ε (fun _ => True)) (fun n : N => @BOTTOM N)
    | cons t l => CONSTR 3 (ε (fun _ => True))
      (FCONS (_dest_term t)
      (FCONS (_dest_tl l) (fun _ => BOTTOM))) end
    in CONSTR 1 n (FCONS (_dest_tl l) (fun _ => BOTTOM))
  end.

Fixpoint _dest_list_204637 l : recspace N :=
  match l with
  | nil => CONSTR 2 (ε (fun _ => True)) (fun n : N => @BOTTOM N)
  | cons t l => CONSTR 3 (ε (fun _ => True))
    (FCONS (_dest_term t)
    (FCONS (_dest_list_204637 l) (fun _ => BOTTOM))) 
  end.

Definition _mk_term :=finv _dest_term.
Definition _mk_list_204637 := finv _dest_list_204637.

Lemma _dest_term_inj : forall t t', _dest_term t = _dest_term t' -> t = t'.
Proof.
  apply (term_ind_full
  (fun t => forall t', _dest_term t = _dest_term t' -> t = t')
  (fun l => forall l', _dest_list_204637 l = _dest_list_204637 l' -> l = l')).
  intros n t. induction t;simpl;inversion 1. reflexivity.
  - induction l ; intros H t' ; Forall_induction t' ; simpl ; inversion 1. 
    induction l. 3 : induction l0. reflexivity.
    1,2 : rewrite FCONS_inj in H3 ; destruct H3 as (H3 , _) ; inversion H3.
    f_equal. apply H. now rewrite FCONS_inj in H3.
  - induction l'. reflexivity. simpl. inversion 1.
  - induction l'; simpl ; inversion 1. do 2 rewrite FCONS_inj in H3. f_equal.
    now apply H. now apply H0.
Qed.

Lemma _mk_dest_term : forall t, (_mk_term (_dest_term t)) = t.
Proof.
  intro t. apply (_dest_term_inj).
  apply (ε_spec (P := fun t' => _dest_term t' = _dest_term t)).
  now exists t.
Qed.

Lemma _dest_list_204637_inj : forall l l', _dest_list_204637 l = _dest_list_204637 l' -> l = l'.
Proof. 
  induction l ; induction l'; simpl ; inversion 1. reflexivity.
  repeat rewrite FCONS_inj in H1. f_equal. now apply _dest_term_inj.
  now apply IHl.
Qed.

Lemma _mk_dest_list_204637 : forall l, (_mk_list_204637  (_dest_list_204637  l)) = l.
Proof.
  intro l. apply (_dest_list_204637_inj). 
  apply (ε_spec (P := fun l' => _dest_list_204637 l' = _dest_list_204637 l)).
  now exists l.
Qed.

Lemma V_def : V = (fun a : N => _mk_term ((fun a' : N => @CONSTR N (NUMERAL N0) a' (fun n : N => @BOTTOM N)) a)).
Proof. ext n. symmetry. exact (_mk_dest_term (V n)). Qed.

Lemma Fn_def : Fn = (fun a0 : N => fun a1 : list_204637 => _mk_term ((fun a0' : N => fun a1' : recspace N => @CONSTR N (N.succ (NUMERAL N0)) a0' (@FCONS (recspace N) a1' (fun n : N => @BOTTOM N))) a0 (_dest_list_204637 a1))).
Proof. ext n l. symmetry. exact (_mk_dest_term (Fn n l)). Qed.

Lemma _204640_def : nil = (_mk_list_204637 (@CONSTR N (N.succ (N.succ (NUMERAL N0))) (@ε N (fun v : N => True)) (fun n : N => @BOTTOM N))).
Proof. symmetry. exact (_mk_dest_list_204637 nil). Qed.

Lemma _204641_def : cons = (fun a0 : term => fun a1 : list_204637 => _mk_list_204637 ((fun a0' : recspace N => fun a1' : recspace N => @CONSTR N (N.succ (N.succ (N.succ (NUMERAL N0)))) (@ε N (fun v : N => True)) (@FCONS (recspace N) a0' (@FCONS (recspace N) a1' (fun n : N => @BOTTOM N)))) (_dest_term a0) (_dest_list_204637 a1))).
Proof. ext t l. symmetry. exact (_mk_dest_list_204637 (cons t l)). Qed.

(*****************************************************************************)
(* tactics to align recursive functions on terms *)
(*****************************************************************************)

(* identical to total_align, but specifically for functions
   defined where the recursive call is done through List.map *)

Ltac term_align1 :=
  align_ε' ; [ firstorder
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let b := fresh in
    let c := fresh in
    let d := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext t ; Forall_induction t ;
    try ext a ; try ext b ; try ext c ; try ext d ;
    [ now rewrite HV, HV'
    | rewrite HFn, HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align2 :=
  align_ε' ; [ firstorder
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let b := fresh in
    let c := fresh in
    let d := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext a t ; revert a ; Forall_induction t ;
    intro a ; try ext b ; try ext c ; try ext d ;
    [ now rewrite HV, HV'
    | rewrite HFn, HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align3 :=
  align_ε' ; [ firstorder
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let b := fresh in
    let c := fresh in
    let d := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext a b t ; revert a b ; Forall_induction t ;
    intros a b ; try ext c ; try ext d ;
    [ now rewrite HV, HV'
    | rewrite HFn, HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align4 :=
  align_ε' ; [ firstorder
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let b := fresh in
    let c := fresh in
    let d := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext a b c ; ext t ; revert a b c ; Forall_induction t ;
    intros a b c ; try ext d ;
    [ now rewrite HV, HV'
    | rewrite HFn, HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align5 :=
  align_ε' ; [ firstorder
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let b := fresh in
    let c := fresh in
    let d := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext a b c ; ext d t ; revert a b c d ; Forall_induction t ;
    intros a b c d ;
    [ now rewrite HV, HV'
    | rewrite HFn, HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align :=
  try term_align1 ;
  try term_align2 ;
  try term_align3 ;
  try term_align4 ;
  try term_align5.

(*****************************************************************************)
(* first order formulae *)
(*****************************************************************************)

Inductive form := 
| FFalse : form
| Atom : N -> list term -> form
| FImp : form -> form -> form
| FAll : N -> form -> form.

Definition form' := {| type := form ; el := FFalse |}.
Canonical form'.

Fixpoint _dest_form (f : form) : recspace (prod N (list term)) :=
match f with
| FFalse => CONSTR 0 (ε (fun n => True) , ε (fun l => True)) (fun n => BOTTOM)
| Atom n l => CONSTR 1 (n,l) (fun n : N => BOTTOM)
| FImp f f' => CONSTR 2 (ε (fun n => True) , ε (fun l => True)) (FCONS (_dest_form f) (FCONS (_dest_form f') (fun n => BOTTOM)))
| FAll n f => CONSTR 3 (n , ε (fun l => True)) (FCONS (_dest_form f) (fun n => BOTTOM)) end.

Definition _mk_form := finv _dest_form.

Lemma _mk_dest_form : forall f, (_mk_form (_dest_form f)) = f.
Proof. _mk_dest_rec. Qed.

Lemma FFalse_def : FFalse = (_mk_form (@CONSTR (prod N (list term)) (NUMERAL N0) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (fun n : N => @BOTTOM (prod N (list term))))).
Proof. symmetry. exact (_mk_dest_form FFalse). Qed.

Lemma Atom_def : Atom = (fun a0 : N => fun a1 : list term => _mk_form ((fun a0' : N => fun a1' : list term => @CONSTR (prod N (list term)) (N.succ (NUMERAL N0)) (@pair N (list term) a0' a1') (fun n : N => @BOTTOM (prod N (list term)))) a0 a1)).
Proof. ext n l. symmetry. exact (_mk_dest_form (Atom n l)). Qed.

Lemma FImp_def : FImp = (fun a0 : form => fun a1 : form => _mk_form ((fun a0' : recspace (prod N (list term)) => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (NUMERAL N0))) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a0' (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term)))))) (_dest_form a0) (_dest_form a1))).
Proof. ext f f'. symmetry. exact (_mk_dest_form (FImp f f')). Qed.

Lemma FAll_def : FAll = (fun a0 : N => fun a1 : form => _mk_form ((fun a0' : N => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (N.succ (NUMERAL N0)))) (@pair N (list term) a0' (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term))))) a0 (_dest_form a1))).
Proof. ext n f. symmetry. exact (_mk_dest_form (FAll n f)). Qed.

Definition Not f := FImp f FFalse.
Lemma Not_def : Not = (fun _204912 : form => FImp _204912 FFalse).
Proof. exact (eq_refl Not). Qed.

Definition FTrue : form := Not FFalse.
Lemma FTrue_def : FTrue = (Not FFalse).
Proof. exact (eq_refl FTrue). Qed.

Definition FOr f f' := FImp (FImp f f') f'.
Lemma FOr_def : FOr = (fun _204917 : form => fun _204918 : form => FImp (FImp _204917 _204918) _204918).
Proof. exact (eq_refl FOr). Qed.

Definition FAnd f f' := Not (FOr (Not f) (Not f')).
Lemma FAnd_def : FAnd = (fun _204929 : form => fun _204930 : form => Not (FOr (Not _204929) (Not _204930))).
Proof. exact (eq_refl FAnd). Qed.

Definition FEquiv f f' := FAnd (FImp f f') (FImp f' f).
Lemma FEquiv_def : FEquiv = (fun _204941 : form => fun _204942 : form => FAnd (FImp _204941 _204942) (FImp _204942 _204941)).
Proof. exact (eq_refl FEquiv). Qed.

Definition FEx n f := Not (FAll n (Not f)).
Lemma FEx_def : FEx = (fun _204953 : N => fun _204954 : form => Not (FAll _204953 (Not _204954))).
Proof. exact (eq_refl FEx). Qed.

(*****************************************************************************)
(* Functions on terms and formulae. *)
(*****************************************************************************)

Fixpoint functions_term t : (prod N N) -> Prop :=
  match t with
  | V _ => Empty_set
  | Fn n l => Ensembles.Add (list_Union (map (functions_term) l)) (n , lengthN l) end.

Lemma functions_term_def : functions_term = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> term -> (prod N N) -> Prop) (fun functions_term' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> term -> (prod N N) -> Prop => forall _204968 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))), (forall v : N, (functions_term' _204968 (V v)) = (@Ensembles.Empty_set (prod N N))) /\ (forall f : N, forall l : list term, (functions_term' _204968 (Fn f l)) = (@INSERT (prod N N) (@pair N N f (@lengthN term l)) (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) (functions_term' _204968) l))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))))))))).
Proof. term_align. Qed.

Fixpoint functions_form f : (prod N N) -> Prop :=
  match f with
  | FFalse => Empty_set
  | Atom _ l => list_Union (map functions_term l)
  | FImp f f' => Union (functions_form f) (functions_form f')
  | FAll _ f => functions_form f end.

Lemma functions_form_def : functions_form = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> form -> (prod N N) -> Prop) (fun functions_form' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> form -> (prod N N) -> Prop => forall _204976 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))), ((functions_form' _204976 FFalse) = (@Ensembles.Empty_set (prod N N))) /\ ((forall a : N, forall l : list term, (functions_form' _204976 (Atom a l)) = (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) functions_term l))) /\ ((forall p : form, forall q : form, (functions_form' _204976 (FImp p q)) = (@Ensembles.Union (prod N N) (functions_form' _204976 p) (functions_form' _204976 q))) /\ (forall x : N, forall p : form, (functions_form' _204976 (FAll x p)) = (functions_form' _204976 p))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))))))))).
Proof. total_align. Qed.

Fixpoint predicates_form f : (prod N N) -> Prop :=
  match f with
  | FFalse => Empty_set
  | Atom a l => Singleton (a , lengthN l)
  | FImp f f' => Union (predicates_form f) (predicates_form f')
  | FAll _ f => predicates_form f end.

Lemma predicates_form_def : predicates_form = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))))) -> form -> (prod N N) -> Prop) (fun predicates_form' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))))) -> form -> (prod N N) -> Prop => forall _204984 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))), ((predicates_form' _204984 FFalse) = (@Ensembles.Empty_set (prod N N))) /\ ((forall a : N, forall l : list term, (predicates_form' _204984 (Atom a l)) = (@INSERT (prod N N) (@pair N N a (@lengthN term l)) (@Ensembles.Empty_set (prod N N)))) /\ ((forall p : form, forall q : form, (predicates_form' _204984 (FImp p q)) = (@Ensembles.Union (prod N N) (predicates_form' _204984 p) (predicates_form' _204984 q))) /\ (forall x : N, forall p : form, (predicates_form' _204984 (FAll x p)) = (predicates_form' _204984 p))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))))))))).
Proof.
  total_align. exact (Singleton_from_Empty _).
Qed.

Definition functions (E : form -> Prop) : (prod N N) -> Prop :=
  UNIONS (IMAGE functions_form E).

Lemma functions_def : functions = (fun _204985 : form -> Prop => @UNIONS (prod N N) (@GSPEC ((prod N N) -> Prop) (fun GEN_PVAR_444 : (prod N N) -> Prop => exists f : form, @SETSPEC ((prod N N) -> Prop) GEN_PVAR_444 (@IN form f _204985) (functions_form f)))).
Proof. exact (eq_refl functions). Qed.

Definition predicates (E : form -> Prop) : (prod N N) -> Prop := 
  UNIONS (IMAGE predicates_form E).
  
Lemma predicates_def : predicates = (fun _204990 : form -> Prop => @UNIONS (prod N N) (@GSPEC ((prod N N) -> Prop) (fun GEN_PVAR_445 : (prod N N) -> Prop => exists f : form, @SETSPEC ((prod N N) -> Prop) GEN_PVAR_445 (@IN form f _204990) (predicates_form f)))).
Proof. exact (eq_refl predicates). Qed.

Definition language (E : form -> Prop) := (functions E, predicates E).

Lemma language_def : language = (fun _204995 : form -> Prop => @pair ((prod N N) -> Prop) ((prod N N) -> Prop) (functions _204995) (predicates _204995)).
Proof. exact (eq_refl language). Qed.

Definition Structure (A : Type') := prod (A -> Prop) (prod (N -> (list A) -> A)  (N -> (list A) -> Prop)).

Definition Dom {A : Type'} (M : Structure A) := fst M.

Lemma Dom_def {A : Type'} : (@Dom A) = (fun _205074 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @fst (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) _205074).
Proof. exact (eq_refl (@Dom A)). Qed.

Definition Fun {A : Type'} (M : Structure A) := fst (snd M).

Lemma Fun_def {A : Type'} : (@Fun A) = (fun _205087 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @fst (N -> (list A) -> A) (N -> (list A) -> Prop) (@snd (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) _205087)).
Proof. exact (eq_refl (@Fun A)). Qed.

Definition Pred {A : Type'} (M : Structure A) := snd (snd M).

Lemma Pred_def {A : Type'} : (@Pred A) = (fun _205100 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @snd (N -> (list A) -> A) (N -> (list A) -> Prop) (@snd (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) _205100)).
Proof. exact (eq_refl (@Pred A)). Qed.

Fixpoint free_variables_term t : N -> Prop :=
  match t with
  | V n => Singleton n
  | Fn _ l => list_Union (map free_variables_term l) end.

Lemma FVT_def : free_variables_term = (@ε ((prod N (prod N N)) -> term -> N -> Prop) (fun FVT' : (prod N (prod N N)) -> term -> N -> Prop => forall _205116 : prod N (prod N N), (forall x : N, (FVT' _205116 (V x)) = (@INSERT N x (@Ensembles.Empty_set N))) /\ (forall f : N, forall l : list term, (FVT' _205116 (Fn f l)) = (@list_Union N (@List.map term (N -> Prop) (FVT' _205116) l)))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).
Proof.
  term_align. exact (Singleton_from_Empty _).
Qed.

Fixpoint free_variables f : N -> Prop := 
  match f with
  | FFalse => Empty_set
  | Atom _ l => list_Union (map free_variables_term l)
  | FImp f f' => Union (free_variables f) (free_variables f')
  | FAll n f => Subtract (free_variables f) n end.

Lemma FV_def : free_variables = (@ε ((prod N N) -> form -> N -> Prop) (fun FV' : (prod N N) -> form -> N -> Prop => forall _205124 : prod N N, ((FV' _205124 FFalse) = (@Ensembles.Empty_set N)) /\ ((forall a : N, forall l : list term, (FV' _205124 (Atom a l)) = (@list_Union N (@List.map term (N -> Prop) free_variables_term l))) /\ ((forall p : form, forall q : form, (FV' _205124 (FImp p q)) = (@Ensembles.Union N (FV' _205124 p) (FV' _205124 q))) /\ (forall x : N, forall p : form, (FV' _205124 (FAll x p)) = (@Ensembles.Subtract N (FV' _205124 p) x))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))).
Proof. total_align. Qed.

Fixpoint bound_variables f : N -> Prop :=
  match f with
  | FFalse | Atom _ _ => Empty_set
  | FImp f f' => Union (bound_variables f) (bound_variables f')
  | FAll n f => Ensembles.Add (bound_variables f) n end.

Lemma BV_def : bound_variables = (@ε ((prod N N) -> form -> N -> Prop) (fun BV' : (prod N N) -> form -> N -> Prop => forall _205132 : prod N N, ((BV' _205132 FFalse) = (@Ensembles.Empty_set N)) /\ ((forall a : N, forall l : list term, (BV' _205132 (Atom a l)) = (@Ensembles.Empty_set N)) /\ ((forall p : form, forall q : form, (BV' _205132 (FImp p q)) = (@Ensembles.Union N (BV' _205132 p) (BV' _205132 q))) /\ (forall x : N, forall p : form, (BV' _205132 (FAll x p)) = (@INSERT N x (BV' _205132 p)))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))).
Proof. total_align. Qed.

Definition valmod {B A : Type'} (c : prod A B) (f : A -> B) (a : A) : B :=
  COND (a = fst c) (snd c) (f a). 

Lemma valmod_def {_185561 _185570 : Type'} : (@valmod _185561 _185570) = (fun _205133 : prod _185570 _185561 => fun _205134 : _185570 -> _185561 => fun y : _185570 => @COND _185561 (y = (@fst _185570 _185561 _205133)) (@snd _185570 _185561 _205133) (_205134 y)).
Proof. exact (eq_refl (@valmod _185561 _185570)). Qed.

Definition valuation {A : Type'} (M : Structure A) : (N -> A) -> Prop :=
  fun v => forall n, IN (v n) (Dom M).

Lemma valuation_def {_185712 : Type'} : (@valuation _185712) = (fun _205170 : prod (_185712 -> Prop) (prod (N -> (list _185712) -> _185712) (N -> (list _185712) -> Prop)) => fun _205171 : N -> _185712 => forall x : N, @IN _185712 (_205171 x) (@Dom _185712 _205170)).
Proof. exact (eq_refl (@valuation _185712)). Qed.

Fixpoint termval {A : Type'} (M : Structure A) (v : N -> A) (t : term) : A :=
  match t with
  | V n => v n
  | Fn n l => Fun M n (map (termval M v) l) end.

Lemma termval_def {_185808 : Type'} : (@termval _185808) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (_185808 -> Prop) (prod (N -> (list _185808) -> _185808) (N -> (list _185808) -> Prop))) -> (N -> _185808) -> term -> _185808) (fun termval' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (_185808 -> Prop) (prod (N -> (list _185808) -> _185808) (N -> (list _185808) -> Prop))) -> (N -> _185808) -> term -> _185808 => forall _205201 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall M : prod (_185808 -> Prop) (prod (N -> (list _185808) -> _185808) (N -> (list _185808) -> Prop)), forall v : N -> _185808, (forall x : N, (termval' _205201 M v (V x)) = (v x)) /\ (forall f : N, forall l : list term, (termval' _205201 M v (Fn f l)) = (@Fun _185808 M f (@List.map term _185808 (termval' _205201 M v) l)))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))).
Proof.
  (* term_align doesn't work : quantification on M and v before the clauses, first time encountered.
     There is nothing in the HOL-Light definition that indicates that it would happen  *)
  align_ε'. firstorder.
  intros f' H H'. ext M v. destruct (H M v) as (HV , HFn).
  destruct (H' M v) as (HV' , HFn').
  ext t. Forall_induction t. now rewrite HV, HV'.
  rewrite HFn, HFn'. f_equal. now apply map_ext_Forall.
  Qed.

Fixpoint holds {A : Type'} (M : Structure A) (v : N -> A) (f : form) : Prop :=
  match f with
  | FFalse => False
  | Atom n l => Pred M n (map (termval M v) l)
  | FImp f f' => holds M v f -> holds M v f'
  | FAll n f => forall a : A, IN a (Dom M) -> holds M (valmod (n , a) v) f end.

Lemma holds_def {_185905 : Type'} : (@holds _185905) = (@ε ((prod N (prod N (prod N (prod N N)))) -> (prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop))) -> (N -> _185905) -> form -> Prop) (fun holds' : (prod N (prod N (prod N (prod N N)))) -> (prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop))) -> (N -> _185905) -> form -> Prop => forall _205213 : prod N (prod N (prod N (prod N N))), (forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, (holds' _205213 M v FFalse) = False) /\ ((forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, forall a : N, forall l : list term, (holds' _205213 M v (Atom a l)) = (@Pred _185905 M a (@List.map term _185905 (@termval _185905 M v) l))) /\ ((forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, forall p : form, forall q : form, (holds' _205213 M v (FImp p q)) = ((holds' _205213 M v p) -> holds' _205213 M v q)) /\ (forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, forall x : N, forall p : form, (holds' _205213 M v (FAll x p)) = (forall a : _185905, (@IN _185905 a (@Dom _185905 M)) -> holds' _205213 M (@valmod _185905 N (@pair N _185905 x a) v) p))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))).
Proof.
  total_align3. apply prop_ext ; intros H' a. 
  - rewrite <- IHform. exact (H' a).
  - rewrite IHform. exact (H' a).
Qed.

Definition hold {A : Type'} (M : Structure A) (v : N -> A) (E : Ensemble form) :=
  Included E (holds M v).

Lemma hold_def {_185927 : Type'} : (@hold _185927) = (fun _205214 : prod (_185927 -> Prop) (prod (N -> (list _185927) -> _185927) (N -> (list _185927) -> Prop)) => fun _205215 : N -> _185927 => fun _205216 : form -> Prop => forall p : form, (@IN form p _205216) -> @holds _185927 _205214 _205215 p).
Proof. exact (eq_refl (@hold _185927)). Qed.

Definition satisfies {A : Type'} (M : Structure A) (E : Ensemble form) : Prop :=
  forall v f, (valuation M v /\ E f) -> holds M v f.

Lemma satisfies_def {_185947 : Type'} : (@satisfies _185947) = (fun _205235 : prod (_185947 -> Prop) (prod (N -> (list _185947) -> _185947) (N -> (list _185947) -> Prop)) => fun _205236 : form -> Prop => forall v : N -> _185947, forall p : form, ((@valuation _185947 _205235 v) /\ (@IN form p _205236)) -> @holds _185947 _205235 v p).
Proof. exact (eq_refl (@satisfies _185947)). Qed.

Definition satisfiable {A : Type'} (_ : Ensemble A) (E : Ensemble form) : Prop :=
  exists M : Structure A, (Dom M) <> Empty_set /\ satisfies M E.

Lemma satisfiable_def {A : Type'} : (@satisfiable A) = (fun _205939 : A -> Prop => fun _205940 : form -> Prop => exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@Ensembles.Empty_set A))) /\ (@satisfies A M _205940)).
Proof. exact (eq_refl (@satisfiable A)). Qed.

Definition valid {A : Type'} (_ : Ensemble A) (E : Ensemble form) : Prop :=
  forall M : Structure A, satisfies M E.

Lemma valid_def {A : Type'} : (@valid A) = (fun _205951 : A -> Prop => fun _205952 : form -> Prop => forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), @satisfies A M _205952).
Proof. exact (eq_refl (@valid A)). Qed.

Definition entails {A : Type'} (_ : Ensemble A) (E : Ensemble form) (f : form) : Prop :=
  forall (M : Structure A) v, hold M v E -> holds M v f.

Lemma entails_def {A : Type'} : (@entails A) = (fun _205963 : A -> Prop => fun _205964 : form -> Prop => fun _205965 : form => forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (@hold A M v _205964) -> @holds A M v _205965).
Proof. exact (eq_refl (@entails A)). Qed.

Definition equivalent {A : Type'} (_ : Ensemble A) (f f' : form) : Prop :=
  forall (M : Structure A) v, holds M v f <-> holds M v f'.

Lemma equivalent_def {A : Type'} : (@equivalent A) = (fun _205984 : A -> Prop => fun _205985 : form => fun _205986 : form => forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (@holds A M v _205985) = (@holds A M v _205986)).
Proof.
  unfold equivalent. ext _ f f'. apply prop_ext;intros H M v.
  - now apply prop_ext_eq.
  - now rewrite H.
Qed.

Definition interpretation {A : Type'} (funpred : (prod ((prod N N) -> Prop) ((prod N N) -> Prop)))
  (M : Structure A) : Prop := forall (n : N) (l : list A),
  IN (n , lengthN l) (fst funpred) /\ Forall (Dom M) l
  -> IN (Fun M n l) (Dom M).

Lemma interpretation_def {_186534 : Type'} : (@interpretation _186534) = (fun _206005 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _206006 : prod (_186534 -> Prop) (prod (N -> (list _186534) -> _186534) (N -> (list _186534) -> Prop)) => forall f : N, forall l : list _186534, ((@IN (prod N N) (@pair N N f (@lengthN _186534 l)) (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _206005)) /\ (@List.Forall _186534 (fun x : _186534 => @IN _186534 x (@Dom _186534 _206006)) l)) -> @IN _186534 (@Fun _186534 _206006 f l) (@Dom _186534 _206006)).
Proof. exact (eq_refl (@interpretation _186534)). Qed.

Fixpoint termsubst (v : N -> term) (t : term) : term :=
  match t with
  | V n => v n
  | Fn n l => Fn n (map (termsubst v) l) end.

Lemma termsubst_def : termsubst = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> term -> term) (fun termsubst' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> term -> term => forall _206161 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall v : N -> term, (forall x : N, (termsubst' _206161 v (V x)) = (v x)) /\ (forall f : N, forall l : list term, (termsubst' _206161 v (Fn f l)) = (Fn f (@List.map term term (termsubst' _206161 v) l)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  align_ε'. firstorder.
  intros f' H H'. ext v. destruct (H v) as (HV , HFn).
  destruct (H' v) as (HV' , HFn').
  ext t. Forall_induction t. now rewrite HV, HV'.
  rewrite HFn, HFn'. f_equal. now apply map_ext_Forall.
Qed.

(* Idea of something to do :
   mapping functions on finite sets in coq-hol-light recursively
   by defining it on finite sets and equal to the HOL-Light epsilon everywhere else.
   it should be easy to define an alignment tactic in that case,
   akin to the alignment of partial functions on lists *)

Definition SETMAX (E : N -> Prop) : N := ITSET N.max E 0.

Lemma SETMAX_def : SETMAX = (fun _206207 : N -> Prop => @ITSET N N N.max _206207 (NUMERAL N0)).
Proof. exact (eq_refl SETMAX). Qed.

Definition VARIANT E := N.succ (SETMAX E).
Lemma VARIANT_def : VARIANT = (fun _206212 : N -> Prop => N.add (SETMAX _206212) (NUMERAL (BIT1 N0))).
Proof.
  ext E. now rewrite N.add_1_r.
Qed.

Fixpoint formsubst (v : N -> term) f :=
  match f with
  | FFalse => FFalse
  | Atom n l => Atom n (map (termsubst v) l)
  | FImp f f' => FImp (formsubst v f) (formsubst v f')
  | FAll n f => let v' := valmod (n , V n) v in
       let n':= COND (exists n0 : N, (IN n0 (free_variables (FAll n f))) /\ (IN n (free_variables_term (v' n0)))) 
       (VARIANT (free_variables (formsubst v' f)))
       n in
      FAll n' (formsubst (valmod (n, V n') v) f) end.

Lemma formsubst_def : formsubst = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> form -> form) (fun formsubst' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> form -> form => forall _206432 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall v : N -> term, (formsubst' _206432 v FFalse) = FFalse) /\ ((forall p : N, forall v : N -> term, forall l : list term, (formsubst' _206432 v (Atom p l)) = (Atom p (@List.map term term (termsubst v) l))) /\ ((forall q : form, forall v : N -> term, forall r : form, (formsubst' _206432 v (FImp q r)) = (FImp (formsubst' _206432 v q) (formsubst' _206432 v r))) /\ (forall q : form, forall x : N, forall v : N -> term, (formsubst' _206432 v (FAll x q)) = (@Basics.apply (N -> term) form (fun v' : N -> term => @id form (@Basics.apply N form (fun z : N => @id form (FAll z (formsubst' _206432 (@valmod term N (@pair N term x (V z)) v) q))) (@COND N (exists y : N, (@IN N y (free_variables (FAll x q))) /\ (@IN N x (free_variables_term (v' y)))) (VARIANT (free_variables (formsubst' _206432 v' q))) x))) (@valmod term N (@pair N term x (V x)) v)))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  total_align2. unfold Basics.apply, id. now repeat rewrite IHform.
Qed.

(****************************************************************************)
(* Conversion to prenex form. *)
(****************************************************************************)

Fixpoint qfree f :=
  match f with 
  | FAll _ _ => False 
  | FImp f f' => qfree f /\ qfree f'
  | _ => True end.

Lemma qfree_def : qfree = (@ε ((prod N (prod N (prod N (prod N N)))) -> form -> Prop) (fun qfree' : (prod N (prod N (prod N (prod N N)))) -> form -> Prop => forall _215105 : prod N (prod N (prod N (prod N N))), ((qfree' _215105 FFalse) = True) /\ ((forall n : N, forall l : list term, (qfree' _215105 (Atom n l)) = True) /\ ((forall p : form, forall q : form, (qfree' _215105 (FImp p q)) = ((qfree' _215105 p) /\ (qfree' _215105 q))) /\ (forall x : N, forall p : form, (qfree' _215105 (FAll x p)) = False)))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))).
Proof. total_align. Qed.

(* PPAT defines a function on prenex formulae, with the default value for all else being the value
   for quantifier free formulae.  *)
Definition PPAT {A : Type} (f1 f2 : N -> form -> A) (f3 : form -> A) (f : form) : A :=
  match f with
  | FAll n f' => f1 n f'
  | FImp f' f'' => match f'' with (* Case FEx n f' *) 
                   | FFalse => match f' with
                     | FAll n f'0 => match f'0 with
                       | FImp f'1 f'2 => match f'2 with
                         | FFalse => f2 n f'1
                         | _ => f3 f end
                       | _ => f3 f end
                     | _ => f3 f end
                   | _ => f3 f end
  | _ => f3 f end.

(* The following :

  Definition PPAT {A : Type} (f1 f2 : N -> form -> A) (f3 : form -> A) (f : form) : A :=
  match f with
  | FAll n f' => f1 n f'
  | FImp (FAll n (FImp f' FFalse)) FFalse => f2 n f'
  | _ => f3 f end.

  doesn't work. For FImp f4 f5 (where f5 <> FFalse), its value is
  "match f4 with
  | FFalse | _ => f3 (FImp f4 f5)
  end"
  which coq cannot even prove to be equal to itself for some reason
  *)

Lemma PPAT_def {_190311 : Type'} : (@PPAT _190311) = (fun _216511 : N -> form -> _190311 => fun _216512 : N -> form -> _190311 => fun _216513 : form -> _190311 => fun _216514 : form => @COND _190311 (exists x : N, exists p : form, _216514 = (FAll x p)) (_216511 (@ε N (fun x : N => exists p : form, _216514 = (FAll x p))) (@ε form (fun p : form => _216514 = (FAll (@ε N (fun x : N => exists p' : form, _216514 = (FAll x p'))) p)))) (@COND _190311 (exists x : N, exists p : form, _216514 = (FEx x p)) (_216512 (@ε N (fun x : N => exists p : form, _216514 = (FEx x p))) (@ε form (fun p : form => _216514 = (FEx (@ε N (fun x : N => exists p' : form, _216514 = (FEx x p'))) p)))) (_216513 _216514))).
Proof.
  ext f1 f2 f3. ext f. repeat apply COND_intro.
  1,2 : intros (n , (f' , H0)) ; rewrite H0 ; simpl ; try intros _ ; f_equal ; align_ε'.
  1,5 : now exists f'.
  2,5 : f_equal ; align_ε' ; [ now exists f' | idtac ].
  1-3,5 : intros n' _ (f'' , H) ; now injection H.
  1,2 : intros f'' _ H ; now injection H.
  induction f;intros H H';auto.
  - destruct f5;auto. destruct f4;auto.
    destruct f4;auto. destruct f4_2;auto.
    contradiction H. exists n. now exists f4_1.
  - contradiction H'. exists n. now exists f.
Qed.

Inductive prenex : form -> Prop :=
| prenex_qfree : forall f, qfree f -> prenex f
| prenex_FAll : forall f n, prenex f -> prenex (FAll n f)
| prenex_FEx : forall f n, prenex f -> prenex (FEx n f).

Lemma prenex_def : prenex = (fun a : form => forall prenex' : form -> Prop, (forall a' : form, ((qfree a') \/ ((exists x : N, exists p : form, (a' = (FAll x p)) /\ (prenex' p)) \/ (exists x : N, exists p : form, (a' = (FEx x p)) /\ (prenex' p)))) -> prenex' a') -> prenex' a).
Proof.
  ind_align.
  - exact (prenex_qfree x H).
  - exact (prenex_FAll p x0 H0).
  - exact (prenex_FEx p x0 H0).
Qed.

Inductive universal : form -> Prop :=
| universal_qfree : forall f, qfree f -> universal f
| universal_forall : forall f n, universal f -> universal (FAll n f).

Lemma universal_def : universal = (fun a : form => forall universal' : form -> Prop, (forall a' : form, ((qfree a') \/ (exists x : N, exists p : form, (a' = (FAll x p)) /\ (universal' p))) -> universal' a') -> universal' a).
Proof.
  ind_align.
  - exact (universal_qfree x H).
  - exact (universal_forall p x0 H0).
Qed.

Fixpoint sizeN f :=
  match f with
  | FFalse | Atom _ _ => 1
  | FImp f f' => sizeN f + sizeN f'
  | FAll n f => N.succ (sizeN f) end.

Lemma size_def : sizeN = (@ε ((prod N (prod N (prod N N))) -> form -> N) (fun size' : (prod N (prod N (prod N N))) -> form -> N => forall _216494 : prod N (prod N (prod N N)), ((size' _216494 FFalse) = (NUMERAL (BIT1 N0))) /\ ((forall p : N, forall l : list term, (size' _216494 (Atom p l)) = (NUMERAL (BIT1 N0))) /\ ((forall q : form, forall r : form, (size' _216494 (FImp q r)) = (N.add (size' _216494 q) (size' _216494 r))) /\ (forall x : N, forall q : form, (size' _216494 (FAll x q)) = (N.add (NUMERAL (BIT1 N0)) (size' _216494 q)))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))).
Proof.
  total_align. now rewrite N.add_1_l.
Qed. 

(* size is used for recursion in HOL-Light, but we'd rather have nat than N. *)
Fixpoint size f :=
  match f with
  | FFalse | Atom _ _ => S O
  | FImp f f' => (size f + size f')%nat
  | FAll n f => S (size f) end.

Lemma size_formsubst : forall f v, size (formsubst v f) = size f.
Proof.
  induction f ; intro v.
  1,2 : reflexivity.
  - simpl. now rewrite IHf1, IHf2.
  - simpl. now rewrite IHf.
Qed.

Require Import Recdef FunInd.

Function Prenex_right0 (f f' : form) {measure size f'} :=
  match f' with
  | FAll n f' => let y := VARIANT (Union (free_variables f) (free_variables (FAll n f')))
                 in FAll y (Prenex_right0 f (formsubst (valmod (n , V y) V) f'))
  | FImp f'0 f'1 => match f'1 with (* Case FEx n f' *) 
                   | FFalse => match f'0 with
                     | FAll n f'0 => match f'0 with
                       | FImp f'1 f'2 => match f'2 with
                         | FFalse => let y := VARIANT (Union (free_variables f) 
                                       (free_variables (FEx n f'1)))
                                     in FEx y (Prenex_right0 f (formsubst (valmod (n , V y) V) f'1))
                         | _ => FImp f f' end
                       | _ => FImp f f' end
                     | _ => FImp f f' end
                   | _ => FImp f f' end
  | _ => FImp f f' end.
Proof.
  1 : intros f _ _ _ _ n _ f' _ _ _ _ _.
  2 : intros f _ n f' _.
  1,2 : rewrite size_formsubst ; simpl ; induction (size f') ;
        [ auto | exact (le_n_S _ _ IHn0)]. 
Qed.

Lemma formsubst_qfree : forall f v, qfree f -> qfree (formsubst v f).
Proof.
  induction f;auto.
  simpl. split. now apply IHf1. now apply IHf2.
Qed.

Lemma formsubst_prenex : forall f v, prenex f -> prenex (formsubst v f).
Proof.
  intros f v H. revert v. induction H ; intro v.
  - exact (prenex_qfree _ (formsubst_qfree _ _ H)).
  - exact (prenex_FAll _ _ (IHprenex _)).
  - exact (prenex_FEx _ _ (IHprenex _)).
Qed.

Lemma Prenex_right0_prenex : forall f f', qfree f -> prenex f' -> prenex (Prenex_right0 f f').
Proof.
  intros f f' H H'. functional induction (Prenex_right0 f f').
  3-7 : inversion H'.
  3,5 : destruct (proj1 H0).
  5,7,9 : now apply prenex_qfree.
  3-8 : match goal with H : _ |- _ => now rewrite <- H in y end.
  - apply prenex_FAll. apply IHf0. apply formsubst_prenex. now inversion H'.
  - apply prenex_FEx. apply IHf0. apply formsubst_prenex.
    inversion_clear H'. destruct (proj1 H0). assumption.
Qed.

Function Prenex_left0 (f' f : form) {measure size f} :=
  match f with
  | FAll n f => let y := VARIANT (Union (free_variables (FAll n f)) (free_variables f'))
                in FEx y (Prenex_left0 f' (formsubst (valmod (n , V y) V) f))
  | FImp f0 f1 => match f1 with (* Case FEx n f' *) 
                   | FFalse => match f0 with
                     | FAll n f0 => match f0 with
                       | FImp f01 f02 => match f02 with
                         | FFalse => let y := VARIANT (Union (free_variables (FEx n f01)) 
                                       (free_variables f'))
                                     in FAll y (Prenex_left0 f' (formsubst (valmod (n , V y) V) f01))
                         | _ => Prenex_right0 f f' end
                       | _ => Prenex_right0 f f' end
                     | _ => Prenex_right0 f f' end
                   | _ => Prenex_right0 f f' end
  | _ => Prenex_right0 f f' end.
Proof.
  1 : intros f' _ _ _ _ n _ f _ _ _ _ _.
  2 : intros f' _ n f _.
  1,2 : rewrite size_formsubst ; simpl ; induction (size f) ;
        [ auto | exact (le_n_S _ _ IHn0)].
Qed.

Lemma Prenex_left0_prenex : forall f f', prenex f -> prenex f' -> prenex (Prenex_left0 f' f).
Proof.
  intros f f' H H'. functional induction (Prenex_left0 f' f).
  3-7 : inversion H ; try now apply Prenex_right0_prenex.
  3-8 : match goal with H : _ |- _ => now rewrite <- H in y end.
  - apply prenex_FEx. apply IHf0. apply formsubst_prenex. now inversion H.
  - apply prenex_FAll. apply IHf0. apply formsubst_prenex.
    inversion_clear H. destruct (proj1 H0). assumption.
Qed.

Definition Prenex_right : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).

Lemma Prenex_right_def : Prenex_right = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))))))).
Proof. exact (eq_refl Prenex_right). Qed.

Definition Prenex_left : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form => forall _216680 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply N form (fun y : N => @id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply N form (fun y : N => @id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))))).

Lemma Prenex_left_def : Prenex_left = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form => forall _216680 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply N form (fun y : N => @id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply N form (fun y : N => @id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).
Proof. exact (eq_refl Prenex_left). Qed.

Lemma partial_align_ε2'var {U A B C : Type'} {uv0 : U} {f : A -> B -> C}
  {P : (U -> A -> B -> C) -> Prop} (QA : A -> Prop) (QB : B -> Prop) :
  P (fun _ => f) -> (forall f' uv a b, P (fun _ => f) ->  P f' -> QA a -> QB b ->
  f a b = f' uv a b) -> forall a b, QA a -> QB b -> f a b = ε P uv0 a b.
Proof.
  intros Hf Hunique a b. apply Hunique;auto.
  apply ε_spec. now exists (fun _ => f).
Qed.

Lemma Prenex_right0_def : forall f f', prenex f' -> Prenex_right0 f f' = Prenex_right f f'.
Proof.
  intros p q Hq. apply (partial_align_ε2'var (fun _ => True) prenex);auto.
  - intros _. repeat split.
    1,2 : intros ; exact (Prenex_right0_equation _ _).
    intros f0 f'0 QF. functional induction (Prenex_right0 f0 f'0);auto.
    destruct QF. destruct (proj1 QF).
  - clear p q Hq. intros f' uv p q Hf Hf' Hp Hq. 
    destruct (Hf' uv) as (Hf'_all , (Hf'_ex , Hf'_qfree)). clear Hf'.
    functional induction (Prenex_right0 p q).
    + rewrite Hf'_all. rewrite IHf. reflexivity. apply formsubst_prenex.
      now inversion Hq.
    + unfold FEx,Not in Hf'_ex. rewrite Hf'_ex.
      rewrite IHf. reflexivity. apply formsubst_prenex. inversion_clear Hq;auto.
      destruct (proj1 H).
    + inversion Hq. destruct (proj1 H). now rewrite <- H2 in y.
    + inversion Hq. destruct (proj1 H). now rewrite <- H1 in y.
    + inversion Hq. now rewrite Hf'_qfree. now rewrite <- H in y.
    + inversion Hq. now rewrite Hf'_qfree. now rewrite <- H1 in y.
    + inversion Hq. now rewrite Hf'_qfree. all : now rewrite <- H0 in y.
Qed.

(* The following definition is just Prenex_left0 but with default value Prenex_right
   instead of Prenex_right0, because Prenex_left0 actually does not actually
   respects the definition of Prenex_left, so this one is used as intermediary,
   since it does. *)
Function Prenex_left1 (f' f : form) {measure size f} :=
  match f with
  | FAll n f => let y := VARIANT (Union (free_variables (FAll n f)) (free_variables f'))
                in FEx y (Prenex_left1 f' (formsubst (valmod (n , V y) V) f))
  | FImp f0 f1 => match f1 with (* Case FEx n f' *) 
                   | FFalse => match f0 with
                     | FAll n f0 => match f0 with
                       | FImp f01 f02 => match f02 with
                         | FFalse => let y := VARIANT (Union (free_variables (FEx n f01)) 
                                       (free_variables f'))
                                     in FAll y (Prenex_left1 f' (formsubst (valmod (n , V y) V) f01))
                         | _ => Prenex_right f f' end
                       | _ => Prenex_right f f' end
                     | _ => Prenex_right f f' end
                   | _ => Prenex_right f f' end
  | _ => Prenex_right f f' end.
Proof.
  1 : intros f' _ _ _ _ n _ f _ _ _ _ _.
  2 : intros f' _ n f _.
  1,2 : rewrite size_formsubst ; simpl ; induction (size f) ;
        [ auto | exact (le_n_S _ _ IHn0)].
Qed.

Lemma Prenex_left0_def0 : forall f f', prenex f -> prenex f' -> Prenex_left0 f' f = Prenex_left1 f' f.
Proof.
  intros f f' Hf Hf'. functional induction (Prenex_left0 f' f).
  1,2 : rewrite Prenex_left1_equation ; rewrite IHf0 ; auto.
  1,2 : inversion Hf ; try contradiction ; apply formsubst_prenex ; auto.
  now destruct H.
  all : induction _x; try destruct y ; rewrite Prenex_left1_equation ;
      now rewrite (Prenex_right0_def _ _ Hf').
Qed.

Lemma Prenex_left0_def : forall f f', prenex f -> prenex f' -> Prenex_left0 f' f = Prenex_left f f'.
Proof.
  intros f f' H H'. rewrite (Prenex_left0_def0 f f' H H').
  revert f f' H H'. apply partial_align_ε2'var.
  - intros _. repeat split.
    1,2 : intros ; exact (Prenex_left1_equation _ _).
    intros f0 f'0 QF.
    functional induction (Prenex_left0 f0 f'0).
    destruct QF.
    1-3 : destruct (proj1 QF).
    all : induction _x ; try (now destruct QF) ; now rewrite Prenex_left1_equation.
  - intros f' uv p q Hf Hf' Hp Hq. 
    destruct (Hf' uv) as (Hf'_all , (Hf'_ex , Hf'_qfree)). clear Hf'.
    functional induction (Prenex_left1 q p).
    + rewrite Hf'_all. rewrite IHf. reflexivity. apply formsubst_prenex.
      now inversion Hp.
    + unfold FEx,Not in Hf'_ex. rewrite Hf'_ex.
      rewrite IHf. reflexivity. apply formsubst_prenex. inversion_clear Hp;auto.
      destruct (proj1 H).
    + inversion Hp. destruct (proj1 H). now rewrite <- H2 in y.
    + inversion Hp. destruct (proj1 H). now rewrite <- H1 in y.
    + inversion Hp. now rewrite Hf'_qfree. now rewrite <- H in y.
    + inversion Hp. now rewrite Hf'_qfree. now rewrite <- H1 in y.
    + inversion Hp. now rewrite Hf'_qfree. all : now rewrite <- H0 in y.
Qed.

Fixpoint Prenex (f : form) : form :=
  match f with
  | FAll n f => FAll n (Prenex f)
  | FImp f f' => Prenex_left0 (Prenex f') (Prenex f)
  | _ => f end.

Lemma Prenex_def0 : forall f, prenex (Prenex f).
Proof.
  induction f.
  1,2 : now apply prenex_qfree.
  - now apply Prenex_left0_prenex.
  - exact (prenex_FAll _ _ IHf).
Qed.

Lemma Prenex_def : Prenex = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> form -> form) (fun Prenex' : (prod N (prod N (prod N (prod N (prod N N))))) -> form -> form => forall _216688 : prod N (prod N (prod N (prod N (prod N N)))), ((Prenex' _216688 FFalse) = FFalse) /\ ((forall a : N, forall l : list term, (Prenex' _216688 (Atom a l)) = (Atom a l)) /\ ((forall p : form, forall q : form, (Prenex' _216688 (FImp p q)) = (Prenex_left (Prenex' _216688 p) (Prenex' _216688 q))) /\ (forall x : N, forall p : form, (Prenex' _216688 (FAll x p)) = (FAll x (Prenex' _216688 p)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof.
  total_align. simpl. rewrite Prenex_left0_def.
  reflexivity. exact (Prenex_def0 p). exact (Prenex_def0 q).
Qed.

(*****************************************************************************)
(* Propositional calculus *)
(*****************************************************************************)

Fixpoint pholds (TrueVar : Ensemble form) (f : form) : Prop :=
  match f with
  | FFalse => False
  | FImp f f' => pholds TrueVar f -> pholds TrueVar f'
  | _ => IN f TrueVar end.

Lemma pholds_def : pholds = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> form -> Prop) (fun pholds' : (prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> form -> Prop => forall _228069 : prod N (prod N (prod N (prod N (prod N N)))), (forall v : form -> Prop, (pholds' _228069 v FFalse) = False) /\ ((forall v : form -> Prop, forall p : N, forall l : list term, (pholds' _228069 v (Atom p l)) = (v (Atom p l))) /\ ((forall q : form, forall v : form -> Prop, forall r : form, (pholds' _228069 v (FImp q r)) = ((pholds' _228069 v q) -> pholds' _228069 v r)) /\ (forall v : form -> Prop, forall x : N, forall q : form, (pholds' _228069 v (FAll x q)) = (v (FAll x q)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof. total_align. Qed.

Definition psatisfies E E' := forall f, IN f E' -> pholds E f.
Lemma psatisfies_def : psatisfies = (fun _228082 : form -> Prop => fun _228083 : form -> Prop => forall p : form, (@IN form p _228083) -> pholds _228082 p).
Proof. exact (eq_refl psatisfies). Qed.

Definition psatisfiable E' := exists E, psatisfies E E'.

Lemma psatisfiable_def : psatisfiable = (fun _228094 : form -> Prop => exists v : form -> Prop, forall p : form, (@IN form p _228094) -> pholds v p).
Proof. exact (eq_refl psatisfiable). Qed.

Definition finsat (E : Ensemble form) : Prop := 
  forall F, Included F E /\ FINITE F -> psatisfiable F.

Lemma finsat_def : finsat = (fun _228106 : form -> Prop => forall B : form -> Prop, ((@Ensembles.Included form B _228106) /\ (@FINITE form B)) -> psatisfiable B).
Proof. exact (eq_refl finsat). Qed.

(*****************************************************************************)
(* canonical models *)
(*****************************************************************************)

Inductive terms (functions : Ensemble (prod N N)) : term -> Prop :=
| terms_V : forall n, terms functions (V n)
| terms_Fn : forall n l, IN (n , lengthN l) functions ->
    Forall (terms functions) l -> terms functions (Fn n l).

Lemma terms_def : terms = (fun fns : (prod N N) -> Prop => fun a : term => forall terms' : term -> Prop, (forall a' : term, ((exists x : N, a' = (V x)) \/ (exists f : N, exists l : list term, (a' = (Fn f l)) /\ ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term terms' l)))) -> terms' a') -> terms' a).
Proof.
  ext functions t. apply prop_ext ; intro H.
  intros P' H'. induction t ; apply H'.
  - now left;exists n.
  - right. exists n. exists l. split;auto.
    inversion_clear H. split;auto. clear H1.
    induction l;auto. inversion_clear H0. inversion_clear H2. 
    apply Forall_cons. now apply H. now apply IHl.
  - apply H ; clear H ; clear t ; intros t H.
    destruct H as [(n , eq) | (n , (l , (eq , (H , H'))))] ; rewrite eq.
    + exact (terms_V functions n).
    + exact (terms_Fn functions n l H H').
Qed.

(*****************************************************************************)
(* retval : bool with a 3rd possibility, exception *)
(*****************************************************************************)

Definition _dest_retval (v : option bool) : recspace Prop :=
match v with
| Some true => CONSTR 0 (ε (fun _ => True)) (fun _ => BOTTOM)
| Some false => CONSTR 1 (ε (fun _ => True)) (fun _ => BOTTOM)
| None => CONSTR 2 (ε (fun _ => True)) (fun _ => BOTTOM) end.

Definition _mk_retval := finv _dest_retval.

Lemma _dest_retval_inj : forall v v', _dest_retval v = _dest_retval v' -> v = v'.
Proof.
  induction v ; induction v' ; try induction a ; try induction a0 ;
  now inversion 1.
Qed.

Lemma _mk_dest_retval : forall v, (_mk_retval (_dest_retval v)) = v.
Proof.
  intro r. apply _dest_retval_inj.
  apply (ε_spec (P := fun x => _dest_retval x = _dest_retval r)).
  now exists r.
Qed.

Lemma TT_def : Some true = (_mk_retval (@CONSTR Prop (NUMERAL N0) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))).
Proof. symmetry. exact (_mk_dest_retval (Some true)). Qed.

Lemma FF_def : Some false = (_mk_retval (@CONSTR Prop (N.succ (NUMERAL N0)) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))).
Proof. symmetry. exact (_mk_dest_retval (Some false)). Qed.

Lemma Exception_def : None = (_mk_retval (@CONSTR Prop (N.succ (N.succ (NUMERAL N0))) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))).
Proof. symmetry. exact (_mk_dest_retval None). Qed.







