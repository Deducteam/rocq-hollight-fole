Require Import HOLLight_Logic1.mappings_coq_hol_light.
Import type classical_sets mappings ssreflect eqtype choice ssrnat ssrfun ssrbool boolp HB.structures.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.Reals.Reals.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(*****************************************************************************)
(* Miscelaneous *)
(*****************************************************************************)

Definition LET {A B : Type} (f : A -> B) := f.

Lemma LET_def {A B : Type'} : LET = (fun f : A -> B => fun x : A => f x).
Proof erefl.

Definition LET_END {A : Type} (a : A) := a.

Lemma LET_END_def {A : Type'} : LET_END = (fun t : A => t).
Proof erefl.

Lemma let_clear {A B} : forall (f : A -> B) x, LET (fun x => LET_END (f x)) x = (let x := x in f x).
Proof. reflexivity. Qed.

Ltac let_clear := rewrite ?let_clear.

Fixpoint list_Union {A : Type'} (l : list (set A)) : A -> Prop :=
  match l with
  | nil => set0
  | cons s l => s `|` (list_Union l) end.

Lemma LIST_UNION_def {_184792 : Type'} : list_Union = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> (list (_184792 -> Prop)) -> _184792 -> Prop) (fun LIST_UNION' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> (list (_184792 -> Prop)) -> _184792 -> Prop => forall _204636 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))), ((LIST_UNION' _204636 (@nil (_184792 -> Prop))) = (@set0 _184792)) /\ (forall h : _184792 -> Prop, forall t : list (_184792 -> Prop), (LIST_UNION' _204636 (@cons (_184792 -> Prop) h t)) = (@setU _184792 h (LIST_UNION' _204636 t)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))))))).
Proof.
  total_align.
Qed.

Lemma TC_def {A : Type'} : (@Relation_Operators.clos_trans A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall TC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (exists y : A, (TC' a0' y) /\ (TC' y a1'))) -> TC' a0' a1') -> TC' a0 a1).
Proof.
  ext 1=> R. ind_align. now apply (Relation_Operators.t_trans _ _ _ x0).
Qed.

Definition MEASURE {A : Type} f (x y : A) := f x < f y.

Lemma MEASURE_def {A : Type'} : (@MEASURE A) = (fun _8094 : A -> N => fun x : A => fun y : A => N.lt (_8094 x) (_8094 y)).
Proof erefl.

Lemma WFP_def {_184264 : Type'} : @Acc _184264 = (fun lt2' : _184264 -> _184264 -> Prop => fun a : _184264 => forall WFP' : _184264 -> Prop, (forall a' : _184264, (forall y : _184264, (lt2' y a') -> WFP' y) -> WFP' a') -> WFP' a).
Proof.
  ext 1 => R. ind_align.
Qed.

(*****************************************************************************)
(* Topologies (Libraries/analysis.ml) *)
(*****************************************************************************)

Definition re_Union {A : Type'} : ((A -> Prop) -> Prop) -> A -> Prop := fun _114505 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114505 s) /\ (s x).
Lemma re_Union_def {A : Type'} : (@re_Union A) = (fun _114505 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114505 s) /\ (s x)).
Proof. exact (REFL (@re_Union A)). Qed.
Definition re_union {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114510 : A -> Prop => fun _114511 : A -> Prop => fun x : A => (_114510 x) \/ (_114511 x).
Lemma re_union_def {A : Type'} : (@re_union A) = (fun _114510 : A -> Prop => fun _114511 : A -> Prop => fun x : A => (_114510 x) \/ (_114511 x)).
Proof. exact (REFL (@re_union A)). Qed.
Definition re_intersect {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114522 : A -> Prop => fun _114523 : A -> Prop => fun x : A => (_114522 x) /\ (_114523 x).
Lemma re_intersect_def {A : Type'} : (@re_intersect A) = (fun _114522 : A -> Prop => fun _114523 : A -> Prop => fun x : A => (_114522 x) /\ (_114523 x)).
Proof. exact (REFL (@re_intersect A)). Qed.
Definition re_null {A : Type'} : A -> Prop := fun x : A => False.
Lemma re_null_def {A : Type'} : (@re_null A) = (fun x : A => False).
Proof. exact (REFL (@re_null A)). Qed.
Definition re_universe {A : Type'} : A -> Prop := fun x : A => True.
Lemma re_universe_def {A : Type'} : (@re_universe A) = (fun x : A => True).
Proof. exact (REFL (@re_universe A)). Qed.
Definition re_subset {A : Type'} : (A -> Prop) -> (A -> Prop) -> Prop := fun _114534 : A -> Prop => fun _114535 : A -> Prop => forall x : A, (_114534 x) -> _114535 x.
Lemma re_subset_def {A : Type'} : (@re_subset A) = (fun _114534 : A -> Prop => fun _114535 : A -> Prop => forall x : A, (_114534 x) -> _114535 x).
Proof. exact (REFL (@re_subset A)). Qed.
Definition re_compl {A : Type'} : (A -> Prop) -> A -> Prop := fun _114546 : A -> Prop => fun x : A => ~ (_114546 x).
Lemma re_compl_def {A : Type'} : (@re_compl A) = (fun _114546 : A -> Prop => fun x : A => ~ (_114546 x)).
Proof. exact (REFL (@re_compl A)). Qed.


Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _114555 : (A -> Prop) -> Prop => (_114555 (@re_null A)) /\ ((_114555 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114555) -> _114555 (@re_Union A P)))).
Lemma istopology_def {A : Type'} : (@istopology A) = (fun _114555 : (A -> Prop) -> Prop => (_114555 (@re_null A)) /\ ((_114555 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114555) -> _114555 (@re_Union A P))))).
Proof. exact (REFL (@istopology A)). Qed.

Record Topology (A : Type) := {
  open : set (set A) ;
  open_empty : open set0;
  open_full : open setT;
  open_I : forall s s', open s -> open s' -> open (s `&` s');
  open_U : forall S, S `<=` open -> open (\bigcup_(s in S) s) }.

Definition discrete_Topology A : Topology A.
Proof.
  by exists setT.
Defined.

HB.instance Definition _ A := is_Type' (discrete_Topology A).

Definition topology {A : Type'} : ((A -> Prop) -> Prop) -> Topology A :=
  finv (@open A).

Lemma _mk_dest_Topology : forall {A : Type'} (a : Topology A), (@topology A (@open A a)) = a.
Proof.
  _mk_dest_record.
Qed.

Lemma andE b b' : b && b' = (b /\ b') :> Prop.
Proof. by ext ; move/andP. Qed.

Lemma re_intersect_eq {A} : @re_intersect A = setI.
Proof.
  funext => s0 s1 a ; rewrite -(in_setE (s0 `&` s1)) in_setI.
  by rewrite andE 2!in_setE.
Qed.

Lemma re_Union_eq {A} S : @re_Union A S = \bigcup_(s in S) s.
Proof.
  by rewrite/bigcup/mkset/re_Union ; funext => a ; rewrite exists2E.
Qed.

Lemma _dest_mk_Topology : forall {A : Type'} (r : (A -> Prop) -> Prop), ((fun t : (A -> Prop) -> Prop => @istopology A t) r) = ((@open A (@topology A r)) = r).
Proof.
  _dest_mk_record.
  - record_exists {| open := r |}.
    by rewrite -re_Union_eq ; auto.
  - by rewrite re_Union_eq ; auto.
Qed.

(*****************************************************************************)
(* Metric spaces (Libraries/analysis.ml) *)
(*****************************************************************************)
(* Difference with Rocq : Base is an argument instead of a projection *)

(* Cannot manage to map to a subtype of Metric_Space : Universe Inconsistency *)
Unset Implicit Arguments.
Definition discrete_metric A (c : prod A A) : R := if (fst c=snd c) then 0%R else 1%R.

Lemma discr_pos A : forall x y : A, (discrete_metric A (x,y) >= 0)%R.
Proof.
  intros. unfold discrete_metric. if_intro. reflexivity.
  left. exact Rlt_0_1.
Qed.

Lemma discr_sym A : forall x y : A, discrete_metric A (x,y) = discrete_metric A (y,x).
Proof.
  intros. unfold discrete_metric. do 2 if_intro.
  1,4 : reflexivity.
  intros nH H. 2 : intros H nH.
  all : symmetry in H ; destruct (nH H).
Qed.

Lemma discr_refl A : forall x y, discrete_metric A (x,y) = 0%R <-> x = y.
Proof.
  intros. unfold discrete_metric. if_intro;split;intro F;auto.
  destruct (R1_neq_R0 F). contradiction.
Qed.

Require Import Lra.
Lemma discr_tri A : forall x y z,
  (discrete_metric A (x,y) <= discrete_metric A (x,z) + discrete_metric A (z,y))%R.
Proof.
  intros. unfold discrete_metric. do 3 if_intro;try lra.
  intros eq1 eq2 neq. destruct (neq (eq_trans eq2 eq1)).
Qed.

Set Implicit Arguments.

Record Metric (A : Type) := { mdist : prod A A -> R;
    mdist_pos : forall x y : A, (mdist (x,y) >= 0)%R;
    mdist_sym : forall x y : A, mdist (x,y) = mdist (y,x);
    mdist_refl : forall x y : A, mdist (x,y) = 0%R <-> x = y;
    mdist_tri : forall x y z : A, (mdist (x,y) <= mdist (x,z) + mdist (z,y))%R }.

Definition discrete (A : Type) :=
  {| mdist := discrete_metric A;
     mdist_pos := discr_pos A;
     mdist_sym := discr_sym A;
     mdist_refl := discr_refl A;
     mdist_tri := discr_tri A |}.

HB.instance Definition _ (A : Type) := is_Type' (discrete A).

Definition metric {A : Type'} := finv (@mdist A).

Lemma _mk_dest_Metric : forall {A : Type'} (a : Metric A), (@metric A (@mdist A a)) = a.
Proof.
  _mk_dest_record.
Qed.

Definition ismet {A : Type'} : (prod A A -> R) -> Prop := fun d =>
  (forall x y, d (x,y) = 0%R <-> x=y) /\
  forall x y z : A, (d (y,z) <= d (x,y) + d (x,z))%R.

Lemma ismet_def {A : Type'} : (@ismet A) = (fun _114640 : (prod A A) -> R => (forall x : A, forall y : A, ((_114640 (@pair A A x y)) = (R_of_N (NUMERAL N0))) = (x = y)) /\ (forall x : A, forall y : A, forall z : A, Rle (_114640 (@pair A A y z)) (Rplus (_114640 (@pair A A x y)) (_114640 (@pair A A x z))))).
Proof.
  ext 1 =>d. unfold ismet. f_equal;auto.
  ext=>H ; intros. now apply propext.
  now rewrite H.
Qed.

Ltac d0 d x := (* automatically replaces all bound instances of d (x,x) with 0 assuming
                  mdist_refl is in the context. *)
  replace (d (x,x)) with (0%R) in * ; [ idtac
  | lazymatch goal with H : forall x y, d (x,y) = 0%R <-> x=y |- 0%R = d (x,x) =>
      symmetry ; now apply H end].

Lemma _dest_mk_Metric : forall {A : Type'} (r : (prod A A) -> R), ((fun m : (prod A A) -> R => @ismet A m) r) = ((@mdist A (@metric A r)) = r).
Proof.
  _dest_mk_record.
  - record_exists {| mdist := r |}.
    + specialize (H0 x y y). d0 r y. lra.
    + assert (H1 := H0 y x y). specialize (H0 x y x). d0 r y. d0 r x. lra.
    + assert (H1 := H0 z x z). assert (H2 := H0 x z x).
      specialize (H0 z x y). d0 r z. d0 r x. lra.
  - rewrite (mdist_sym0 x y). apply mdist_tri0.
Qed.

(*****************************************************************************)
(* Multisets *)
(*****************************************************************************)

Lemma empty_mempty_domain {A : Type} : (fun _ : A => 0 <> 0) = set0.
Proof. ext ; easy. Qed.

Import cardinality.
Definition is_fmultiset {A : Type'} : (A -> N) -> Prop :=
  fun f => @finite_set A (@GSPEC A (fun GEN_PVAR_433 : A => exists a : A, @SETSPEC A GEN_PVAR_433 (~ ((f a) = (NUMERAL N0))) a)).

Lemma is_fmultiset0 (A : Type') : is_fmultiset (fun (_ : A) => 0).
Proof.
  unfold is_fmultiset. rewrite SPEC_elim finite_as_ind empty_mempty_domain.
  exact (finite'_set0 _).
Qed.

Definition Multiset (A : Type') := subtype (is_fmultiset0 A).

Definition multiset {A : Type'} := mk (is_fmultiset0 A).
Definition multiplicity {A : Type'} := dest (is_fmultiset0 A).

Lemma _mk_dest_Multiset : forall {A : Type'} (a : Multiset A), (@multiset A (@multiplicity A a)) = a.
Proof. intros. apply mk_dest. Qed.

Lemma _dest_mk_Multiset : forall {A : Type'} (r : A -> N), ((fun f : A -> N => @finite_set A (@GSPEC A (fun GEN_PVAR_433 : A => exists a : A, @SETSPEC A GEN_PVAR_433 (~ ((f a) = (NUMERAL N0))) a))) r) = ((@multiplicity A (@multiset A r)) = r).
Proof. intros. apply dest_mk. Qed.

Definition mempty {A : Type'} : Multiset A := multiset (fun _ => 0).
Lemma mempty_def {_183533 : Type'} : mempty = (@multiset _183533 (fun b : _183533 => NUMERAL N0)).
Proof. reflexivity. Qed.

Definition mmember {A : Type'} (a : A) (m : Multiset A) := multiplicity m a <> 0.
Lemma mmember_def {_183543 : Type'} : mmember = (fun _203992 : _183543 => fun _203993 : Multiset _183543 => ~ ((@multiplicity _183543 _203993 _203992) = (NUMERAL N0))).
Proof. reflexivity. Qed.

Definition msing {A : Type'} : A -> Multiset A := fun a => multiset (fun a' => COND (a'=a) 1 0).

Lemma msing_def {_183559 : Type'} : msing = (fun _204004 : _183559 => @multiset _183559 (fun b : _183559 => @COND N (b = _204004) (NUMERAL (BIT1 N0)) (NUMERAL N0))).
Proof. reflexivity. Qed.

Definition munion {A : Type'} := fun (m m' : Multiset A) => 
  multiset (fun a => multiplicity m a + (multiplicity m' a)).

Lemma munion_def {_183578 : Type'} : (@munion _183578) = (fun _204009 : Multiset _183578 => fun _204010 : Multiset _183578 => @multiset _183578 (fun b : _183578 => N.add (@multiplicity _183578 _204009 b) (@multiplicity _183578 _204010 b))).
Proof. reflexivity. Qed.

Definition mdiff {A : Type'} := fun (m m' : Multiset A) => 
  multiset (fun a => multiplicity m a - (multiplicity m' a)). 

Lemma mdiff_def {_183597 : Type'} : (@mdiff _183597) = (fun _204021 : Multiset _183597 => fun _204022 : Multiset _183597 => @multiset _183597 (fun b : _183597 => N.sub (@multiplicity _183597 _204021 b) (@multiplicity _183597 _204022 b))).
Proof. reflexivity. Qed.

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

Require Import Stdlib.Lists.List.

Unset Elimination Schemes.
Inductive term : Set := V (_ : N) | Fn (_ : N) (_ : list term).
Set Elimination Schemes.

HB.instance Definition _ := is_Type' (V 0).

Definition list_204637 := list term.

Unset Implicit Arguments.

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

Fixpoint tl_rect l : Q l :=
  match l as l return Q l with
  | nil => H3
  | t::l => H4 t l (term_rect t) (tl_rect l) end.

End term_rect.

Definition term_ind_full (P : term -> Prop) (Q : list term -> Prop) := 
  term_rect P Q.

Definition tl_ind (P : term -> Prop) (Q : list term -> Prop) :=
  tl_rect P Q.

Definition term_tl_ind P Q H1 H2 H3 H4 :=
  conj (term_ind_full P Q H1 H2 H3 H4) (tl_ind P Q H1 H2 H3 H4).

Definition term_ind : forall (P : term -> Prop),
       (forall n, P (V n)) ->
       (forall n l, Forall P l -> P (Fn n l)) ->
       forall t, P t :=
  (fun P Hv HFn => term_ind_full P (Forall P) Hv HFn (Forall_nil _) (Forall_cons (P := P))).

Ltac Forall_induction t :=
  revert t ; match goal with
  |- forall t, ?P => apply (term_ind (fun t => P)) ;
    [ intros ?n | intros ?n ?l ?IHt ] end.

Definition term_rec (P : term -> Set) (Q : list term -> Set) := term_rect P Q.

Set Implicit Arguments.

(* _dest_term and _dest_list are codefined but coq doesn't accept it so it is split in two with
   a fix inside. *)
Fixpoint _dest_term t : recspace N :=
  match t with
  | V n => CONSTR 0 n []_rec
  | Fn n l => let fix _dest_tl l := match l with
    | nil => CONSTR 2 (ε (fun _ => True)) []_rec
    | cons t l => CONSTR 3 (ε (fun _ => True))
      [_dest_term t ; _dest_tl l]_rec end
    in CONSTR 1 n [_dest_tl l]_rec
  end.

Fixpoint _dest_list_204637 l : recspace N :=
  match l with
  | nil => CONSTR 2 (ε (fun _ => True)) []_rec
  | cons t l => CONSTR 3 (ε (fun _ => True))
    [_dest_term t ; _dest_list_204637 l]_rec end.

Definition _mk_term :=finv _dest_term.
Definition _mk_list_204637 := finv _dest_list_204637.

Lemma _dest_term_tl_inj : (forall t t', _dest_term t = _dest_term t' -> t = t')
  /\ (forall l l', _dest_list_204637 l = _dest_list_204637 l' -> l = l').
Proof.
  apply term_tl_ind.
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
  finv_inv_l. exact (proj1 _dest_term_tl_inj).
Qed.

Lemma _mk_dest_list_204637 : forall l, (_mk_list_204637  (_dest_list_204637  l)) = l.
Proof.
  finv_inv_l. exact (proj2 _dest_term_tl_inj).
Qed.

Definition term_tl_pred term' list_204637':=
    ((forall a0' : recspace N, 
      ((exists a : N, a0' = ((fun a' : N => @CONSTR N (NUMERAL N0) a' (fun n : N => @BOTTOM N)) a)) \/ 
        (exists a0 : N, exists a1 : recspace N, (a0' = ((fun a0'' : N => fun a1' : recspace N => 
          @CONSTR N (N.succ (NUMERAL N0)) a0'' (@FCONS (recspace N) a1' (fun n : N => @BOTTOM N))) a0 a1)) /\ 
            (list_204637' a1))) -> term' a0') /\ 
              (forall a1' : recspace N, ((a1' = (@CONSTR N (N.succ (N.succ (NUMERAL N0))) 
              (@ε N (fun v : N => True)) (fun n : N => @BOTTOM N))) \/ 
                (exists a0 : recspace N, exists a1 : recspace N, 
                (a1' = ((fun a0'' : recspace N => fun a1'' : recspace N => 
                @CONSTR N (N.succ (N.succ (N.succ (NUMERAL N0)))) (@ε N (fun v : N => True)) 
                (@FCONS (recspace N) a0'' (@FCONS (recspace N) a1'' (fun n : N => @BOTTOM N)))) a0 a1)) /\ 
                  ((term' a0) /\ (list_204637' a1)))) -> list_204637' a1')).

Lemma _dest_mk_term_tl0 : forall P P' : recspace N -> Prop, term_tl_pred P P' ->
  (forall t, P (_dest_term t)) /\ forall l, P' (_dest_list_204637 l).
Proof.
  intros P P' H. apply term_tl_ind.
  - intro n. apply H. left. now exists n.
  - intros n l IHl. apply H. right. exists n. now exists (_dest_list_204637 l).
  - apply H. now left.
  - intros t l IHt IHl. apply H. right. exists (_dest_term t). now exists (_dest_list_204637 l).
Qed.

Lemma _dest_mk_list_204637 : forall r, (fun r' => forall P P', term_tl_pred P P' -> P' r') r =
  (_dest_list_204637 (_mk_list_204637 r) = r).
Proof.
  intro r.
  let H := fresh in
  let x := fresh "x" in
  apply finv_inv_r ; intro H ;
  [ apply (H (fun y => exists x, _dest_term x = y)) ;
    clear H ; split ; intros x H ;
    firstorder ; rewrite H ;
    clear H ; simpl in *
  | destruct H as (x,H) ; rewrite <- H ; clear H ;
    intros P P' H ; exact (proj2 (_dest_mk_term_tl0 H) x) ].
  - now exists (V x0).
  - rewrite <- H0. now exists (Fn x0 x2).
  - now exists nil.
  - rewrite <- H0, <- H1. now exists (x3::x2).
Qed.

Lemma _dest_mk_term : forall r, (fun r' => forall P P', term_tl_pred P P' -> P r') r =
  (_dest_term (_mk_term r) = r).
Proof.
  intro r.
  let H := fresh in
  let x := fresh "x" in
  apply finv_inv_r ; intro H ;
  [ apply (H (fun y => exists x, _dest_term x = y) (fun y => exists x, _dest_list_204637 x = y)) ;
    clear H ; split ; intros x H ;
    firstorder ; rewrite H ;
    clear H ; simpl in *
  | destruct H as (x,H) ; rewrite <- H ; clear H ;
    intros P P' H ; exact (proj1 (_dest_mk_term_tl0 H) x) ].
  - now exists (V x0).
  - rewrite <- H0. now exists (Fn x0 x2).
  - now exists nil.
  - rewrite <- H0, <- H1. now exists (x3::x2).
Qed.

Lemma V_def : V = (fun a : N => _mk_term ((fun a' : N => @CONSTR N (NUMERAL N0) a' (fun n : N => @BOTTOM N)) a)).
Proof. constr_align _mk_dest_term. Qed.

Lemma Fn_def : Fn = (fun a0 : N => fun a1 : list_204637 => _mk_term ((fun a0' : N => fun a1' : recspace N => @CONSTR N (N.succ (NUMERAL N0)) a0' (@FCONS (recspace N) a1' (fun n : N => @BOTTOM N))) a0 (_dest_list_204637 a1))).
Proof. constr_align _mk_dest_term. Qed.

Definition tnil : list term := nil.
Lemma _204640_def : tnil = (_mk_list_204637 (@CONSTR N (N.succ (N.succ (NUMERAL N0))) (@ε N (fun v : N => True)) (fun n : N => @BOTTOM N))).
Proof. constr_align _mk_dest_list_204637. Qed.

Definition tcons : term -> _ := cons.

Lemma _204641_def : tcons = (fun a0 : term => fun a1 : list_204637 => _mk_list_204637 ((fun a0' : recspace N => fun a1' : recspace N => @CONSTR N (N.succ (N.succ (N.succ (NUMERAL N0)))) (@ε N (fun v : N => True)) (@FCONS (recspace N) a0' (@FCONS (recspace N) a1' (fun n : N => @BOTTOM N)))) (_dest_term a0) (_dest_list_204637 a1))).
Proof. constr_align _mk_dest_list_204637. Qed.

Lemma _204757_def : Fn = (fun a0 : N => fun a1 : list term => Fn a0 (@ε ((list term) -> list_204637) (fun fn : (list term) -> list_204637 => ((fn (@nil term)) = tnil) /\ (forall a0' : term, forall a1' : list term, (fn (@cons term a0' a1')) = (tcons a0' (fn a1')))) a1)).
Proof.
  ext=> t l. f_equal. apply (ext_fun (f := (fun l => l))). align_ε. auto.
  simpl. intros f' H H'. full_destruct. clear l. ext=> l. induction l ; auto.
  rewrite H1. now rewrite <- IHl.
Qed.

(*****************************************************************************)
(* tactics to align recursive functions on terms *)
(*****************************************************************************)

(* identical to total_align, but specifically for functions
   where the recursive call is done through List.map on terms *)

Ltac term_align1 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh in
    let t := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext 1=> t ; Forall_induction t ; extall ;
    [ now rewrite HV HV'
    | rewrite HFn HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align2 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext 2 => a t ; revert a ; Forall_induction t => a ; extall ;
    [ now rewrite HV HV'
    | rewrite HFn HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align3 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let b := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext 3 => a b t ; revert a b ; Forall_induction t=> a b ; extall ;
    [ now rewrite HV HV'
    | rewrite HFn HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align4 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh in
    let t := fresh in
    let a := fresh in
    let b := fresh in
    let c := fresh in
    let HV := fresh in
    let HFn := fresh in
    let HV' := fresh in
    let HFn' := fresh in
    intros f' (HV, HFn) (HV', HFn');
    ext 4 => a b c t ; revert a b c ; Forall_induction t => a b c ; extall ;
    [ now rewrite HV HV'
    | rewrite HFn HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

Ltac term_align5 :=
  align_ε ; [ repeat split ; intros ; auto
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
    ext 5 => a b c d t ; revert a b c d ;
    Forall_induction t => a b c d ; extall ;
    [ now rewrite HV HV'
    | rewrite HFn HFn' ; repeat (f_equal ; try now apply map_ext_Forall) ]].

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

HB.instance Definition _ := is_Type' FFalse.

Fixpoint _dest_form (f : form) : recspace (prod N (list term)) :=
match f with
| FFalse => CONSTR 0 (ε (fun n => True) , ε (fun l => True)) []_rec
| Atom n l => CONSTR 1 (n,l) []_rec
| FImp f f' => CONSTR 2 (ε (fun n => True) , ε (fun l => True))
  [_dest_form f ; _dest_form f']_rec
| FAll n f => CONSTR 3 (n , ε (fun l => True))
  [_dest_form f]_rec end.

Definition _mk_form := finv _dest_form.

Lemma _mk_dest_form : forall (a : form), (_mk_form (_dest_form a)) = a.
Proof. _mk_dest_inductive. Qed.

Lemma _dest_mk_form : forall (r : recspace (prod N (list term))), ((fun a : recspace (prod N (list term)) => forall form' : (recspace (prod N (list term))) -> Prop, (forall a' : recspace (prod N (list term)), ((a' = (@CONSTR (prod N (list term)) (NUMERAL N0) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (fun n : N => @BOTTOM (prod N (list term))))) \/ ((exists a0 : N, exists a1 : list term, a' = ((fun a0' : N => fun a1' : list term => @CONSTR (prod N (list term)) (N.succ (NUMERAL N0)) (@pair N (list term) a0' a1') (fun n : N => @BOTTOM (prod N (list term)))) a0 a1)) \/ ((exists a0 : recspace (prod N (list term)), exists a1 : recspace (prod N (list term)), (a' = ((fun a0' : recspace (prod N (list term)) => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (NUMERAL N0))) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a0' (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term)))))) a0 a1)) /\ ((form' a0) /\ (form' a1))) \/ (exists a0 : N, exists a1 : recspace (prod N (list term)), (a' = ((fun a0' : N => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (N.succ (NUMERAL N0)))) (@pair N (list term) a0' (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term))))) a0 a1)) /\ (form' a1))))) -> form' a') -> form' a) r) = ((_dest_form (_mk_form r)) = r).
Proof.
  intro r. _dest_mk_inductive.
  - now exists FFalse.
  - now exists (Atom x0 x1).
  - exists (FImp x3 x2). unfold _dest_form. now repeat f_equal.
  - exists (FAll x0 x2). unfold _dest_form. now repeat f_equal.
  - do 2 right. left. exists (_dest_form x0_1). exists (_dest_form x0_2).
    repeat split;auto. now apply IHx0_1. now apply IHx0_2.
  - do 3 right. exists n. exists (_dest_form x0). split. reflexivity. now apply IHx0.
Qed.

Lemma FFalse_def : FFalse = (_mk_form (@CONSTR (prod N (list term)) (NUMERAL N0) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (fun n : N => @BOTTOM (prod N (list term))))).
Proof. constr_align _mk_dest_form. Qed.

Lemma Atom_def : Atom = (fun a0 : N => fun a1 : list term => _mk_form ((fun a0' : N => fun a1' : list term => @CONSTR (prod N (list term)) (N.succ (NUMERAL N0)) (@pair N (list term) a0' a1') (fun n : N => @BOTTOM (prod N (list term)))) a0 a1)).
Proof. constr_align _mk_dest_form. Qed.

Lemma FImp_def : FImp = (fun a0 : form => fun a1 : form => _mk_form ((fun a0' : recspace (prod N (list term)) => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (NUMERAL N0))) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a0' (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term)))))) (_dest_form a0) (_dest_form a1))).
Proof. constr_align _mk_dest_form. Qed.

Lemma FAll_def : FAll = (fun a0 : N => fun a1 : form => _mk_form ((fun a0' : N => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (N.succ (NUMERAL N0)))) (@pair N (list term) a0' (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term))))) a0 (_dest_form a1))).
Proof. constr_align _mk_dest_form. Qed.

Definition Not f := FImp f FFalse.
Lemma Not_def : Not = (fun _204912 : form => FImp _204912 FFalse).
Proof. exact erefl. Qed.

Definition FTrue : form := Not FFalse.
Lemma FTrue_def : FTrue = (Not FFalse).
Proof. exact erefl. Qed.

Definition FOr f f' := FImp (FImp f f') f'.
Lemma FOr_def : FOr = (fun _204917 : form => fun _204918 : form => FImp (FImp _204917 _204918) _204918).
Proof. exact erefl. Qed.

Definition FAnd f f' := Not (FOr (Not f) (Not f')).
Lemma FAnd_def : FAnd = (fun _204929 : form => fun _204930 : form => Not (FOr (Not _204929) (Not _204930))).
Proof. exact erefl. Qed.

Definition FEquiv f f' := FAnd (FImp f f') (FImp f' f).
Lemma FEquiv_def : FEquiv = (fun _204941 : form => fun _204942 : form => FAnd (FImp _204941 _204942) (FImp _204942 _204941)).
Proof. exact erefl. Qed.

Definition FEx n f := Not (FAll n (Not f)).
Lemma FEx_def : FEx = (fun _204953 : N => fun _204954 : form => Not (FAll _204953 (Not _204954))).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* Functions on terms and formulae. *)
(*****************************************************************************)

Fixpoint functions_term t : (prod N N) -> Prop :=
  match t with
  | V _ => set0
  | Fn n l => (n , lengthN l) |` (list_Union (map (functions_term) l)) end.

Lemma functions_term_def : functions_term = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> term -> (prod N N) -> Prop) (fun functions_term' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> term -> (prod N N) -> Prop => forall _204968 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))), (forall v : N, (functions_term' _204968 (V v)) = (@set0 (prod N N))) /\ (forall f : N, forall l : list term, (functions_term' _204968 (Fn f l)) = (@INSERT (prod N N) (@pair N N f (@lengthN term l)) (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) (functions_term' _204968) l))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))))))))).
Proof. term_align. Qed.

Fixpoint functions_form f : (prod N N) -> Prop :=
  match f with
  | FFalse => set0
  | Atom _ l => list_Union (map functions_term l)
  | FImp f f' => (functions_form f) `|` (functions_form f')
  | FAll _ f => functions_form f end.

Lemma functions_form_def : functions_form = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> form -> (prod N N) -> Prop) (fun functions_form' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) -> form -> (prod N N) -> Prop => forall _204976 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))), ((functions_form' _204976 FFalse) = (@set0 (prod N N))) /\ ((forall a : N, forall l : list term, (functions_form' _204976 (Atom a l)) = (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) functions_term l))) /\ ((forall p : form, forall q : form, (functions_form' _204976 (FImp p q)) = (@setU (prod N N) (functions_form' _204976 p) (functions_form' _204976 q))) /\ (forall x : N, forall p : form, (functions_form' _204976 (FAll x p)) = (functions_form' _204976 p))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))))))))).
Proof. total_align. Qed.

Fixpoint predicates_form f : (prod N N) -> Prop :=
  match f with
  | FFalse => set0
  | Atom a l => [set (a , lengthN l)]
  | FImp f f' => (predicates_form f) `|` (predicates_form f')
  | FAll _ f => predicates_form f end.

Lemma predicates_form_def : predicates_form = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))))) -> form -> (prod N N) -> Prop) (fun predicates_form' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))))) -> form -> (prod N N) -> Prop => forall _204984 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))), ((predicates_form' _204984 FFalse) = (@set0 (prod N N))) /\ ((forall a : N, forall l : list term, (predicates_form' _204984 (Atom a l)) = (@INSERT (prod N N) (@pair N N a (@lengthN term l)) (@set0 (prod N N)))) /\ ((forall p : form, forall q : form, (predicates_form' _204984 (FImp p q)) = (@setU (prod N N) (predicates_form' _204984 p) (predicates_form' _204984 q))) /\ (forall x : N, forall p : form, (predicates_form' _204984 (FAll x p)) = (predicates_form' _204984 p))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))))))))).
Proof.
  total_align. by ssimpl.
Qed.

Definition functions (s : set form) : (prod N N) -> Prop :=
  UNIONS [set functions_form x | x in s].

Lemma functions_def : functions = (fun _204985 : form -> Prop => @UNIONS (prod N N) (@GSPEC ((prod N N) -> Prop) (fun GEN_PVAR_444 : (prod N N) -> Prop => exists f : form, @SETSPEC ((prod N N) -> Prop) GEN_PVAR_444 (@IN form f _204985) (functions_form f)))).
Proof. extall ; now ssimpl. Qed.

Definition predicates (s : form -> Prop) : (prod N N) -> Prop := 
  UNIONS [set predicates_form f | f in s].
  
Lemma predicates_def : predicates = (fun _204990 : form -> Prop => @UNIONS (prod N N) (@GSPEC ((prod N N) -> Prop) (fun GEN_PVAR_445 : (prod N N) -> Prop => exists f : form, @SETSPEC ((prod N N) -> Prop) GEN_PVAR_445 (@IN form f _204990) (predicates_form f)))).
Proof. extall ; now ssimpl. Qed.

Definition language (s : form -> Prop) := (functions s, predicates s).

Lemma language_def : language = (fun _204995 : form -> Prop => @pair ((prod N N) -> Prop) ((prod N N) -> Prop) (functions _204995) (predicates _204995)).
Proof. exact erefl. Qed.

Definition Structure (A : Type') := prod (A -> Prop) (prod (N -> (list A) -> A)  (N -> (list A) -> Prop)).

Definition Dom {A : Type'} (M : Structure A) := fst M.

Lemma Dom_def {A : Type'} : (@Dom A) = (fun _205074 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @fst (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) _205074).
Proof. exact erefl. Qed.

Definition Fun {A : Type'} (M : Structure A) := fst (snd M).

Lemma Fun_def {A : Type'} : (@Fun A) = (fun _205087 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @fst (N -> (list A) -> A) (N -> (list A) -> Prop) (@snd (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) _205087)).
Proof. exact erefl. Qed.

Definition Pred {A : Type'} (M : Structure A) := snd (snd M).

Lemma Pred_def {A : Type'} : (@Pred A) = (fun _205100 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @snd (N -> (list A) -> A) (N -> (list A) -> Prop) (@snd (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) _205100)).
Proof. exact erefl. Qed.

Fixpoint free_variables_term t : N -> Prop :=
  match t with
  | V n => [set n]
  | Fn _ l => list_Union (map free_variables_term l) end.

Lemma FVT_def : free_variables_term = (@ε ((prod N (prod N N)) -> term -> N -> Prop) (fun FVT' : (prod N (prod N N)) -> term -> N -> Prop => forall _205116 : prod N (prod N N), (forall x : N, (FVT' _205116 (V x)) = (@INSERT N x (@set0 N))) /\ (forall f : N, forall l : list term, (FVT' _205116 (Fn f l)) = (@list_Union N (@List.map term (N -> Prop) (FVT' _205116) l)))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).
Proof.
  term_align. by ssimpl.
Qed.

Fixpoint free_variables f : N -> Prop := 
  match f with
  | FFalse => set0
  | Atom _ l => list_Union (map free_variables_term l)
  | FImp f f' => free_variables f `|` free_variables f'
  | FAll n f => free_variables f `\ n end.

Lemma FV_def : free_variables = (@ε ((prod N N) -> form -> N -> Prop) (fun FV' : (prod N N) -> form -> N -> Prop => forall _205124 : prod N N, ((FV' _205124 FFalse) = (@set0 N)) /\ ((forall a : N, forall l : list term, (FV' _205124 (Atom a l)) = (@list_Union N (@List.map term (N -> Prop) free_variables_term l))) /\ ((forall p : form, forall q : form, (FV' _205124 (FImp p q)) = (@setU N (FV' _205124 p) (FV' _205124 q))) /\ (forall x : N, forall p : form, (FV' _205124 (FAll x p)) = (@DELETE N (FV' _205124 p) x))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))).
Proof. total_align. Qed.

Fixpoint bound_variables f : N -> Prop :=
  match f with
  | FFalse | Atom _ _ => set0
  | FImp f f' => bound_variables f `|` bound_variables f'
  | FAll n f => n |` bound_variables f end.

Lemma BV_def : bound_variables = (@ε ((prod N N) -> form -> N -> Prop) (fun BV' : (prod N N) -> form -> N -> Prop => forall _205132 : prod N N, ((BV' _205132 FFalse) = (@set0 N)) /\ ((forall a : N, forall l : list term, (BV' _205132 (Atom a l)) = (@set0 N)) /\ ((forall p : form, forall q : form, (BV' _205132 (FImp p q)) = (@setU N (BV' _205132 p) (BV' _205132 q))) /\ (forall x : N, forall p : form, (BV' _205132 (FAll x p)) = (@INSERT N x (BV' _205132 p)))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))).
Proof. total_align. Qed.

Definition valmod {B A : Type'} (c : prod A B) (f : A -> B) (a : A) : B :=
  if a = fst c then snd c else f a.

Lemma valmod_def {_185561 _185570 : Type'} : (@valmod _185561 _185570) = (fun _205133 : prod _185570 _185561 => fun _205134 : _185570 -> _185561 => fun y : _185570 => @COND _185561 (y = (@fst _185570 _185561 _205133)) (@snd _185570 _185561 _205133) (_205134 y)).
Proof. exact erefl. Qed.

Definition valuation {A : Type'} (M : Structure A) : (N -> A) -> Prop :=
  fun v => forall n, Dom M (v n).

Lemma valuation_def {_185712 : Type'} : (@valuation _185712) = (fun _205170 : prod (_185712 -> Prop) (prod (N -> (list _185712) -> _185712) (N -> (list _185712) -> Prop)) => fun _205171 : N -> _185712 => forall x : N, @IN _185712 (_205171 x) (@Dom _185712 _205170)).
Proof. extall ; now ssimpl. Qed.

Fixpoint termval {A : Type'} (M : Structure A) (v : N -> A) (t : term) : A :=
  match t with
  | V n => v n
  | Fn n l => Fun M n (map (termval M v) l) end.

Lemma termval_def {_185808 : Type'} : (@termval _185808) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (_185808 -> Prop) (prod (N -> (list _185808) -> _185808) (N -> (list _185808) -> Prop))) -> (N -> _185808) -> term -> _185808) (fun termval' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (_185808 -> Prop) (prod (N -> (list _185808) -> _185808) (N -> (list _185808) -> Prop))) -> (N -> _185808) -> term -> _185808 => forall _205201 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall M : prod (_185808 -> Prop) (prod (N -> (list _185808) -> _185808) (N -> (list _185808) -> Prop)), forall v : N -> _185808, (forall x : N, (termval' _205201 M v (V x)) = (v x)) /\ (forall f : N, forall l : list term, (termval' _205201 M v (Fn f l)) = (@Fun _185808 M f (@List.map term _185808 (termval' _205201 M v) l)))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))).
Proof.
  (* term_align doesn't work : quantification on M and v before the clauses, first time encountered.
     There is nothing in the HOL-Light definition that indicates that it would happen  *)
  align_ε. easy.
  intros f' H H'. ext => M v t. destruct (H M v) as (HV , HFn).
  destruct (H' M v) as (HV' , HFn').
  Forall_induction t. now rewrite HV HV'.
  rewrite HFn HFn'. f_equal. now apply map_ext_Forall.
  Qed.

Fixpoint holds {A : Type'} (M : Structure A) (v : N -> A) (f : form) : Prop :=
  match f with
  | FFalse => False
  | Atom n l => Pred M n (map (termval M v) l)
  | FImp f f' => holds M v f -> holds M v f'
  | FAll n f => forall a : A, IN a (Dom M) -> holds M (valmod (n , a) v) f end.

Lemma holds_def {_185905 : Type'} : (@holds _185905) = (@ε ((prod N (prod N (prod N (prod N N)))) -> (prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop))) -> (N -> _185905) -> form -> Prop) (fun holds' : (prod N (prod N (prod N (prod N N)))) -> (prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop))) -> (N -> _185905) -> form -> Prop => forall _205213 : prod N (prod N (prod N (prod N N))), (forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, (holds' _205213 M v FFalse) = False) /\ ((forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, forall a : N, forall l : list term, (holds' _205213 M v (Atom a l)) = (@Pred _185905 M a (@List.map term _185905 (@termval _185905 M v) l))) /\ ((forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, forall p : form, forall q : form, (holds' _205213 M v (FImp p q)) = ((holds' _205213 M v p) -> holds' _205213 M v q)) /\ (forall M : prod (_185905 -> Prop) (prod (N -> (list _185905) -> _185905) (N -> (list _185905) -> Prop)), forall v : N -> _185905, forall x : N, forall p : form, (holds' _205213 M v (FAll x p)) = (forall a : _185905, (@IN _185905 a (@Dom _185905 M)) -> holds' _205213 M (@valmod _185905 N (@pair N _185905 x a) v) p))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))).
Proof.
  total_align3. ext => H' a. 
  - rewrite <- IHform. exact (H' a).
  - rewrite IHform. exact (H' a).
Qed.

Definition hold {A : Type'} (M : Structure A) (v : N -> A) (s : set form) :=
  subset s (holds M v).

Lemma hold_def {_185927 : Type'} : (@hold _185927) = (fun _205214 : prod (_185927 -> Prop) (prod (N -> (list _185927) -> _185927) (N -> (list _185927) -> Prop)) => fun _205215 : N -> _185927 => fun _205216 : form -> Prop => forall p : form, (@IN form p _205216) -> @holds _185927 _205214 _205215 p).
Proof. extall ; now ssimpl. Qed.

Definition satisfies {A : Type'} (M : Structure A) (s : set form) : Prop :=
  forall v f, (valuation M v /\ s f) -> holds M v f.

Lemma satisfies_def {_185947 : Type'} : (@satisfies _185947) = (fun _205235 : prod (_185947 -> Prop) (prod (N -> (list _185947) -> _185947) (N -> (list _185947) -> Prop)) => fun _205236 : form -> Prop => forall v : N -> _185947, forall p : form, ((@valuation _185947 _205235 v) /\ (@IN form p _205236)) -> @holds _185947 _205235 v p).
Proof. extall ; now ssimpl. Qed.

Definition satisfiable {A : Type'} (_ : set A) (s : set form) : Prop :=
  exists M : Structure A, (Dom M) <> set0 /\ satisfies M s.

Lemma satisfiable_def {A : Type'} : (@satisfiable A) = (fun _205939 : A -> Prop => fun _205940 : form -> Prop => exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M _205940)).
Proof. exact erefl. Qed.

Definition valid {A : Type'} (_ : set A) (s : set form) : Prop :=
  forall M : Structure A, satisfies M s.

Lemma valid_def {A : Type'} : (@valid A) = (fun _205951 : A -> Prop => fun _205952 : form -> Prop => forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), @satisfies A M _205952).
Proof. exact erefl. Qed.

Definition entails {A : Type'} (_ : set A) (s : set form) (f : form) : Prop :=
  forall (M : Structure A) v, hold M v s -> holds M v f.

Lemma entails_def {A : Type'} : (@entails A) = (fun _205963 : A -> Prop => fun _205964 : form -> Prop => fun _205965 : form => forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (@hold A M v _205964) -> @holds A M v _205965).
Proof. exact erefl. Qed.

Definition equivalent {A : Type'} (_ : set A) (f f' : form) : Prop :=
  forall (M : Structure A) v, holds M v f = holds M v f'.

Lemma equivalent_def {A : Type'} : (@equivalent A) = (fun _205984 : A -> Prop => fun _205985 : form => fun _205986 : form => forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (@holds A M v _205985) = (@holds A M v _205986)).
Proof. exact erefl. Qed.

Definition interpretation {A : Type'} (funpred : (prod ((prod N N) -> Prop) ((prod N N) -> Prop)))
  (M : Structure A) : Prop := forall (n : N) (l : list A),
  fst funpred (n , lengthN l) -> Forall (Dom M) l
  -> Dom M (Fun M n l).

Lemma interpretation_def {_186534 : Type'} : (@interpretation _186534) = (fun _206005 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _206006 : prod (_186534 -> Prop) (prod (N -> (list _186534) -> _186534) (N -> (list _186534) -> Prop)) => forall f : N, forall l : list _186534, ((@IN (prod N N) (@pair N N f (@lengthN _186534 l)) (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _206005)) /\ (@List.Forall _186534 (fun x : _186534 => @IN _186534 x (@Dom _186534 _206006)) l)) -> @IN _186534 (@Fun _186534 _206006 f l) (@Dom _186534 _206006)).
Proof. ext=>M v ; ssimpl ; firstorder. Qed.

Fixpoint termsubst (v : N -> term) (t : term) : term :=
  match t with
  | V n => v n
  | Fn n l => Fn n (map (termsubst v) l) end.

Lemma termsubst_def : termsubst = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> term -> term) (fun termsubst' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> term -> term => forall _206161 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall v : N -> term, (forall x : N, (termsubst' _206161 v (V x)) = (v x)) /\ (forall f : N, forall l : list term, (termsubst' _206161 v (Fn f l)) = (Fn f (@List.map term term (termsubst' _206161 v) l)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  align_ε. easy.
  intros f' H H'. ext=> v t. destruct (H v) as (HV , HFn).
  destruct (H' v) as (HV' , HFn').
  Forall_induction t. now rewrite HV HV'.
  rewrite HFn HFn'. f_equal. now apply map_ext_Forall.
Qed.

Definition SETMAX (s : N -> Prop) : N := fold_set N.max s 0.

Lemma SETMAX_def : SETMAX = (fun _206207 : N -> Prop => @fold_set N N N.max _206207 (NUMERAL N0)).
Proof. exact erefl. Qed.

Definition VARIANT s := N.succ (SETMAX s).
Lemma VARIANT_def : VARIANT = (fun _206212 : N -> Prop => N.add (SETMAX _206212) (NUMERAL (BIT1 N0))).
Proof.
  ext=> s. now rewrite N.add_1_r.
Qed.

Fixpoint formsubst (v : N -> term) f :=
  match f with
  | FFalse => FFalse
  | Atom n l => Atom n (map (termsubst v) l)
  | FImp f f' => FImp (formsubst v f) (formsubst v f')
  | FAll n f => let v' := valmod (n , V n) v in
       let n':= if exists n0 : N, (IN n0 (free_variables (FAll n f))) /\ (IN n (free_variables_term (v' n0)))
         then VARIANT (free_variables (formsubst v' f)) else n in
       FAll n' (formsubst (valmod (n, V n') v) f) end.

Lemma formsubst_def : formsubst = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> form -> form) (fun formsubst' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> term) -> form -> form => forall _206432 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall v : N -> term, (formsubst' _206432 v FFalse) = FFalse) /\ ((forall p : N, forall v : N -> term, forall l : list term, (formsubst' _206432 v (Atom p l)) = (Atom p (@List.map term term (termsubst v) l))) /\ ((forall q : form, forall v : N -> term, forall r : form, (formsubst' _206432 v (FImp q r)) = (FImp (formsubst' _206432 v q) (formsubst' _206432 v r))) /\ (forall q : form, forall x : N, forall v : N -> term, (formsubst' _206432 v (FAll x q)) = (@Basics.apply (N -> term) form (fun v' : N -> term => @Datatypes.id form (@Basics.apply N form (fun z : N => @Datatypes.id form (FAll z (formsubst' _206432 (@valmod term N (@pair N term x (V z)) v) q))) (@COND N (exists y : N, (@IN N y (free_variables (FAll x q))) /\ (@IN N x (free_variables_term (v' y)))) (VARIANT (free_variables (formsubst' _206432 v' q))) x))) (@valmod term N (@pair N term x (V x)) v)))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  total_align2. unfold Basics.apply, Datatypes.id. now repeat rewrite IHform.
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

Definition PPAT {A : Type} (f1 f2 : N -> form -> A) (f3 : form -> A) (f : form) : A :=
  match f with
  | FAll n f' => f1 n f'
  | FImp (FAll n (FImp f' FFalse)) FFalse => f2 n f'
  | _ => f3 f end.

Lemma PPAT_def {_190311 : Type'} : (@PPAT _190311) = (fun _216511 : N -> form -> _190311 => fun _216512 : N -> form -> _190311 => fun _216513 : form -> _190311 => fun _216514 : form => @COND _190311 (exists x : N, exists p : form, _216514 = (FAll x p)) (_216511 (@ε N (fun x : N => exists p : form, _216514 = (FAll x p))) (@ε form (fun p : form => _216514 = (FAll (@ε N (fun x : N => exists p' : form, _216514 = (FAll x p'))) p)))) (@COND _190311 (exists x : N, exists p : form, _216514 = (FEx x p)) (_216512 (@ε N (fun x : N => exists p : form, _216514 = (FEx x p))) (@ε form (fun p : form => _216514 = (FEx (@ε N (fun x : N => exists p' : form, _216514 = (FEx x p'))) p)))) (_216513 _216514))).
Proof.
  ext=> f1 f2 f3 f. repeat if_intro.
  1,2 : intros (n , (f' , ->)) ; try intros _ ; try unfold FEx , Not ;
        simpl ; f_equal ; align_ε.
  1,5 : now exists f'.
  2,5 : repeat f_equal ; align_ε ; [ now exists f' | idtac ].
  1-3,5 : intros n' _ (f'' , H) ; now injection H.
  1,2 : intros f'' _ H ; now injection H.
  induction f;intros H H';auto.
  - destruct f4 ; simp PPAT ; auto.
    destruct f4 ; simp PPAT ; auto.
    destruct f4_2 ; simp PPAT ; auto.
    destruct f5 ; simp PPAT ; auto.
    contradiction H. exists n. now exists f4_1.
  - contradiction H'. exists n. now exists f.
Qed.

Inductive prenex : form -> Prop :=
| prenex_qfree : forall f, qfree f -> prenex f
| prenex_FAll : forall f n, prenex f -> prenex (FAll n f)
| prenex_FEx : forall f n, prenex f -> prenex (FEx n f).

Lemma prenex_def : prenex = (fun a : form => forall prenex' : form -> Prop, (forall a' : form, ((qfree a') \/ ((exists x : N, exists p : form, (a' = (FAll x p)) /\ (prenex' p)) \/ (exists x : N, exists p : form, (a' = (FEx x p)) /\ (prenex' p)))) -> prenex' a') -> prenex' a).
Proof. ind_align. Qed.

Inductive universal : form -> Prop :=
| universal_qfree : forall f, qfree f -> universal f
| universal_FAll : forall f n, universal f -> universal (FAll n f).

Lemma universal_def : universal = (fun a : form => forall universal' : form -> Prop, (forall a' : form, ((qfree a') \/ (exists x : N, exists p : form, (a' = (FAll x p)) /\ (universal' p))) -> universal' a') -> universal' a).
Proof. ind_align. Qed.

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
  induction f ; intro v ; reflexivity + now simpl ; f_equal.
Qed.

 (*
  Unfruitful attempts at defining the conversion to prenex form without equations


Lemma COND_elim' {A : Type'} {P Q' : Prop} {x y : A} (Q : A -> Prop) :
  Q (COND P x y) -> (P -> Q x -> Q') -> (~P -> Q y -> Q') -> Q'.
Proof.
  intros H H1 H2. destruct (classic P) as [H' | H'].
  - apply H1. auto. rewrite <- (is_True P) in H'. now rewrite H', COND_True in H.
  - apply H2. auto. rewrite <- (is_False P) in H'. now rewrite H', COND_False in H.
Qed.

Ltac COND_elim Q H' intropattern1 intropattern2 :=
  apply (COND_elim' Q H') ; clear H' ;
  [ intros intropattern1 H' | intros intropattern2 H' ].

Lemma valmod_permut {A B : Type'} (x x' : A) (y y' : B) (f : A -> B) :
  x <> x' -> valmod (x,y) (valmod (x',y') f) = valmod (x',y') (valmod (x,y) f).
Proof.
  intro H. unfold valmod. ext x0. simpl.
  repeat apply COND_intro ; try easy.
  intros H0 H1. destruct (H (eq_trans (eq_sym H1) H0)).
Qed.

Lemma valmod_triv {A B : Type'} (x : A) (f : A -> B) :
  valmod (x , f x) f = f.
Proof.
  unfold valmod. ext x0. apply COND_intro;auto. intro H. now rewrite H.
Qed.

Lemma termsubst_V : termsubst V = (fun t => t).
Proof.
  ext t. Forall_induction t;auto. simpl. f_equal.
  rewrite <- map_id. now apply map_ext_Forall.
Qed.

Lemma formsubst_V : formsubst V = (fun f => f).
Proof.
  ext f. induction f ; auto ; simpl.
  - induction l;auto. simpl. repeat f_equal.
    now rewrite termsubst_V. inversion IHl. now rewrite H0.
  - now rewrite IHf1,IHf2.
  - rewrite valmod_triv. apply COND_intro ; intro H.
    + destruct H as (n' , (H , H')). destruct H'. destruct H as (_ , H).
      contradiction H. exists.
    + rewrite valmod_triv. now rewrite IHf.
Qed.

Definition PRENEX_RIGHT : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).

Definition varswitch (l : list (N*N)) (f : form) :=
  fold_left (fun f' c => formsubst (valmod (fst c , V (snd c)) V) f') l f.

Fixpoint Prenex_right0 (f f' : form) (l : list (N * N)) :=
  match f' with
  | FAll n' f' =>
    let m := VARIANT
      (Union (free_variables f) (free_variables (varswitch l (FAll n' f'))))
    in FAll m (Prenex_right0 f f' ((n',m)::l))
  | FImp f0 f1 => match f1 with
    | FFalse => match f0 with
      | FAll n' f0 => match f0 with
        | FImp f'' f0 => match f0 with
          | FFalse => let m := VARIANT
              (Union (free_variables f)
              (free_variables (varswitch l (FEx n' f''))))
            in FEx m (Prenex_right0 f f'' ((n',m)::l))
          | _ => FImp f (varswitch l f') end
        | _ => FImp f (varswitch l f') end
      | _ => FImp f (varswitch l f') end
    | _ => FImp f (varswitch l f') end
  | _ => FImp f (varswitch l f') end.

Definition Prenex_right f f' := COND (prenex f') (Prenex_right0 f f' nil) (PRENEX_RIGHT f f').

Definition not_quantifier f :=
  match f with
  | FAll n f | FImp (FAll n (FImp f FFalse)) FFalse => False
  | _ => True end.

Definition test_hyp f P := 
  match f with
  | FAll n f' => P f'
  | FImp f0 f1 => match f1 with
    | FFalse => match f0 with
      | FAll _ f0 => match f0 with
        | FImp f' f0 => match f0 with
          | FFalse => P f'
          | _ => True end
        | _ => True end
      | _ => True end
    | _ => True end
  | _ => True end.

Fixpoint test_ind P (H : forall f, test_hyp f P -> P f) f : P f :=
  H f
  ( match f return test_hyp f P with
    | FAll n f' => test_ind P H f'
    | FImp f0 f1 => match f1 with
      | FFalse => match f0 with
        | FAll _ f0 => match f0 with
          | FImp f' f0 => match f0 with
            | FFalse => test_ind P H f'
            | _ => I end
          | _ => I end
        | _ => I end
      | _ => I end
    | _ => I end ).

Ltac test_ind f :=
  let IH := fresh "IH" in
  revert f ; match goal with |- forall f, ?P => apply (test_ind (fun f => P)) end ;
  intro f ; destruct f ; simpl test_hyp ; intro IH ;
  match type of IH with True => clear IH | _ => idtac end.

Lemma Prenex_right0_quantifier_case f f' : forall n m l,
  Prenex_right0 f f' ((n , m) :: l) =
  Prenex_right0 f (formsubst (valmod (n, V m) V) f') l.
Proof.
  test_ind f' ; intros n' m' l'.
  1,2 : reflexivity.
  - destruct f'2 ; auto. destruct f'1 ; auto. destruct f'1 ; auto.
    destruct f'1_2 ; auto. simpl. f_equal.
    repeat rewrite IH. f_equal. remember (VARIANT
      (Union (free_variables f)
         (Subtract (free_variables (FImp (FAll n (FImp f'1_1 FFalse)) FFalse)) n'))) as m.
    simpl. f_equal.
    + simpl.
    2 : simpl ; now repeat rewrite Union_empty.
    
Qed.

Lemma Prenex_right_def : Prenex_right = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))))))).
Proof.
  ext f f'. unfold Prenex_right. apply COND_intro ; auto ; intro H.
  - apply (partial_align1_spec2 prenex (fun _ f f' => Prenex_right0 f f' nil)) ; auto ;
    clear f f' H. intros _. repeat split.
    + intros f n' f'. let_clear. simpl. rewrite valmod_triv. simpl.
      apply COND_intro.
      * intros (n , (H , H')). destruct H'.
        destruct H as (_,H). contradiction H. exists.
      * intros _. f_equal. rewrite valmod_triv. now rewrite formsubst_V.
        
    + intros. unfold FEx,Not. now simp Prenex_right0.
    + intros f f' H. funelim (Prenex_right0 f f') ; auto.
      destruct (proj1 H0). destruct H0.
    + simpl. clear f f' H. intros g uv f f' H H' Pf'.
      specialize (H uv). specialize (H' uv). full_destruct.
      funelim (Prenex_right0 f f') ; try now (inversion Pf' ; rewrite H1 ; auto).
      * unfold FEx,Not in *. rewrite H1. let_clear. simpl in *. repeat f_equal. rewrite (H g uv);auto.
        apply formsubst_prenex. inversion Pf';auto. destruct (proj1 H5).
      * rewrite H'. let_clear. simpl in *. repeat f_equal. rewrite (H g uv);auto.
        apply formsubst_prenex. inversion Pf';easy.
  - reflexivity.
Qed.

Lemma form_Varswitch_triv l : Forall (fun c => fst c = snd c) l ->
  form_Varswitch l = (fun f => f).
Proof.
  intro H. ext f. revert l H. induction f ; intros l' H' ; simpl.
  - reflexivity.
  - rewrite term_Varswitch_triv;auto. now rewrite map_id.
  - f_equal ; auto.
  - induction H'. simpl. now rewrite IHf.
    destruct x as (m,m'). simpl in *.
Qed.

Lemma fold_right_cons {A B : Type} {f : A -> B -> B} x x0 l :
  (f x (fold_right f x0 l)) = fold_right f x0 (x::l).
Proof. reflexivity. Qed.

Lemma form_Varswitch_filter n l :
  form_Varswitch ((n,n)::l) = form_Varswitch (filter (fun c => negb (fst c =? n)) l).
Proof.
  induction l. simpl. rewrite form_Varswitch_nil.
  ext f. induction f;auto.
Qed.



Lemma formsubst_valmod_V l : NoDup (map fst l) ->
  formsubst (fold_right valmod V (map (fun c => (fst c, V (snd c))) l)) =
  form_Varswitch l.
Proof.
  intro H. ext f. revert l H. induction f ; intros l' H'.
  - reflexivity.
  - simpl. now rewrite termsubst_valmod_V.
  - simpl. f_equal;auto.
  - induction l'.
    + simpl form_Varswitch. rewrite <- IHf. simpl fold_right.
      now rewrite formsubst_V. auto.
    + destruct a as (m,m'). simpl. apply COND_intro.
      * intros (n0 , (H1,H2)). unfold valmod in H2. simpl in H2.
        COND_elim (fun t => IN n (free_variables_term t)) H2 e ne.
        rewrite e in H1. contradiction (proj2 H1).
        COND_elim (fun t => IN n (free_variables_term t)) H2 e ne'.
        { inversion_clear H2. rewrite N.eqb_refl. f_equal.
          { do 2 f_equal. do 2 rewrite fold_right_cons.
            rewrite <- (map_cons (fun c => (fst c , V (snd c))) (m,n)).
            rewrite <- (map_cons (fun c => (fst c , V (snd c))) (n,n)).
            rewrite IHf. rewrite valmod_permut.
            rewrite IHf. all : destruct e. rewrite <- N.eqb_neq in ne.
            now rewrite ne. now symmetry. }
        { rewrite valmod_permut.
          
      apply (COND_elim' (fun t => IN n0 (free_variables_term t)) H') ; clear H'.

Qed.
       let n':= COND (exists n0 : N, (IN n0 (free_variables (FAll n f))) /\ (IN n (free_variables_term (v' n0)))) 
       (VARIANT (free_variables (formsubst v' f)))
       n in
      FAll n' (formsubst (valmod (n, V n') v) f) end.

Fixpoint Prenex_right0 (f f' : form) (v : N -> term) :=
  match f' with
  | FAll n' f' => 
    let m := VARIANT 
      (Union (free_variables f) (free_variables (formsubst v (FAll n' f'))))
    in FAll m (Prenex_right0 f f' (valmod (n' , V m) v))
  | FImp (FAll n' (FImp f' FFalse)) FFalse => 
    let m := VARIANT 
      (Union (free_variables f) (free_variables (formsubst v (FEx n' f'))))
    in FEx m (Prenex_right0 f f' (valmod (n' , V m) v))
  | qfreeform => FImp f (formsubst v qfreeform)
  end.

Lemma formsubst_qfree : forall f v, qfree f -> qfree (formsubst v f).
Proof.
  intros f v. induction f ; auto.
  simpl. split. now apply IHf1. now apply IHf2.
Qed.

Lemma formsubst_prenex : forall f v, prenex f -> prenex (formsubst v f).
Proof.
  intros f v H. revert v. induction H ; intro v.
  - apply prenex_qfree. now apply formsubst_qfree.
  - exact (prenex_FAll _ _ (IHprenex _)).
  - exact (prenex_FEx _ _ (IHprenex _)).
Qed.

Lemma Prenex_right0_prenex : forall f f', qfree f -> prenex f' -> forall v, prenex (Prenex_right0 f f' v).
Proof.
  intros f f' H H'. induction H' ; intro v.
  - destruct f0 ; try now constructor. destruct f0_1.
    1-3 : apply prenex_qfree ; repeat split ; (try apply formsubst_qfree) ;
          simpl in H0 ; full_destruct ; auto.
    destruct (proj1 H0).
  - apply prenex_FAll. apply IHH'.
  - apply prenex_FEx. apply IHH'.
Qed.

Definition PRENEX_RIGHT : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).

Definition Prenex_right f f' := COND (prenex f') (Prenex_right0 f f' V) (PRENEX_RIGHT f f').

Lemma valmod_V_triv : forall n, valmod (n , V n) V = V.
Proof.
  intro n. ext n'. unfold valmod. apply COND_intro ; auto. intro H.
  now rewrite H.
Qed.

Lemma termsubst_V_triv : termsubst V = (fun t => t).
Proof.
  ext t. Forall_induction t;auto. simpl. f_equal.
  rewrite <- map_id. now apply map_ext_Forall.
Qed.

Lemma formsubst_V_triv : formsubst V = (fun f => f).
Proof.
  ext f. induction f ; auto ; simpl.
  - induction l;auto. simpl. repeat f_equal.
    now rewrite termsubst_V_triv. inversion IHl. now rewrite H0.
  - now rewrite IHf1,IHf2.
  - rewrite valmod_V_triv. apply COND_intro ; intro H.
    + destruct H as (n' , (H , H')). destruct H'. destruct H as (_ , H).
      contradiction H. exists.
    + rewrite valmod_V_triv. now rewrite IHf.
Qed.
(*
Lemma Prenex_right_forall_def : forall f f' v n,
  VARIANT (Union (free_variables f) (free_variables (formsubst v (FAll n f')))) = 0.
  simpl.
  VARIANT
  (Union (free_variables f)
     (Subtract
        (free_variables
           (formsubst
              (valmod
                 (n,
                  V n) v) f')) n))
                    (COND
                       (exists n0 : N,
                          IN n0 (Subtract (free_variables f') n) /\
                          IN n (free_variables_term (valmod (n, V n) v n0)))
                       (VARIANT (free_variables (formsubst (valmod (n, V n) v) f'))) n)) v)
              f'))
        (COND
           (exists n0 : N,
              IN n0 (Subtract (free_variables f') n) /\
              IN n (free_variables_term (valmod (n, V n) v n0)))
           (VARIANT (free_variables (formsubst (valmod (n, V n) v) f'))) n))) = 0
 *) (*
Lemma Prenex_right_def0 : forall f n f' v,
  (Prenex_right0 f f' (valmod (n , V (VARIANT
    (Union (free_variables f)
      (Subtract
        (free_variables
           (formsubst
              (valmod
                 (n,
                  V n) v) f')) n)))) v) =
      Prenex_right0 f (formsubst (valmod (n , V (VARIANT
        (Union (free_variables f) (free_variables (FAll n f'))))) V) f') v).
Proof.
 intros f n. induction f' ; intro v ; auto.
 - simpl. do 2 f_equal.
   induction l ; auto.
   simpl. f_equal.
   + clear IHl. Forall_induction a.
     * simpl. unfold valmod at 1 4. apply COND_intro.
       { simpl. intro H. rewrite H. 
         apply COND_intro ; try (intro H' ; now contradiction H') ; intros _.
         simpl. *)

Lemma Prenex_right_def0 : forall f n' f', Prenex_right0 f f'
  (valmod
     (n',
      V
        (VARIANT
           (Union (free_variables f)
              (Subtract (free_variables (formsubst (valmod (n', V n') V) f')) n')))) V) =
Prenex_right0 f
  (formsubst
     (valmod (n', V (VARIANT (Union (free_variables f) (Subtract (free_variables f') n')))) V)
     f') V.
Proof.
 intros f n. induction f' ; auto.
 - simpl. do 2 f_equal.
   induction l ; auto.
   simpl. f_equal.
   + clear IHl. Forall_induction a ; simpl.
     * unfold valmod at 1 4. simpl. apply COND_intro ; intro H.
       { rewrite H.
         apply COND_intro ; try (intro H' ; now contradiction H') ; intros _.
         simpl. rewrite valmod_V_triv. rewrite termsubst_V_triv. now rewrite map_id. }
       { apply COND_intro. intro H'. destruct (H H').
         reflexivity. }
     * f_equal. apply map_ext_Forall in IHt. rewrite (map_map _ (termsubst V)). simpl in IHt. rewrite IHt. repeat rewrite map_map. f_equal.
  *)

Opaque card_eq.

Equations? Prenex_right0 (f f' : form) : form by wf (size f') lt :=
  Prenex_right0 f (FAll n' f') =>
    let y := VARIANT (setU (free_variables f) (free_variables (FAll n' f')))
    in FAll y (Prenex_right0 f (formsubst (valmod (n' , V y) V) f'));
  Prenex_right0 f (FImp (FAll n' (FImp f' FFalse)) FFalse) =>
    let y := VARIANT (setU (free_variables f) (free_variables (FEx n' f')))
    in FEx y (Prenex_right0 f (formsubst (valmod (n' , V y) V) f'));
  Prenex_right0 f qfree => FImp f qfree.
Proof.
  1,2 : rewrite/addn size_formsubst // ; lia.
Qed.


Lemma formsubst_qfree : forall f v, qfree f -> qfree (formsubst v f).
Proof.
  intros f v. induction f ; auto.
  simpl. split. now apply IHf1. now apply IHf2.
Qed.

Lemma formsubst_prenex : forall f v, prenex f -> prenex (formsubst v f).
Proof.
  intros f v H. revert v. induction H ; intro v.
  - apply prenex_qfree. now apply formsubst_qfree.
  - exact (prenex_FAll _ (IHprenex _)).
  - exact (prenex_FEx _ (IHprenex _)).
Qed.

Lemma Prenex_right0_prenex : forall f f', qfree f -> prenex f' -> prenex (Prenex_right0 f f').
Proof.
  intros f f' H H'. funelim (Prenex_right0 f f') ;
  try (inversion H' ; now apply prenex_qfree).
  - apply prenex_FEx. apply H;auto. inversion H'. destruct (proj1 H1).
    now apply (formsubst_prenex).
  - apply prenex_FAll. apply H;auto. inversion H'. destruct H1.
    now apply (formsubst_prenex).
Qed.

Definition PRENEX_RIGHT : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).

Definition Prenex_right f f' := if prenex f' then Prenex_right0 f f' else PRENEX_RIGHT f f'.

Lemma Prenex_right_def : Prenex_right = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))))))).
Proof.
  unfold Prenex_right, PRENEX_RIGHT.
  align_ε_if.
  - repeat split.
    + intros f n' f'. now simp Prenex_right0.
    + intros. unfold FEx,Not. now simp Prenex_right0.
    + intros f f' H. funelim (Prenex_right0 f f') ; auto.
      destruct (proj1 H0). destruct H0.
  - simpl. intros g H H' f f' Pf'. full_destruct.
      funelim (Prenex_right0 f f') ; try now (inversion Pf' ; rewrite H2 ; auto).
      * unfold FEx,Not in *. rewrite H2. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf';auto. destruct (proj1 H6).
      * rewrite H1. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf';easy.
Qed.

Equations? Prenex_left0 (f f' : form) : form by wf (size f) lt :=
  Prenex_left0 (FAll n f) f' =>
    let y := VARIANT (setU (free_variables (FAll n f)) (free_variables f'))
    in FEx y (Prenex_left0 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left0 (FImp (FAll n (FImp f FFalse)) FFalse) f' =>
    let y := VARIANT (setU (free_variables (FEx n f)) (free_variables f'))
    in FAll y (Prenex_left0 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left0 f f' => Prenex_right0 f f'.
Proof.
    1,2 : rewrite/addn size_formsubst // ; lia.
Qed.

Equations? Prenex_left1 (f f' : form) : form by wf (size f) lt :=
  Prenex_left1 (FAll n f) f' =>
    let y := VARIANT (setU (free_variables (FAll n f)) (free_variables f'))
    in FEx y (Prenex_left1 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left1 (FImp (FAll n (FImp f FFalse)) FFalse) f' =>
    let y := VARIANT (setU (free_variables (FEx n f)) (free_variables f'))
    in FAll y (Prenex_left1 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left1 f f' => Prenex_right f f'.
Proof.
  1,2 : rewrite/addn size_formsubst // ; lia.
Qed.

Lemma Prenex_left0_prenex : forall f f', prenex f -> prenex f' -> prenex (Prenex_left0 f f').
Proof.
  intros f f' H H'. funelim (Prenex_left0 f f') ;
  try now inversion H ; apply Prenex_right0_prenex.
  - apply prenex_FAll. apply H;auto. inversion H0. destruct (proj1 H1).
    now apply (formsubst_prenex).
  - apply prenex_FEx. apply H;auto. inversion H0. destruct H1.
    now apply (formsubst_prenex).
Qed.

Definition PRENEX_LEFT : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form => forall _216680 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@setU N (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@setU N (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))))).

Definition Prenex_left f f' := if prenex f then Prenex_left1 f f' else PRENEX_LEFT f f'.

Lemma Prenex_left_def : Prenex_left = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form => forall _216680 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@setU N (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@setU N (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).
Proof.
  unfold Prenex_left, PRENEX_LEFT.
  align_ε_if.
  - repeat split.
    + intros. now simp Prenex_left1.
    + intros. unfold FEx,Not.  now simp Prenex_left1.
    + intros f' f H. destruct f ; try now simp Prenex_left1.
      destruct f1 ; try now simp Prenex_left1. destruct (proj1 H).
  - simpl. intros g H H' f f' Pf. full_destruct.
      funelim (Prenex_left1 f f') ; try now (inversion Pf ; rewrite H2 ; auto).
      * unfold FEx,Not in *. rewrite H2. let_clear. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf;auto. destruct (proj1 H6).
      * rewrite H1. let_clear. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf;easy.
Qed.

Fixpoint Prenex (f : form) : form :=
  match f with
  | FAll n f => FAll n (Prenex f)
  | FImp f f' => Prenex_left0 (Prenex f) (Prenex f')
  | _ => f end.

Lemma Prenex_def0 : forall f, prenex (Prenex f).
Proof.
  induction f.
  1,2 : now apply prenex_qfree.
  - now apply Prenex_left0_prenex.
  - exact (prenex_FAll _ IHf).
Qed.

Lemma Prenex_def : Prenex = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> form -> form) (fun Prenex' : (prod N (prod N (prod N (prod N (prod N N))))) -> form -> form => forall _216688 : prod N (prod N (prod N (prod N (prod N N)))), ((Prenex' _216688 FFalse) = FFalse) /\ ((forall a : N, forall l : list term, (Prenex' _216688 (Atom a l)) = (Atom a l)) /\ ((forall p : form, forall q : form, (Prenex' _216688 (FImp p q)) = (Prenex_left (Prenex' _216688 p) (Prenex' _216688 q))) /\ (forall x : N, forall p : form, (Prenex' _216688 (FAll x p)) = (FAll x (Prenex' _216688 p)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof.
  total_align. simpl. unfold Prenex_left. if_intro=>[_|H].
  - generalize (Prenex p). clear p. intro f. funelim (Prenex_left0 f (Prenex q)) ;
    try now simp Prenex_left1 ; unfold Prenex_right ; if_intro ;
    [ reflexivity | intro H' ; destruct (H' (Prenex_def0 q)) ].
    all : simp Prenex_left1 ; now rewrite H.
  - destruct (H (Prenex_def0 p)).
Qed.

(****************************************************************************)
(* Conversion to Skollem form. *)
(****************************************************************************)
Definition Skolem1 (k n : N) (f : form) := formsubst (valmod (n , (Fn k (map V (list_of_set (free_variables (FEx n f)))))) V) f.

Lemma Skolem1_def : Skolem1 = (fun _221139 : N => fun _221140 : N => fun _221141 : form => formsubst (@valmod term N (@pair N term _221140 (Fn _221139 (@List.map N term V (@list_of_set N (free_variables (FEx _221140 _221141)))))) V) _221141).
Proof. exact erefl. Qed.

Equations? Skolems n f k : form by wf (size f) lt :=
Skolems n (FAll m f) k => FAll m (Skolems n f k);
Skolems n (FImp (FAll m (FImp f FFalse)) FFalse) k => Skolems n (Skolem1 (NUMPAIR n k) m f) (N.succ k);
Skolems _ f _ => f.
Proof.
  rewrite/addn/Skolem1 size_formsubst // ; lia.
Qed.

Lemma Skolems_def : Skolems = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> form -> N -> form) (fun Skolems' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> form -> N -> form => forall _221561 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall J : N, forall r : form, forall k : N, (Skolems' _221561 J r k) = (@PPAT form (fun x : N => fun q : form => FAll x (Skolems' _221561 J q k)) (fun x : N => fun q : form => Skolems' _221561 J (Skolem1 (NUMPAIR J k) x q) (N.succ k)) (fun p : form => p) r)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))).
Proof.
  align_ε.
  - intros n f k. funelim (Skolems n f k) ; auto ; now destruct f1.
  - intros f' H H'. ext=> n f k.
    funelim (Skolems n f k) ; rewrite H' ; auto ;
    try destruct f1 ; simpl ; f_equal ; auto.
Qed.

Definition Skopre n f := Skolems n (Prenex f) 0.

Lemma Skopre_def : Skopre = (fun _223892 : N => fun _223893 : form => Skolems _223892 (Prenex _223893) (NUMERAL N0)).
Proof. exact erefl. Qed.

Definition bumpmod {A : Type'} (M : Structure A) : Structure A :=
  (Dom M , ((fun n l => Fun M (NUMSND n) l) , Pred M)).

Lemma bumpmod_def {_195501 : Type'} : (@bumpmod _195501) = (fun _223909 : prod (_195501 -> Prop) (prod (N -> (list _195501) -> _195501) (N -> (list _195501) -> Prop)) => @pair (_195501 -> Prop) (prod (N -> (list _195501) -> _195501) (N -> (list _195501) -> Prop)) (@Dom _195501 _223909) (@pair (N -> (list _195501) -> _195501) (N -> (list _195501) -> Prop) (fun k : N => fun zs : list _195501 => @Fun _195501 _223909 (NUMSND k) zs) (@Pred _195501 _223909))).
Proof. exact erefl. Qed.

Fixpoint bumpterm t :=
  match t with
  | V n => V n
  | Fn n l => Fn (NUMPAIR 0 n) (map bumpterm l) end.

Lemma bumpterm_def : bumpterm = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> term) (fun bumpterm' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> term => forall _223917 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : N, (bumpterm' _223917 (V x)) = (V x)) /\ (forall k : N, forall l : list term, (bumpterm' _223917 (Fn k l)) = (Fn (NUMPAIR (NUMERAL N0) k) (@List.map term term (bumpterm' _223917) l)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).
Proof. term_align. Qed.

Fixpoint bumpform f :=
  match f with
  | FFalse => FFalse
  | Atom n l => Atom n (map bumpterm l)
  | FImp f f' => FImp (bumpform f) (bumpform f')
  | FAll n f => FAll n (bumpform f) end.
  
Lemma bumpform_def : bumpform = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> form -> form) (fun bumpform' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> form -> form => forall _223925 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((bumpform' _223925 FFalse) = FFalse) /\ ((forall p : N, forall l : list term, (bumpform' _223925 (Atom p l)) = (Atom p (@List.map term term bumpterm l))) /\ ((forall q : form, forall r : form, (bumpform' _223925 (FImp q r)) = (FImp (bumpform' _223925 q) (bumpform' _223925 r))) /\ (forall x : N, forall r : form, (bumpform' _223925 (FAll x r)) = (FAll x (bumpform' _223925 r)))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).
Proof. total_align. Qed.

Fixpoint unbumpterm t :=
  match t with
  | V n => V n
  | Fn n l => Fn (NUMSND n) (map unbumpterm l) end.

Lemma unbumpterm_def : unbumpterm = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> term -> term) (fun unbumpterm' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> term -> term => forall _225051 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))), (forall x : N, (unbumpterm' _225051 (V x)) = (V x)) /\ (forall k : N, forall l : list term, (unbumpterm' _225051 (Fn k l)) = (Fn (NUMSND k) (@List.map term term (unbumpterm' _225051) l)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))))).
Proof. term_align. Qed.

Fixpoint unbumpform f :=
  match f with
  | FFalse => FFalse
  | Atom n l => Atom n (map unbumpterm l)
  | FImp f f' => FImp (unbumpform f) (unbumpform f')
  | FAll n f => FAll n (unbumpform f) end.

Lemma unbumpform_def : unbumpform = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> form -> form) (fun unbumpform' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> form -> form => forall _225059 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))), ((unbumpform' _225059 FFalse) = FFalse) /\ ((forall p : N, forall l : list term, (unbumpform' _225059 (Atom p l)) = (Atom p (@List.map term term unbumpterm l))) /\ ((forall q : form, forall r : form, (unbumpform' _225059 (FImp q r)) = (FImp (unbumpform' _225059 q) (unbumpform' _225059 r))) /\ (forall x : N, forall r : form, (unbumpform' _225059 (FAll x r)) = (FAll x (unbumpform' _225059 r)))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))))).
Proof. total_align. Qed.

Definition unbumpmod {A : Type'} (M : Structure A) : Structure A :=
  (Dom M , ((fun n l => Fun M (NUMPAIR 0 n) l) , Pred M)).

Lemma unbumpmod_def {_195825 : Type'} : (@unbumpmod _195825) = (fun _225060 : prod (_195825 -> Prop) (prod (N -> (list _195825) -> _195825) (N -> (list _195825) -> Prop)) => @pair (_195825 -> Prop) (prod (N -> (list _195825) -> _195825) (N -> (list _195825) -> Prop)) (@Dom _195825 _225060) (@pair (N -> (list _195825) -> _195825) (N -> (list _195825) -> Prop) (fun k : N => fun zs : list _195825 => @Fun _195825 _225060 (NUMPAIR (NUMERAL N0) k) zs) (@Pred _195825 _225060))).
Proof. exact erefl. Qed.

Fixpoint NUMLIST l :=
  match l with
  | nil => 0
  | cons a l => NUMPAIR a (NUMLIST l) + 1 end.

Lemma NUMLIST_def : NUMLIST = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list N) -> N) (fun NUMLIST' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list N) -> N => forall _225068 : prod N (prod N (prod N (prod N (prod N (prod N N))))), ((NUMLIST' _225068 (@nil N)) = (NUMERAL N0)) /\ (forall h : N, forall t : list N, (NUMLIST' _225068 (@cons N h t)) = (N.add (NUMPAIR h (NUMLIST' _225068 t)) (NUMERAL (BIT1 N0))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))))))).
Proof. total_align. Qed.

Fixpoint num_of_term t :=
  match t with
  | V n => NUMPAIR 0 n
  | Fn n l => NUMPAIR 1 (NUMPAIR n (NUMLIST (map num_of_term l))) end.

Lemma num_of_term_def : num_of_term = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> term -> N) (fun num_of_term' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> term -> N => forall _225072 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall x : N, (num_of_term' _225072 (V x)) = (NUMPAIR (NUMERAL N0) x)) /\ (forall f : N, forall l : list term, (num_of_term' _225072 (Fn f l)) = (NUMPAIR (NUMERAL (BIT1 N0)) (NUMPAIR f (NUMLIST (@List.map term N (num_of_term' _225072) l)))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))))).
Proof. term_align. Qed.

Fixpoint num_of_form f :=
  match f with
  | FFalse => 1
  | Atom n l => NUMPAIR 1 (NUMPAIR n (NUMLIST (map num_of_term l)))
  | FImp f f' => NUMPAIR 2 (NUMPAIR (num_of_form f) (num_of_form f'))
  | FAll n f => NUMPAIR 3 (NUMPAIR n (num_of_form f)) end.

Lemma num_of_form_def : num_of_form = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> N) (fun num_of_form' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> N => forall _225305 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), ((num_of_form' _225305 FFalse) = (NUMPAIR (NUMERAL N0) (NUMERAL N0))) /\ ((forall p : N, forall l : list term, (num_of_form' _225305 (Atom p l)) = (NUMPAIR (NUMERAL (BIT1 N0)) (NUMPAIR p (NUMLIST (@List.map term N num_of_term l))))) /\ ((forall q : form, forall r : form, (num_of_form' _225305 (FImp q r)) = (NUMPAIR (NUMERAL (BIT0 (BIT1 N0))) (NUMPAIR (num_of_form' _225305 q) (num_of_form' _225305 r)))) /\ (forall x : N, forall q : form, (num_of_form' _225305 (FAll x q)) = (NUMPAIR (NUMERAL (BIT1 (BIT1 N0))) (NUMPAIR x (num_of_form' _225305 q))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))))).
Proof. total_align. Qed.

Definition form_of_num := finv num_of_form. (* Could construct it, but it would require using
                                               NUMFST which is not constructed anyway. *)
Lemma form_of_num_def : form_of_num = (fun _225306 : N => @ε form (fun p : form => (num_of_form p) = _225306)).
Proof. exact erefl. Qed.

Definition SKOLEMIZE f := Skopre (num_of_form (bumpform f) + 1) (bumpform f).

Lemma SKOLEMIZE_def : SKOLEMIZE = (fun _225311 : form => Skopre (N.add (num_of_form (bumpform _225311)) (NUMERAL (BIT1 N0))) (bumpform _225311)).
Proof. exact erefl. Qed.

Definition SKOMOD1 {A : Type'} (f : form) (M : Structure A) : Structure A :=
  if forall v : N -> A, valuation M v -> holds M v f
  then ε (fun M' => Dom M' = Dom M /\ Pred M' = Pred M /\
       (forall n l, Fun M' n l <> Fun M (NUMSND n) l -> exists k, n = (NUMPAIR (num_of_form (bumpform f) + 1) k)) /\ 
       interpretation (language [set (SKOLEMIZE f)]) M' /\
       (forall v : N -> A, valuation M' v -> holds M' v (SKOLEMIZE f)))
  else (Dom M , ((fun n l => ε (fun a : A => IN a (Dom M))), Pred M)).

Lemma SKOMOD1_def {A : Type'} : (@SKOMOD1 A) = (fun _226669 : form => fun _226670 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @COND (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (forall v : N -> A, (@valuation A _226670 v) -> @holds A _226670 v _226669) (@ε (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (fun M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => ((@Dom A M') = (@Dom A (@bumpmod A _226670))) /\ (((@Pred A M') = (@Pred A (@bumpmod A _226670))) /\ ((forall g : N, forall zs : list A, (~ ((@Fun A M' g zs) = (@Fun A (@bumpmod A _226670) g zs))) -> exists l : N, g = (NUMPAIR (N.add (num_of_form (bumpform _226669)) (NUMERAL (BIT1 N0))) l)) /\ ((@interpretation A (language (@INSERT form (SKOLEMIZE _226669) (@set0 form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (SKOLEMIZE _226669))))))) (@pair (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) (@Dom A _226670) (@pair (N -> (list A) -> A) (N -> (list A) -> Prop) (fun g : N => fun zs : list A => @ε A (fun a : A => @IN A a (@Dom A _226670))) (@Pred A _226670)))).
Proof.
  ext=> f M. rewrite/SKOMOD1. if_intro=>_ ; last by [].
  f_equal. funext => M'. repeat f_equal. now ssimpl.
Qed.

Definition SKOMOD {A : Type'} (M : Structure A) : Structure A :=
  (Dom M,
  ((fun n l => match (NUMFST n) with
  | 0 => Fun M (NUMSND n) l
  | _ => Fun (SKOMOD1 (unbumpform (form_of_num (N.pred (NUMFST n)))) M) n l end),
  Pred M)).

Lemma SKOMOD_def {_196878 : Type'} : (@SKOMOD _196878) = (fun _226687 : prod (_196878 -> Prop) (prod (N -> (list _196878) -> _196878) (N -> (list _196878) -> Prop)) => @pair (_196878 -> Prop) (prod (N -> (list _196878) -> _196878) (N -> (list _196878) -> Prop)) (@Dom _196878 _226687) (@pair (N -> (list _196878) -> _196878) (N -> (list _196878) -> Prop) (fun g : N => fun zs : list _196878 => @COND _196878 ((NUMFST g) = (NUMERAL N0)) (@Fun _196878 _226687 (NUMSND g) zs) (@Fun _196878 (@SKOMOD1 _196878 (unbumpform (form_of_num (N.pred (NUMFST g)))) _226687) g zs)) (@Pred _196878 _226687))).
Proof.
  ext=> M. unfold SKOMOD. repeat f_equal.
  ext=> n l. if_intro ; induction (NUMFST n) ; auto.
  inversion 1. contradiction.
Qed.

Fixpoint specialize f :=
  match f with
  | FAll n f => specialize f
  | _ => f end.

Lemma specialize_def : specialize = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> form -> form) (fun specialize' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> form -> form => forall _227760 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))), ((specialize' _227760 FFalse) = FFalse) /\ ((forall p : N, forall l : list term, (specialize' _227760 (Atom p l)) = (Atom p l)) /\ ((forall q : form, forall r : form, (specialize' _227760 (FImp q r)) = (FImp q r)) /\ (forall x : N, forall r : form, (specialize' _227760 (FAll x r)) = (specialize' _227760 r))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))))))).
Proof. total_align. Qed.

Definition SKOLEM f := specialize (SKOLEMIZE f).

Lemma SKOLEM_def : SKOLEM = (fun _227960 : form => specialize (SKOLEMIZE _227960)).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* Propositional calculus *)
(*****************************************************************************)

(* Representing Propositional calculus in FOL by considering that every atomic formula
   and every universally quantified formula is simply a propositional variable. *)

Fixpoint pholds (TrueVar : set form) (f : form) : Prop :=
  match f with
  | FFalse => False
  | FImp f f' => pholds TrueVar f -> pholds TrueVar f'
  | _ => TrueVar f end.

Lemma pholds_def : pholds = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> form -> Prop) (fun pholds' : (prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> form -> Prop => forall _228069 : prod N (prod N (prod N (prod N (prod N N)))), (forall v : form -> Prop, (pholds' _228069 v FFalse) = False) /\ ((forall v : form -> Prop, forall p : N, forall l : list term, (pholds' _228069 v (Atom p l)) = (v (Atom p l))) /\ ((forall q : form, forall v : form -> Prop, forall r : form, (pholds' _228069 v (FImp q r)) = ((pholds' _228069 v q) -> pholds' _228069 v r)) /\ (forall v : form -> Prop, forall x : N, forall q : form, (pholds' _228069 v (FAll x q)) = (v (FAll x q)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof. total_align. Qed.

Definition psatisfies s s' := forall f, IN f s' -> pholds s f.
Lemma psatisfies_def : psatisfies = (fun _228082 : form -> Prop => fun _228083 : form -> Prop => forall p : form, (@IN form p _228083) -> pholds _228082 p).
Proof. exact erefl. Qed.

Definition psatisfiable s' := exists s, psatisfies s s'.

Lemma psatisfiable_def : psatisfiable = (fun _228094 : form -> Prop => exists v : form -> Prop, forall p : form, (@IN form p _228094) -> pholds v p).
Proof. exact erefl. Qed.

Definition finsat (s : set form) : Prop :=
  forall F, subset F s /\ finite_set F -> psatisfiable F.

Lemma finsat_def : finsat = (fun _228106 : form -> Prop => forall B : form -> Prop, ((@subset form B _228106) /\ (@finite_set form B)) -> psatisfiable B).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* canonical models *)
(*****************************************************************************)

Inductive terms (functions : set (prod N N)) : term -> Prop :=
| terms_V : forall n, terms functions (V n)
| terms_Fn : forall n l, functions (n , lengthN l) ->
    Forall (terms functions) l -> terms functions (Fn n l).

Lemma terms_def : terms = (fun fns : (prod N N) -> Prop => fun a : term => forall terms' : term -> Prop, (forall a' : term, ((exists x : N, a' = (V x)) \/ (exists f : N, exists l : list term, (a' = (Fn f l)) /\ ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term terms' l)))) -> terms' a') -> terms' a).
Proof.
  ssimpl. ext=> functions t H.
  intros P' H'. induction t ; apply H'.
  - now left;exists n.
  - right. exists n. exists l. split;auto.
    inversion_clear H. split;auto. clear H1.
    induction l;auto. inversion_clear H0. inversion_clear H2.
    apply Forall_cons. now apply H. now apply IHl.
  - apply H ; clear H ; clear t ; intros t H.
    destruct H as [(n , eq) | (n , (l , (eq , (H , H'))))] ; rewrite eq.
    + exact (terms_V functions n).
    + exact (terms_Fn H H').
Qed.

Definition canonical (L : prod (set (prod N N)) (set (prod N N)))
  (M : Structure term) := (Dom M = terms (fst L) /\ (forall n, Fun M n = Fn n)).

Lemma canonical_def : canonical = (fun _230099 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _230100 : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) => ((@Dom term _230100) = (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _230099))) /\ (forall f : N, (@Fun term _230100 f) = (Fn f))).
Proof. exact erefl. Qed.

Lemma prop_of_model_def {_199383 : Type'} : holds = (fun _230111 : prod (_199383 -> Prop) (prod (N -> (list _199383) -> _199383) (N -> (list _199383) -> Prop)) => fun _230112 : N -> _199383 => fun _230113 : form => @holds _199383 _230111 _230112 _230113).
Proof. exact erefl. Qed.

Definition canon_of_prop (L : prod (set (prod N N)) (set (prod N N)))
  (Predval : form -> Prop)  := (terms (fst L), (Fn, fun (p : N) (l : list term) => Predval (Atom p l))).

Lemma canon_of_prop_def : canon_of_prop = (fun _230132 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _230133 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _230132)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun l : list term => _230133 (Atom p l)))).
Proof. exact erefl. Qed.

Definition term_of_num := finv num_of_term.

Lemma term_of_num_def : term_of_num = (fun _230920 : N => @ε term (fun t : term => (num_of_term t) = _230920)).
Proof. exact erefl. Qed.

Definition LOWMOD (M : Structure term) : Structure N := ([set num_of_term t | t in Dom M], 
  (fun n l => num_of_term (Fun M n (map term_of_num l)),
  fun n l => Pred M n (map term_of_num l))).

Lemma LOWMOD_def : LOWMOD = (fun _230925 : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) => @pair (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) (@GSPEC N (fun GEN_PVAR_501 : N => exists t : term, @SETSPEC N GEN_PVAR_501 (@IN term t (@Dom term _230925)) (num_of_term t))) (@pair (N -> (list N) -> N) (N -> (list N) -> Prop) (fun g : N => fun zs : list N => num_of_term (@Fun term _230925 g (@List.map N term term_of_num zs))) (fun p : N => fun zs : list N => @Pred term _230925 p (@List.map N term term_of_num zs)))).
Proof. by ext=>* ; ssimpl. Qed.

(*****************************************************************************)
(* herbrand.ml *)
(*****************************************************************************)

Inductive herbase (functions : set (prod N N)) : term -> Prop :=
| herbase_const : (~ exists k, IN (k,0) functions) -> herbase functions (V 0)
| herbase_Fn : forall n l, IN (n , lengthN l) functions ->
    Forall (herbase functions) l -> herbase functions (Fn n l).

Lemma herbase_def : herbase = (fun fns : (prod N N) -> Prop => fun a : term => forall herbase' : term -> Prop, (forall a' : term, (((a' = (V (NUMERAL N0))) /\ (~ (exists c : N, @IN (prod N N) (@pair N N c (NUMERAL N0)) fns))) \/ (exists f : N, exists l : list term, (a' = (Fn f l)) /\ ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term herbase' l)))) -> herbase' a') -> herbase' a).
Proof.
  ext=> functions t H.
  intros P' H'. induction t ; apply H'.
  - inversion H. now left.
  - right. exists n. exists l.
    inversion_clear H. repeat split;auto.
    clear H1. induction l;auto. inversion_clear H0.
    inversion_clear H2. apply Forall_cons;auto.
  - apply H ; clear H ; clear t ; intros t H.
    destruct H as [(eq , H) | (n , (l , (eq , (H , H'))))] ; rewrite eq.
    + exact (herbase_const H).
    + exact (herbase_Fn H H').
Qed.

Definition herbrand (L : prod (set (prod N N)) (set (prod N N)))
  (M : Structure term) := (Dom M = herbase (fst L) /\ (forall n, Fun M n = Fn n)).

Lemma herbrand_def : herbrand = (fun _232129 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _232130 : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) => ((@Dom term _232130) = (herbase (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _232129))) /\ (forall f : N, (@Fun term _232130 f) = (Fn f))).
Proof. exact erefl. Qed.

Definition herbrand_of_prop (L : prod (set (prod N N)) (set (prod N N)))
  (Predval : form -> Prop)  := (herbase (fst L), (Fn, fun (p : N) (l : list term) => Predval (Atom p l))).

Lemma herbrand_of_prop_def : herbrand_of_prop = (fun _232334 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _232335 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (herbase (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _232334)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun l : list term => _232335 (Atom p l)))).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* fole.ml : FOL with defined equality  *)
(*****************************************************************************)

Definition FEq t t' := Atom 0 (cons t (cons t' nil)).

Lemma FEq_def : FEq = (fun _232588 : term => fun _232589 : term => Atom (NUMERAL N0) (@cons term _232588 (@cons term _232589 (@nil term)))).
Proof. exact erefl. Qed.

Definition uclose f := fold_right_with_perm_args FAll (list_of_set (free_variables f)) f.

Lemma uclose_def : uclose = (fun _232600 : form => @fold_right_with_perm_args N form FAll (@list_of_set N (free_variables _232600)) _232600).
Proof. exact erefl. Qed.

Definition normal {A : Type'} functions (M : Structure A) :=
  (forall t t' v, valuation M v /\ IN t (terms functions) /\ IN t' (terms functions) ->
  holds M v (FEq t t') <-> (termval M v t = termval M v t')).

Lemma normal_def {_201755 : Type'} : (@normal _201755) = (fun _232605 : (prod N N) -> Prop => fun _232606 : prod (_201755 -> Prop) (prod (N -> (list _201755) -> _201755) (N -> (list _201755) -> Prop)) => forall s : term, forall t : term, forall v : N -> _201755, ((@valuation _201755 _232606 v) /\ ((@IN term s (terms _232605)) /\ (@IN term t (terms _232605)))) -> (@holds _201755 _232606 v (FEq s t)) = ((@termval _201755 _232606 v s) = (@termval _201755 _232606 v t))).
Proof.
  ext=> functions M H t t' v H' ; apply H in H'.
  now apply propext. now rewrite H'.
Qed.

Definition Varpairs n := (* could be defined without nat if needed, like repeatN but harder. *)
  let fix Varpairsnat n :=
    match n with
    | O => nil
    | S n => (V (N.double (N.of_nat n)) , V (N.succ_double (N.of_nat n))) :: (Varpairsnat n) end
  in Varpairsnat (N.to_nat n).

Lemma Varpairs_def : Varpairs = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list (prod term term)) (fun Varpairs' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list (prod term term) => forall _232620 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((Varpairs' _232620 (NUMERAL N0)) = (@nil (prod term term))) /\ (forall n : N, (Varpairs' _232620 (N.succ n)) = (@cons (prod term term) (@pair term term (V (N.mul (NUMERAL (BIT0 (BIT1 N0))) n)) (V (N.add (N.mul (NUMERAL (BIT0 (BIT1 N0))) n) (NUMERAL (BIT1 N0))))) (Varpairs' _232620 n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))).
Proof.
  unfold NUMERAL. N_rec_align. destruct n.
  reflexivity. unfold Varpairs.
  rewrite Nnat.N2Nat.inj_succ.
  now rewrite Nnat.N2Nat.id.
Qed.

Definition FEqc c := FEq (fst c) (snd c).

Lemma FEqc_exists : FEqc = ε (fun f : term * term -> form => forall s t : term, f (s, t) = FEq s t).
Proof.
  align_ε. reflexivity.
  intros Eq' _ H'. ext=> [[t t']]. now rewrite H'.
Qed.

Definition Eqaxiom_Func (f : prod N N) := uclose
  (FImp (fold_right FAnd FTrue (map FEqc (Varpairs (snd f))))
    (FEq (Fn (fst f) (map fst (Varpairs (snd f)))) (Fn (fst f) (map snd (Varpairs (snd f)))))).

Lemma Eqaxiom_Func_def : Eqaxiom_Func = (fun _232621 : prod N N => uclose (FImp (@fold_right_with_perm_args form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs (@snd N N _232621))) FTrue) (FEq (Fn (@fst N N _232621) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _232621)))) (Fn (@fst N N _232621) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _232621))))))).
Proof.
  unfold Eqaxiom_Func. now rewrite FEqc_exists.
Qed.

Definition Eqaxiom_Pred (P : prod N N) := uclose
  (FImp (fold_right FAnd FTrue (map FEqc (Varpairs (snd P))))
    (FEquiv (Atom (fst P) (map fst (Varpairs (snd P)))) (Atom (fst P) (map snd (Varpairs (snd P)))))).

Lemma Eqaxiom_Pred_def : Eqaxiom_Pred = (fun _232630 : prod N N => uclose (FImp (@fold_right_with_perm_args form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs (@snd N N _232630))) FTrue) (FEquiv (Atom (@fst N N _232630) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _232630)))) (Atom (@fst N N _232630) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _232630))))))).
Proof.
  unfold Eqaxiom_Pred. now rewrite FEqc_exists.
Qed.

Definition FEq_refl := FAll 0 (FEq (V 0) (V 0)).

Definition FEq_trans_sym := FAll 0 (FAll 1 (FAll 2 (FImp (FEq (V 0) (V 1))
 (FImp (FEq (V 2) (V 1)) (FEq (V 0) (V 2)))))).

Definition Eqaxioms (L : prod (set (prod N N)) (set (prod N N))) :=
  FEq_refl |` (FEq_trans_sym |` [set Eqaxiom_Func f | f in fst L] `|`
    [set Eqaxiom_Pred p | p in snd L]).

Lemma Eqaxioms_def : Eqaxioms = (fun _232639 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => @setU form (@INSERT form (FAll (NUMERAL N0) (FEq (V (NUMERAL N0)) (V (NUMERAL N0)))) (@set0 form)) (@setU form (@INSERT form (FAll (NUMERAL N0) (FAll (NUMERAL (BIT1 N0)) (FAll (NUMERAL (BIT0 (BIT1 N0))) (FImp (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT1 N0)))) (FImp (FEq (V (NUMERAL (BIT0 (BIT1 N0)))) (V (NUMERAL (BIT1 N0)))) (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT0 (BIT1 N0)))))))))) (@set0 form)) (@setU form (@GSPEC form (fun GEN_PVAR_508 : form => exists fa : prod N N, @SETSPEC form GEN_PVAR_508 (@IN (prod N N) fa (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _232639)) (Eqaxiom_Func fa))) (@GSPEC form (fun GEN_PVAR_509 : form => exists pa : prod N N, @SETSPEC form GEN_PVAR_509 (@IN (prod N N) pa (@snd ((prod N N) -> Prop) ((prod N N) -> Prop) _232639)) (Eqaxiom_Pred pa)))))).
Proof.
  by ext 1 =>L ; unfold Eqaxioms ; ssimpl ; do 4 rewrite setUA.
Qed.

(*****************************************************************************)
(* retval : bool with a 3rd possibility, exception *)
(*****************************************************************************)

Inductive retval := TT | FF | Exception.

HB.instance Definition _ := is_Type' TT.

Definition _dest_retval (v : retval) : recspace Prop :=
match v with
| TT => CONSTR 0 (ε (fun _ => True)) (fun _ => BOTTOM)
| FF => CONSTR 1 (ε (fun _ => True)) (fun _ => BOTTOM)
| Exception => CONSTR 2 (ε (fun _ => True)) (fun _ => BOTTOM) end.

Definition _mk_retval := finv _dest_retval.

Lemma _mk_dest_retval : forall v, (_mk_retval (_dest_retval v)) = v.
Proof.
  _mk_dest_inductive.
Qed.

Lemma _dest_mk_retval : forall (r : recspace Prop), ((fun a : recspace Prop => forall retval' : (recspace Prop) -> Prop, (forall a' : recspace Prop, ((a' = (@CONSTR Prop (NUMERAL N0) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))) \/ ((a' = (@CONSTR Prop (N.succ (NUMERAL N0)) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))) \/ (a' = (@CONSTR Prop (N.succ (N.succ (NUMERAL N0))) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))))) -> retval' a') -> retval' a) r) = ((_dest_retval (_mk_retval r)) = r).
Proof.
  intro r. _dest_mk_inductive.
  - now exists TT.
  - now exists FF.
  - now exists Exception.
Qed.

Lemma TT_def : TT = (_mk_retval (@CONSTR Prop (NUMERAL N0) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))).
Proof. symmetry. exact (_mk_dest_retval TT). Qed.

Lemma FF_def : FF = (_mk_retval (@CONSTR Prop (N.succ (NUMERAL N0)) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))).
Proof. symmetry. exact (_mk_dest_retval FF). Qed.

Lemma Exception_def : Exception = (_mk_retval (@CONSTR Prop (N.succ (N.succ (NUMERAL N0))) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))).
Proof. symmetry. exact (_mk_dest_retval Exception). Qed.

(*****************************************************************************)
(* Logic/unif.ml *)
(*****************************************************************************)

Definition OCC (env : list (prod N term)) n m :=
  exists t, In (n, t) env /\ IN m (free_variables_term t).

Lemma OCC_def : OCC = (fun _259304 : list (prod N term) => fun _259305 : N => fun _259306 : N => exists t : term, (@List.In (prod N term) (@pair N term _259305 t) _259304) /\ (@IN N _259306 (free_variables_term t))).
Proof. exact erefl. Qed.

Definition LOOPFREE l := forall n, ~ Relation_Operators.clos_trans N (OCC l) n n.

Lemma LOOPFREE_def : LOOPFREE = (fun _259325 : list (prod N term) => forall z : N, ~ (@Relation_Operators.clos_trans N (OCC _259325) z z)).
Proof. exact erefl. Qed.

(* Inductive loopcheck (env : list (prod N term)) : N -> term -> Prop :=
  | loopcheck_isfreein : forall n t, IN n (free_variables_term t) -> loopcheck env n t
  | loopcheck_rec : forall n t n' t', IN n' (free_variables_term t) ->
                    In (n,t') env -> loopcheck env n' t' -> loopcheck env n t. *)

(* come back with a better tactic for partial functions *)

Definition rightsubst (c c' : prod N term) := (fst c',termsubst (valmod c V) (snd c')).

Lemma rightsubst_def : rightsubst = (fun _260241 : prod N term => fun _260242 : prod N term => @pair N term (@fst N term _260242) (termsubst (fun z : N => @COND term (z = (@fst N term _260241)) (@snd N term _260241) (V z)) (@snd N term _260242))).
Proof. exact erefl. Qed.

Fixpoint list_rightsubst l c' :=
  match l with
  | nil => c'
  | c::l => rightsubst c (list_rightsubst l c') end.

Fixpoint lsubst l :=
  match l with
  | nil => nil
  | c::l => (list_rightsubst (lsubst l) c)::(lsubst l) end.

Fixpoint self_rightsubst l :=
  match l with
  | nil => nil
  | c::l => let c' := list_rightsubst (lsubst l) c in
            c'::(map (rightsubst c') (self_rightsubst l)) end.

Definition SOLVE l l' := let l'' := rev l' in
  (self_rightsubst l'') ++ (map (list_rightsubst (lsubst l'')) l).

Definition SOLVEC c := SOLVE (fst c) (snd c).

Lemma appcons_appapp {A : Type} (a:A) l l' : (l++a::nil)++l' = l++a::l'.
Proof.
  induction l;auto. repeat rewrite <- app_comm_cons. now f_equal.
Qed.

Lemma list_rightsubst_tail c l c' :
  list_rightsubst (l++c::nil) c' = list_rightsubst l (rightsubst c c').
Proof.
  induction l;auto. simpl. now rewrite IHl.
Qed.

Lemma lsubst_tail l c :
  lsubst (l++c::nil) =
  lsubst (map (rightsubst c) l) ++ c::nil.
Proof.
  induction l;auto. simpl. now rewrite IHl list_rightsubst_tail.
Qed.

Lemma self_rightsubst_tail l c :
  self_rightsubst (l ++ c::nil) = let l' := map (rightsubst c) l in
  self_rightsubst l' ++ (list_rightsubst (lsubst l') c) :: nil.
Proof.
  induction l;auto.
  simpl. rewrite IHl.
  now rewrite map_last lsubst_tail list_rightsubst_tail.
Qed.

Lemma SOLVEC_def : SOLVEC = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (prod (list (prod N term)) (list (prod N term))) -> list (prod N term)) (fun SOLVE' : (prod N (prod N (prod N (prod N (prod N N))))) -> (prod (list (prod N term)) (list (prod N term))) -> list (prod N term) => forall _260267 : prod N (prod N (prod N (prod N (prod N N)))), forall pr : prod (list (prod N term)) (list (prod N term)), (SOLVE' _260267 pr) = (@COND (list (prod N term)) ((@snd (list (prod N term)) (list (prod N term)) pr) = (@nil (prod N term))) (@fst (list (prod N term)) (list (prod N term)) pr) (SOLVE' _260267 (@pair (list (prod N term)) (list (prod N term)) (@cons (prod N term) (@mappings.hd (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr)) (@List.map (prod N term) (prod N term) (rightsubst (@mappings.hd (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr))) (@fst (list (prod N term)) (list (prod N term)) pr))) (@List.map (prod N term) (prod N term) (rightsubst (@mappings.hd (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr))) (@mappings.tl (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof.
  align_ε.
  - intros (l,l'). simpl. if_list. destruct l'. apply map_id.
    unfold SOLVEC. simpl. unfold SOLVE. rewrite <- map_rev.
    simpl. rewrite self_rightsubst_tail. simpl.
    rewrite (appcons_appapp (list_rightsubst (lsubst (map (rightsubst p) (rev l'))) p)).
    do 2 f_equal. induction l;auto. simpl.
    now rewrite IHl lsubst_tail list_rightsubst_tail.
  - intros f' H H'. ext => [[l l']]. replace l' with (map (list_rightsubst nil) l').
    + generalize (nil (T := N*term)). revert l.
      induction l' ; intros l lsubst ; simpl ; rewrite H H' ;
      do 2 if_list ; simpl. reflexivity.
      rewrite map_map. replace (fun x => rightsubst (list_rightsubst lsubst a) (list_rightsubst lsubst x))
      with (fun x => list_rightsubst ((list_rightsubst lsubst a)::lsubst) x).
      apply IHl'. reflexivity.
    + induction l'. reflexivity. simpl. now f_equal.
Qed.

Lemma SOLVE_def : SOLVE = (fun _260268 : list (prod N term) => fun _260269 : list (prod N term) => SOLVEC (@pair (list (prod N term)) (list (prod N term)) _260268 _260269)).
Proof. exact erefl. Qed.

Definition CONFLICTFREE (l : list (N*term)) :=
  forall n, lengthN (filter (fun c => fst c = n) l) <= 1.

Lemma CONFLICTFREE_def : CONFLICTFREE = (fun _260280 : list (prod N term) => forall x : N, N.le (@lengthN (prod N term) (@filter (prod N term) (@ε ((prod N term) -> Prop) (fun f : (prod N term) -> Prop => forall y : N, forall s : term, @eq Prop (f (@pair N term y s)) (y = x))) _260280)) (NUMERAL (BIT1 N0))).
Proof.
  unfold CONFLICTFREE. funext => l.
  apply (f_equal (fun f => forall n : N, lengthN (filter (f n) l) <=1)).
  ext => n c. f_equal. generalize c. apply ext_fun. align_ε. reflexivity.
  intros f' H H'. funext=> [[n' t]]. now rewrite H'.
Qed.

(* again, a difficult partial function. *) 
Definition istriv : (list (prod N term)) -> N -> term -> retval := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval) (fun istriv' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval => forall _262675 : prod N (prod N (prod N (prod N (prod N N)))), forall env : list (prod N term), forall x : N, ((LOOPFREE env) /\ (CONFLICTFREE env)) -> forall t : term, (istriv' _262675 env x t) = (@COND retval (t = (V x)) TT (@COND retval (exists y : N, (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env))) (istriv' _262675 env x (@assoc N term (@ε N (fun y : N => (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env)))) env)) (@COND retval (@IN N x (free_variables_term t)) Exception (@COND retval (exists y : N, exists s : term, (@IN N y (free_variables_term t)) /\ ((@List.In (prod N term) (@pair N term y s) env) /\ (~ ((istriv' _262675 env x s) = FF)))) Exception FF))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))).
Lemma istriv_def : istriv = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval) (fun istriv' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval => forall _262675 : prod N (prod N (prod N (prod N (prod N N)))), forall env : list (prod N term), forall x : N, ((LOOPFREE env) /\ (CONFLICTFREE env)) -> forall t : term, (istriv' _262675 env x t) = (@COND retval (t = (V x)) TT (@COND retval (exists y : N, (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env))) (istriv' _262675 env x (@assoc N term (@ε N (fun y : N => (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env)))) env)) (@COND retval (@IN N x (free_variables_term t)) Exception (@COND retval (exists y : N, exists s : term, (@IN N y (free_variables_term t)) /\ ((@List.In (prod N term) (@pair N term y s) env) /\ (~ ((istriv' _262675 env x s) = FF)))) Exception FF))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof. exact erefl. Qed.

Definition EQV {A : Type} l (a : A) n := In (a, V n) l.

Lemma EQV_def {_208558 : Type'} : (@EQV _208558) = (fun _263122 : list (prod _208558 term) => fun _263123 : _208558 => fun _263124 : N => @List.In (prod _208558 term) (@pair _208558 term _263123 (V _263124)) _263122).
Proof. exact erefl. Qed.

Definition SUB1 t t' := exists n l, t' = Fn n l /\ In t l.

Lemma SUB1_def : SUB1 = (fun _267259 : term => fun _267260 : term => exists f : N, exists args : list term, (_267260 = (Fn f args)) /\ (@List.In term _267259 args)).
Proof. exact erefl. Qed.

Definition termcases {A : Type} caseV caseFn t : A :=
  match t with
  | V n => caseV n
  | Fn n l => caseFn n l end.

Lemma termcases_def {_209078 : Type'} : (@termcases _209078) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> _209078) -> (N -> (list term) -> _209078) -> term -> _209078) (fun termcases' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (N -> _209078) -> (N -> (list term) -> _209078) -> term -> _209078 => forall _267400 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall cf : N -> (list term) -> _209078, forall cv : N -> _209078, forall v : N, (termcases' _267400 cv cf (V v)) = (cv v)) /\ (forall cv : N -> _209078, forall cf : N -> (list term) -> _209078, forall f : N, forall args : list term, (termcases' _267400 cv cf (Fn f args)) = (cf f args))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))).
Proof. term_align. Qed.

Definition tpcases {A : Type} caseFn_Fn caseV caseFn_V c : A :=
    match fst c with
    | V n => caseV n (snd c)
    | Fn n l => match snd c with
      | V n' => caseFn_V n l n'
      | Fn n' l' => caseFn_Fn n l n' l' end end.

Lemma tpcases_def {_209138 : Type'} : (@tpcases _209138) = (fun _267401 : N -> (list term) -> N -> (list term) -> _209138 => fun _267402 : N -> term -> _209138 => fun _267403 : N -> (list term) -> N -> _209138 => fun _267404 : prod term term => @termcases _209138 (fun v1 : N => @termcases _209138 (fun v2 : N => _267402 v1 (V v2)) (fun f2 : N => fun args2 : list term => _267402 v1 (Fn f2 args2)) (@snd term term _267404)) (fun f1 : N => fun args1 : list term => @termcases _209138 (fun v2 : N => _267403 f1 args1 v2) (fun f2 : N => fun args2 : list term => _267401 f1 args1 f2 args2) (@snd term term _267404)) (@fst term term _267404)).
Proof. ext => f f' f'' [t t']. now induction t'. Qed.

Definition MLEFT c :=
  match c with (env,eqs) =>
    card (setU (free_variables_term (Fn 0 (map fst eqs)))
    (setU (free_variables_term (Fn 0 (map snd eqs)))
    (setU (free_variables_term (Fn 0 (map snd env)))
    (free_variables_term (Fn 0 (map (Basics.compose V fst) env)))))) -
    card (free_variables_term (Fn 0 (map (Basics.compose V fst) env))) end.

Lemma MLEFT_def : MLEFT = (fun _267440 : prod (list (prod N term)) (list (prod term term)) => N.sub (@card N (@setU N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod term term) term (@fst term term) (@snd (list (prod N term)) (list (prod term term)) _267440)))) (@setU N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod term term) term (@snd term term) (@snd (list (prod N term)) (list (prod term term)) _267440)))) (@setU N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod N term) term (@snd N term) (@fst (list (prod N term)) (list (prod term term)) _267440)))) (free_variables_term (Fn (NUMERAL N0) (@List.map (prod N term) term (@Basics.compose (prod N term) N term V (@fst N term)) (@fst (list (prod N term)) (list (prod term term)) _267440)))))))) (@card N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod N term) term (@Basics.compose (prod N term) N term V (@fst N term)) (@fst (list (prod N term)) (list (prod term term)) _267440)))))).
Proof. ext=> [[env eqs]]. reflexivity. Qed.

Definition CRIGHT c c' := match c,c' with (env', eqs'),(env, eqs) =>
  (LOOPFREE env /\
   env' = env /\
   ((exists (f : N) (args1 args2 : list term) (oth : list (term * term)),
       lengthN args1 = lengthN args2 /\
       eqs = (Fn f args1, Fn f args2) :: oth /\ eqs' = zip args1 args2 ++ oth) \/
    (exists (x : N) (t : term) (oth : list (term * term)),
       eqs = (V x, t) :: oth /\
       (In x (map fst env) /\ eqs' = (assoc x env, t) :: oth \/
        ~ In x (map fst env) /\ istriv env x t = TT /\ eqs' = oth)) \/
    (exists (x f : N) (args : list term) (oth : list (term * term)),
       eqs = (Fn f args, V x) :: oth /\ eqs' = (V x, Fn f args) :: oth))) end. 

Lemma CRIGHT_def : CRIGHT = (fun _267449 : prod (list (prod N term)) (list (prod term term)) => fun _267450 : prod (list (prod N term)) (list (prod term term)) => (LOOPFREE (@fst (list (prod N term)) (list (prod term term)) _267450)) /\ (((@fst (list (prod N term)) (list (prod term term)) _267449) = (@fst (list (prod N term)) (list (prod term term)) _267450)) /\ ((exists f : N, exists args1 : list term, exists args2 : list term, exists oth : list (prod term term), ((@lengthN term args1) = (@lengthN term args2)) /\ (((@snd (list (prod N term)) (list (prod term term)) _267450) = (@cons (prod term term) (@pair term term (Fn f args1) (Fn f args2)) oth)) /\ ((@snd (list (prod N term)) (list (prod term term)) _267449) = (@app (prod term term) (@zip term term args1 args2) oth)))) \/ ((exists x : N, exists t : term, exists oth : list (prod term term), ((@snd (list (prod N term)) (list (prod term term)) _267450) = (@cons (prod term term) (@pair term term (V x) t) oth)) /\ (((@List.In N x (@List.map (prod N term) N (@fst N term) (@fst (list (prod N term)) (list (prod term term)) _267450))) /\ ((@snd (list (prod N term)) (list (prod term term)) _267449) = (@cons (prod term term) (@pair term term (@assoc N term x (@fst (list (prod N term)) (list (prod term term)) _267450)) t) oth))) \/ ((~ (@List.In N x (@List.map (prod N term) N (@fst N term) (@fst (list (prod N term)) (list (prod term term)) _267450)))) /\ (((istriv (@fst (list (prod N term)) (list (prod term term)) _267450) x t) = TT) /\ ((@snd (list (prod N term)) (list (prod term term)) _267449) = oth))))) \/ (exists x : N, exists f : N, exists args : list term, exists oth : list (prod term term), ((@snd (list (prod N term)) (list (prod term term)) _267450) = (@cons (prod term term) (@pair term term (Fn f args) (V x)) oth)) /\ ((@snd (list (prod N term)) (list (prod term term)) _267449) = (@cons (prod term term) (@pair term term (V x) (Fn f args)) oth))))))).
Proof. funext=> [[env' eqs'] [env eqs]]. reflexivity. Qed.

Definition CALLORDER c' c :=
  MEASURE MLEFT c' c \/ CRIGHT c' c.

Lemma CALLORDER_def : CALLORDER = (fun _267471 : prod (list (prod N term)) (list (prod term term)) => fun _267472 : prod (list (prod N term)) (list (prod term term)) => (@MEASURE (prod (list (prod N term)) (list (prod term term))) MLEFT (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267471) (@snd (list (prod N term)) (list (prod term term)) _267471)) (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267472) (@snd (list (prod N term)) (list (prod term term)) _267472))) \/ (CRIGHT (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267471) (@snd (list (prod N term)) (list (prod term term)) _267471)) (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267472) (@snd (list (prod N term)) (list (prod term term)) _267472)))).
Proof. funext=> [[env' eqs'] [env eqs]]. reflexivity. Qed.

(*****************************************************************************)
(* Trivial definitions *)
(*****************************************************************************)
Definition V_def' : V = V := erefl.
Definition Fn_def' : Fn = Fn := erefl.
Definition FFalse_def' : FFalse = FFalse:= erefl.
Definition FImp_def' : FImp = FImp := erefl.
Definition Atom_def' : Atom = Atom := erefl.
Definition FAll_def' : FAll = FAll := erefl.
Definition TT_def' : TT = TT := erefl.
Definition FF_def' : FF = FF := erefl.
Definition Exception_def' : Exception = Exception := erefl.

Transparent card_eq.