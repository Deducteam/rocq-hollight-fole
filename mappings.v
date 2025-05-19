Require Import HOLLight_Real_With_N.mappings HOLLight.mappings.
Require Import Coq.NArith.BinNat.
Require Import Reals.

Set Bullet Behavior "Strict Subproofs".

(*****************************************************************************)
(* latest versions of automatic alignment tactics *)
(*****************************************************************************)

Lemma cases_equal {A B : Type} {f f' : A -> B} (* splits the goal into cases P and Q *)
  (P Q : A -> Prop) (H : forall a, P a \/ Q a) (a : A) :
  (P a -> f a = f' a) -> (Q a -> f a = f' a) -> f a = f' a.
Proof.
  intros HP HQ. destruct (H a);auto.
Qed.

Record partial_case {A : Type} := (* for a case to be fully automated, one needs to define
                                     it inductively, while also defining its negation recursively,
                                     and proving that they do cover all cases. *)
  { case : A -> Prop ; negcase : A -> Prop ; cover_proof : forall a, case a \/ negcase a }.

Lemma partial_align1_spec1 {U A B : Type'} {uv0 : U} {x : A}
  (Q : A -> Prop) (f : U -> A -> B) (P : (U -> A -> B) -> Prop) :
  P f -> (forall f' uv x, P f ->  P f' -> Q x ->
  f uv x = f' uv x) -> Q x -> f uv0 x = ε P uv0 x.
Proof.
  intros Hf Hunique. apply Hunique;auto.
  apply ε_spec. now exists f.
Qed.

Lemma partial_align1_spec2 {U A B C : Type'} {uv0 : U} {x : B} {y : A}
  (Q : A -> Prop) (f : U -> B -> A -> C) (P : (U -> B -> A -> C) -> Prop) :
  P f -> (forall f' uv x y, P f ->  P f' -> Q y ->
  f uv x y = f' uv x y) -> Q y -> f uv0 x y = ε P uv0 x y.
Proof.
  intros Hf Hunique. apply Hunique;auto.
  apply ε_spec. now exists f.
Qed.

Lemma partial_align1_spec3 {U A B C D : Type'} {uv0 : U} {x : B} {y : C} {z : A}
  (Q : A -> Prop) (f : U -> B -> C -> A -> D) (P : (U -> B -> C -> A -> D) -> Prop) :
  P f -> (forall f' uv x y z, P f ->  P f' -> Q z ->
  f uv x y z = f' uv x y z) -> Q z -> f uv0 x y z = ε P uv0 x y z.
Proof.
  intros Hf Hunique. apply Hunique;auto.
  apply ε_spec. now exists f.
Qed.

Ltac partial_align1_spec P x :=
  match reverse goal with
  | |- P x -> ?f x = ε _ _ x => apply (partial_align1_spec1 P (fun _ => f))
  | |- P x -> ?f _ x = ε _ _ _ x => apply (partial_align1_spec2 P (fun _ => f))
  | |- P x -> ?f _ _ x = ε _ _ _ _ x => apply (partial_align1_spec3 P (fun _ => f)) end ;
  clear x ;
  [ repeat split ; auto
  | let f' := fresh "f'" in
    let uv := fresh "uv" in
    let H := fresh in
    let H' := fresh "H'" in
    let Px := fresh "Px" in
    try intros f' uv y z x H H' Px ;
    try (intros f' uv y x H H' Px ; try ext z) ;
    try (intros f' uv x H H' Px ; try ext y ; try ext z) ;
    induction Px ;
    try full_destruct ;
    repeat match goal with
    H : _ |- _ => rewrite H end ;
    auto ].

Ltac palign_1var c nc cp x :=
  let ncx := fresh in
  apply (cases_equal c nc cp x) ;
  [ partial_align1_spec c x
  | intro ncx ; induction ncx ; auto ;
    try now repeat match goal with H : _ |- _ => rewrite H end ].

Lemma partial_align2_spec12 {U A B : Type'} {uv0 : U} {x y : A}
  (Q : A -> Prop) (f : U -> A -> A -> B) (P : (U -> A -> A -> B) -> Prop) :
  P f -> (forall f' uv x y, P f ->  P f' -> Q x -> Q y ->
  f uv x y = f' uv x y) -> Q x -> Q y -> f uv0 x y = ε P uv0 x y.
Proof.
  intros Hf Hunique. apply Hunique;auto.
  apply ε_spec. now exists f.
Qed.

Lemma partial_align2_spec23 {U A B C : Type'} {uv0 : U} {x : B} {y z : A}
  (Q : A -> Prop) (f : U -> B -> A -> A -> C) (P : (U -> B -> A -> A -> C) -> Prop) :
  P f -> (forall f' uv x y, P f ->  P f' -> Q y -> Q z ->
  f uv x y z = f' uv x y z) -> Q y -> Q z -> f uv0 x y z = ε P uv0 x y z.
Proof.
  intros Hf Hunique. apply Hunique;auto.
  apply ε_spec. now exists f.
Qed.


Ltac partial_align2_spec P x y :=
  match goal with
  | |- P x -> P y -> ?f x y = ε _ _ x y => apply (partial_align2_spec12 P (fun _ => f))
  | |- P x -> P y -> ?f _ x y = ε _ _ _ x y => apply (partial_align2_spec23 P (fun _ => f)) end ;
  try apply (partial_align2_spec12 P) ;
  try apply (partial_align2_spec23 P) ;
  clear x y ;
  [ repeat split ; auto
  | let f' := fresh "f'" in
    let uv := fresh "uv" in
    let z := fresh "z" in
    let H := fresh in
    let H' := fresh "H'" in
    let Px := fresh "Px" in
    let Py := fresh "Py" in
    try intros f' uv z x y H H' Px Py ;
    try (intros f' uv x y H H' Px Py ; try ext z) ;
    induction Px ; induction Py ;
    try full_destruct ;
    repeat match goal with
    H : _ |- _ => rewrite H end ;
    auto ].

Ltac palign_2var c nc cp x y :=
  let Hx := fresh in
  let Hy := fresh in
  apply (cases_equal c nc cp y) ;
  apply (cases_equal c nc cp x) ;
  [ partial_align2_spec c x y
  | intros Hx Hy ; induction Hx ; induction Hy ; auto ;
    try now repeat match goal with H : _ |- _ => rewrite H end ].

Lemma partial_align3_spec {U A B : Type'} {uv0 : U} {x y z : A}
  (Q : A -> Prop) (f : U -> A -> A -> A -> B) (P : (U -> A -> A -> A -> B) -> Prop) :
  P f -> (forall f' uv x y z, P f ->  P f' -> Q x -> Q y -> Q z ->
  f uv x y z = f' uv x y z) -> Q x -> Q y -> Q z -> f uv0 x y z = ε P uv0 x y z.
Proof.
  intros Hf Hunique. apply Hunique;auto.
  apply ε_spec. now exists f.
Qed.


Ltac partial_align3_spec P x y z :=
  match goal with |- P x -> P y -> P z -> ?f x y z = ε _ _ x y z =>
    apply (partial_align3_spec P (fun _ => f)) end ;
  clear x y z ;
  [ repeat split ; auto
  | let f' := fresh "f'" in
    let uv := fresh "uv" in
    let H := fresh in
    let H' := fresh "H'" in
    let Px := fresh "Px" in
    let Py := fresh "Py" in
    let Pz := fresh "Pz" in
    intros f' uv z x y H H' Px Py Pz ;
    induction Px ; induction Py ; induction Pz ;
    try full_destruct ;
    repeat match goal with
    H : _ |- _ => rewrite H end ;
    auto ].

Ltac palign_3var c nc cp x y z :=
  let Hx := fresh in
  let Hy := fresh in
  let Hz := fresh in
  apply (cases_equal c nc cp z) ;
  apply (cases_equal c nc cp y) ;
  apply (cases_equal c nc cp x) ;
  [ partial_align3_spec c x y z
  | intros Hx Hy Hz ; induction Hx ; induction Hy ; induction Hz ; auto ;
    try now repeat match goal with H : _ |- _ => rewrite H end ].


Ltac partial_align pcase := (* pcase must contain two inductive cases over some type A and a proof
                               that these cases cover A. *)
  let c := fresh "c" in
  let nc := fresh "nc" in
  let cp := fresh "cp" in
  set (c := case pcase) ;
  set (nc := negcase pcase) ;
  set (cp := cover_proof pcase) ;
  let x := fresh "x" in
  let y := fresh "y" in
  let z := fresh "z" in
  ext x ;
  ( ext y ;
    ( ext z ; palign_3var c nc cp x y z +
      palign_2var c nc cp y z +
      palign_1var c nc cp z ) +
    palign_2var c nc cp x y +
    palign_1var c nc cp y ) +
  palign_1var c nc cp x.

Ltac breakgoal' H := (* trying to prove [rule1' a' \/ ... \/ rulen' a' -> P' a'] for some a' with hypothesis
                       [P a] after induction on said hypothesis. *)
  let rec breakgoal'' :=
    match goal with
    | |- _ \/ _ => left + right ; breakgoal''
    | x : ?T |- exists _ : ?T, _ => exists x ; breakgoal'' (* the correct x1 ... xn should be directly given
                                                             by the induction on [P a]. *)
    | |- _ /\ _ => (repeat split) ; (try apply H) ; auto ; try assumption ; reflexivity
         (* the reflexivity proves a = f x1 ... xn and therefore assures us that we are
            in the correct disjunctive clause. We cannot be sure of what to do after,
            so we only try tactics dealing with the easiest cases.  *)
    | |- _ => (try now apply H) ; try assumption ; reflexivity
        (* dealing with cases with no subterms. reflexivity is probably useless but
           it's good to have a tactic that fails so that the tactic goes back to trying
           other paths in the disjunction. *)
    end
  in breakgoal''.

Ltac ind_align' :=
  let x := fresh "x" in (* to replace with newer ind_align after the merge *)
  let y := fresh "y" in
  let z := fresh "z" in
  let H := fresh in
  try ext x ; try ext y ; try ext z ; apply prop_ext ; intro H ;
  [ let P' := fresh "P'" in
    let H' := fresh "H'" in
    intros P' H' ; apply H' ; induction H ;
    try breakgoal' H'
  | apply H ; (* applying the HOL-Light definition to the coq version of P itself *)
    clear H ; try clear x ; try clear y ; try clear z ;
    try intros x y z H ; try intros x y H ; try intros x H ;
    full_destruct ; try match goal with
    H : _ |- _ => rewrite H (* not much to do, each clause should be proved with a rule,
                               we just try to rewrite [a = f x1 ... xn] if it exists *)
    end ; try now constructor ].

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
Lemma SPEC_elim {A : Type'} {P : A -> Prop} : GSPEC (fun x => exists x', SETSPEC x (P x') x') = P.
Proof.
  ext x. apply prop_ext ; intro H. destruct H as (x', (HP , e)). now subst x.
  now exists x.
Qed.

Definition IMAGE {A B : Type'} (f : A -> B) (E : Ensemble A) : Ensemble B :=
  fun y => exists x, In E x /\ y = f x.

Lemma IMAGE_def {A B : Type'} : (@IMAGE A B) = (fun _32493 : A -> B => fun _32494 : A -> Prop => @GSPEC B (fun GEN_PVAR_7 : B => exists y : B, @SETSPEC B GEN_PVAR_7 (exists x : A, (@IN A x _32494) /\ (y = (_32493 x))) y)).
Proof.
  ext f E. symmetry. exact SPEC_elim.
Qed.

(* Variant *)
Lemma SPEC_IMAGE {A B : Type'} {f : A -> B} {E : Ensemble A} :
  GSPEC (fun x => exists x', SETSPEC x (IN x' E) (f x')) = IMAGE f E.
Proof. reflexivity. Qed.

Lemma o_def {A B C : Type'} : Basics.compose = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Proof. reflexivity. Qed.

Lemma I_def {A : Type'} : Datatypes.id = (fun x : A => x).
Proof. reflexivity. Qed.

Lemma let_clear {A B} : forall (f : A -> B) x, Basics.apply f x = (let y := x in f y).
Proof. reflexivity. Qed.

Ltac let_clear := repeat rewrite let_clear.

Lemma LET_def {A B : Type'} : Basics.apply = (fun f : A -> B => fun x : A => f x).
Proof. ext f x. reflexivity. Qed.

Lemma LET_END_def {A : Type'} : Datatypes.id = (fun t : A => t).
Proof. reflexivity. Qed.

Lemma UNION_def {A : Type'} : Union = (fun _32385 : A -> Prop => fun _32386 : A -> Prop => @GSPEC A (fun GEN_PVAR_0 : A => exists x : A, @SETSPEC A GEN_PVAR_0 ((@IN A x _32385) \/ (@IN A x _32386)) x)).
Proof.
  ext B C x. rewrite SPEC_elim. apply prop_ext;inversion 1;auto.
  now apply Union_introl. now apply Union_intror.
Qed.

Definition INTERS {A : Type'} : Ensemble (Ensemble A) -> Ensemble A := fun E x => forall y, In E y -> In y x.
Lemma INTERS_def {A : Type'} : INTERS = (fun _32414 : (A -> Prop) -> Prop => @GSPEC A (fun GEN_PVAR_3 : A => exists x : A, @SETSPEC A GEN_PVAR_3 (forall u : A -> Prop, (@IN (A -> Prop) u _32414) -> @IN A x u) x)).
Proof.
  ext E. symmetry. exact SPEC_elim.
Qed.

Lemma DIFF_def {A : Type'} : Setminus = (fun _32419 : A -> Prop => fun _32420 : A -> Prop => @GSPEC A (fun GEN_PVAR_4 : A => exists x : A, @SETSPEC A GEN_PVAR_4 ((@IN A x _32419) /\ (~ (@IN A x _32420))) x)).
Proof.
  ext B C. symmetry. exact SPEC_elim.
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

Fixpoint list_Union {A : Type'} (l : list (A -> Prop)) : A -> Prop :=
  match l with
  | nil => Empty_set
  | cons E l => Union E (list_Union l) end.

Lemma LIST_UNION_def {_184792 : Type'} : list_Union = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> (list (_184792 -> Prop)) -> _184792 -> Prop) (fun LIST_UNION' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) -> (list (_184792 -> Prop)) -> _184792 -> Prop => forall _204636 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))), ((LIST_UNION' _204636 (@nil (_184792 -> Prop))) = (@Ensembles.Empty_set _184792)) /\ (forall h : _184792 -> Prop, forall t : list (_184792 -> Prop), (LIST_UNION' _204636 (@cons (_184792 -> Prop) h t)) = (@Ensembles.Union _184792 h (LIST_UNION' _204636 t)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))))))).
Proof.
  total_align.
Qed.

Fixpoint set_of_list {A : Type'} (l : list A) : A -> Prop :=
  match l with
  | nil => Empty_set
  | cons a l => INSERT a (set_of_list l) end.

Lemma set_of_list_def {A : Type'} : (@set_of_list A) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> (list A) -> A -> Prop) (fun set_of_list' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> (list A) -> A -> Prop => forall _56425 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), ((set_of_list' _56425 (@nil A)) = (@Ensembles.Empty_set A)) /\ (forall h : A, forall t : list A, (set_of_list' _56425 (@cons A h t)) = (@INSERT A h (set_of_list' _56425 t)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).
Proof. total_align. Qed.

Definition list_of_set {A : Type'} (E : Ensemble A) : list A :=
  ε (fun l => set_of_list l = E /\ lengthN l = CARD E).

Lemma list_of_set_def {A : Type'} : (@list_of_set A) = (fun _56426 : A -> Prop => @ε (list A) (fun l : list A => ((@set_of_list A l) = _56426) /\ ((@lengthN A l) = (@CARD A _56426)))).
Proof. exact (eq_refl (@list_of_set A)). Qed.

(* Transitive closure *)
Inductive TC {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
 | TC_R : forall x y, R x y -> TC R x y
 | TC_trans : forall x y z, TC R x y -> TC R y z -> TC R x z.

Lemma TC_def {A : Type'} : (@TC A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall TC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (exists y : A, (TC' a0' y) /\ (TC' y a1'))) -> TC' a0' a1') -> TC' a0 a1).
Proof.
  ext R. ind_align'. exact (TC_trans R x y0 y H H0).
Qed.

Fixpoint FILTER {A : Type'} (P : A -> Prop) l :=
  match l with
  | nil => nil
  | cons a l => let l' := FILTER P l in COND (P a) (cons a l') l'  end.

Lemma FILTER_def {A : Type'} : (@FILTER A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> Prop) -> (list A) -> list A) (fun FILTER' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> Prop) -> (list A) -> list A => forall _18185 : prod N (prod N (prod N (prod N (prod N N)))), (forall P : A -> Prop, (FILTER' _18185 P (@nil A)) = (@nil A)) /\ (forall h : A, forall P : A -> Prop, forall t : list A, (FILTER' _18185 P (@cons A h t)) = (@COND (list A) (P h) (@cons A h (FILTER' _18185 P t)) (FILTER' _18185 P t)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))).
Proof. total_align. Qed.

Definition MEASURE {A : Type} f (x y : A) := f x < f y.

Lemma MEASURE_def {A : Type'} : (@MEASURE A) = (fun _8094 : A -> N => fun x : A => fun y : A => N.lt (_8094 x) (_8094 y)).
Proof. exact (eq_refl (@MEASURE A)). Qed.

Lemma WFP_def {_184264 : Type'} : @Acc _184264 = (fun lt2' : _184264 -> _184264 -> Prop => fun a : _184264 => forall WFP' : _184264 -> Prop, (forall a' : _184264, (forall y : _184264, (lt2' y a') -> WFP' y) -> WFP' a') -> WFP' a).
Proof.
  ext R a. apply prop_ext;intro H.
  - intros Acc' H'. induction H. now apply H'.
  - apply H. intro x. exact (Acc_intro _).
Qed.

(*****************************************************************************)
(* Metric spaces (Libraries/analysis.ml) *)
(*****************************************************************************)
(* Difference with coq : Base is an argument instead of a projection *)

(* Cannot mannage to map to a subtype of Metric_Space : Universe Inconsistency *)

Definition discrete_metric A (c : prod A A) : R := COND (fst c=snd c) 0%R 1%R.

Lemma discr_pos A : forall x y, (discrete_metric A (x,y) >= 0)%R.
Proof.
  intros. unfold discrete_metric. apply COND_intro. reflexivity.
  left. exact Rlt_0_1.
Qed.

Lemma discr_sym A : forall x y, discrete_metric A (x,y) = discrete_metric A (y,x).
Proof.
  intros. unfold discrete_metric. do 2 apply COND_intro.
  1,4 : reflexivity.
  intros nH H. 2 : intros H nH.
  all : symmetry in H ; destruct (nH H).
Qed.

Lemma discr_refl A : forall x y, discrete_metric A (x,y) = 0%R <-> x = y.
Proof.
  intros. unfold discrete_metric. apply COND_intro;split;intro F;auto.
  destruct (R1_neq_R0 F). contradiction.
Qed.

Require Import Lra.
Lemma discr_tri A : forall x y z,
  (discrete_metric A (x,y) <= discrete_metric A (x,z) + discrete_metric A (z,y))%R.
Proof.
  intros. unfold discrete_metric. do 3 apply COND_intro;try lra.
  intros eq1 eq2 neq. destruct (neq (eq_trans eq2 eq1)).
Qed.

(* Attempt with dependant type equality, not quite a success yet *)
(*
Record Metric (A : Type') := { mdist : prod A A -> R;
    mdist_pos : forall x y : A, (mdist (x,y) >= 0)%R;
    mdist_sym : forall x y : A, mdist (x,y) = mdist (y,x);
    mdist_refl : forall x y : A, mdist (x,y) = 0%R <-> x = y;
    mdist_tri : forall x y z : A, (mdist (x,y) <= mdist (x,z) + mdist (z,y))%R }.

Definition discrete (A : Type') :=
  {| mdist := discrete_metric A;
     mdist_pos := discr_pos A;
     mdist_sym := discr_sym A;
     mdist_refl := discr_refl A;
     mdist_tri := discr_tri A |}.

Definition Metric' (A : Type') := {| type := Metric A ; el := discrete A |}.
Canonical Metric'.

Definition metric {A : Type'} := finv (@mdist A).

Ltac ext_fun e :=
  let H := fresh in
  assert (H := ext_fun e) ; clear e ;
  rename H into e.

Print eq_rect.

Definition mdist_proj {A : Type'} {d : prod A A -> R} {M : Metric A} (H : mdist A M = d) :=
  {| mdist := d ;
     mdist_pos := match H in (_ = d) return (forall x y : A, (d (x,y) >= 0)%R) with
       eq_refl => mdist_pos A M end ;
     mdist_sym := match H in (_ = d) return (forall x y : A, d (x,y) = d (y,x)) with
       eq_refl => mdist_sym A M end ;
     mdist_refl := match H in (_ = d) return (forall x y : A, d (x,y) = 0%R <-> x = y) with
       eq_refl => mdist_refl A M end ;
     mdist_tri := match H in (_ = d) return (forall x y z : A, (d (x,y) <= d (x,z) + d (z,y))%R) with
       eq_refl => mdist_tri A M end |}.

Lemma mdist_proj_surj {A : Type'} {d : prod A A -> R} {M : Metric A} (H : d = mdist A M) :
  exists M', exists (H' : mdist A M' = d), mdist_proj (eq_trans H' H) = M.
Proof.
  exists (mdist_proj (eq_sym H)). simpl. exists (eq_refl d).
  destruct M. unfold mdist_proj. simpl. f_equal;apply proof_irrelevance.
Qed.

Lemma _mk_dest_metric : forall {A : Type'} (a : Metric A), (@metric A (@mdist A a)) = a.
Proof.
  intro A. _mk_dest_rec. clear H. (* Can be improved in the tactic... *)
  intros M M' H. destruct (mdist_proj_surj H) as (M'0, (H'0, H'1)).
  destruct (mdist_proj_surj (eq_refl (mdist A M))) as (M0, (H0 , H1)).
  rewrite <- H1 , <- H'1. simpl.
Qed.
Axiom axiom_44 : forall {A : Type'} (r : (prod A A) -> R), ((fun m : (prod A A) -> R => @ismet A m) r) = ((@mdist A (@metric A r)) = r).
*)

Definition ismet {A : Type'} : (prod A A -> R) -> Prop := fun d =>
  (forall x y, d (x,y) = 0%R <-> x=y) /\
  forall x y z : A, (d (y,z) <= d (x,y) + d (x,z))%R.

Lemma ismet_def {A : Type'} : (@ismet A) = (fun _114640 : (prod A A) -> R => (forall x : A, forall y : A, ((_114640 (@pair A A x y)) = (R_of_N (NUMERAL N0))) = (x = y)) /\ (forall x : A, forall y : A, forall z : A, Rle (_114640 (@pair A A y z)) (Rplus (_114640 (@pair A A x y)) (_114640 (@pair A A x z))))).
Proof.
  ext d. unfold ismet. f_equal;auto.
  apply prop_ext;intro H ; intros. now apply prop_ext_eq.
  now rewrite H.
Qed.

Lemma is_metric0 {A : Type'} : ismet (discrete_metric A).
Proof.
  split. exact (discr_refl A). intros x y z. rewrite (discr_sym A x y).
  now apply discr_tri.
Qed.

Definition Metric (A : Type') := subtype (A:= prod A A -> R) is_metric0.

Definition metric {A : Type'} : (prod A A -> R) -> Metric A := mk is_metric0.
Definition mdist {A : Type'} : Metric A -> prod A A -> R := dest is_metric0.

Definition _mk_dest_Metric {A : Type'} : forall a : Metric A, (@metric A (@mdist A a)) = a :=
  mk_dest is_metric0.

Definition _dest_mk_Metric {A : Type'} : forall r : (prod A A) -> R, ((fun m : (prod A A) -> R => @ismet A m) r) = ((@mdist A (@metric A r)) = r) :=
  dest_mk is_metric0.

(*****************************************************************************)
(* Multisets *)
(*****************************************************************************)

Lemma empty_mempty_domain {A : Type} : (fun _ : A => 0 <> 0) = Empty_set.
Proof.
  ext x. apply prop_ext ; intro H. destruct (H (eq_refl 0)). inversion H.
Qed.

Definition is_fmultiset {A : Type'} : (A -> N) -> Prop :=
  fun f => @FINITE A (@GSPEC A (fun GEN_PVAR_433 : A => exists a : A, @SETSPEC A GEN_PVAR_433 (~ ((f a) = (NUMERAL N0))) a)).

Lemma is_fmultiset0 (A : Type') : is_fmultiset (fun (_ : A) => 0).
Proof.
  unfold is_fmultiset. rewrite SPEC_elim , FINITE_eq_finite , empty_mempty_domain. left.
Qed.

Definition Multiset (A : Type') := subtype (is_fmultiset0 A).

Definition multiset {A : Type'} := mk (is_fmultiset0 A).
Definition multiplicity {A : Type'} := dest (is_fmultiset0 A).

Lemma _mk_dest_Multiset : forall {A : Type'} (a : Multiset A), (@multiset A (@multiplicity A a)) = a.
Proof. intros. apply mk_dest. Qed.

Lemma _dest_mk_Multiset : forall {A : Type'} (r : A -> N), ((fun f : A -> N => @FINITE A (@GSPEC A (fun GEN_PVAR_433 : A => exists a : A, @SETSPEC A GEN_PVAR_433 (~ ((f a) = (NUMERAL N0))) a))) r) = ((@multiplicity A (@multiset A r)) = r).
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
  _mk_dest_rec. exact (proj1 _dest_term_tl_inj).
Qed.

Lemma _mk_dest_list_204637 : forall l, (_mk_list_204637  (_dest_list_204637  l)) = l.
Proof.
  _mk_dest_rec. exact (proj2 _dest_term_tl_inj).
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
  apply finv_inv ; intro H ;
  [ apply (H (fun y => exists x, _dest_term x = y)) ; (* P y states that to prove any P' y, one only has to prove
                 P' x' for all x' built from the constructors (top down construction).
                 so we apply it to our goal and then use firstorder to break the hypothesis
                 into clauses of equality with each constructor, rewrite it,
                 then remove the hypothesis and we are only left with choosing
                 the correct construtor to replace x with. *)
    clear H ; split ; intros x H ;
    firstorder ; rewrite H ;
    clear H ; simpl in *
  | (* simply inducting over x such that _dest_ x = y. *)
    destruct H as (x,H) ; rewrite <- H ; clear H ;
    intros P P' H ; exact (proj2 (_dest_mk_term_tl0 P P' H) x) ].
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
  apply finv_inv ; intro H ;
  [ apply (H (fun y => exists x, _dest_term x = y) (fun y => exists x, _dest_list_204637 x = y)) ; (* P y states that to prove any P' y, one only has to prove
                 P' x' for all x' built from the constructors (top down construction).
                 so we apply it to our goal and then use firstorder to break the hypothesis
                 into clauses of equality with each constructor, rewrite it,
                 then remove the hypothesis and we are only left with choosing
                 the correct construtor to replace x with. *)
    clear H ; split ; intros x H ;
    firstorder ; rewrite H ;
    clear H ; simpl in *
  | (* simply inducting over x such that _dest_ x = y. *)
    destruct H as (x,H) ; rewrite <- H ; clear H ;
    intros P P' H ; exact (proj1 (_dest_mk_term_tl0 P P' H) x) ].
  - now exists (V x0).
  - rewrite <- H0. now exists (Fn x0 x2).
  - now exists nil.
  - rewrite <- H0, <- H1. now exists (x3::x2).
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
   where the recursive call is done through List.map on terms *)

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

Lemma _mk_dest_form : forall (a : form), (_mk_form (_dest_form a)) = a.
Proof. _mk_dest_rec. Qed.

Lemma _dest_mk_form : forall (r : recspace (prod N (list term))), ((fun a : recspace (prod N (list term)) => forall form' : (recspace (prod N (list term))) -> Prop, (forall a' : recspace (prod N (list term)), ((a' = (@CONSTR (prod N (list term)) (NUMERAL N0) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (fun n : N => @BOTTOM (prod N (list term))))) \/ ((exists a0 : N, exists a1 : list term, a' = ((fun a0' : N => fun a1' : list term => @CONSTR (prod N (list term)) (N.succ (NUMERAL N0)) (@pair N (list term) a0' a1') (fun n : N => @BOTTOM (prod N (list term)))) a0 a1)) \/ ((exists a0 : recspace (prod N (list term)), exists a1 : recspace (prod N (list term)), (a' = ((fun a0' : recspace (prod N (list term)) => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (NUMERAL N0))) (@pair N (list term) (@ε N (fun v : N => True)) (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a0' (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term)))))) a0 a1)) /\ ((form' a0) /\ (form' a1))) \/ (exists a0 : N, exists a1 : recspace (prod N (list term)), (a' = ((fun a0' : N => fun a1' : recspace (prod N (list term)) => @CONSTR (prod N (list term)) (N.succ (N.succ (N.succ (NUMERAL N0)))) (@pair N (list term) a0' (@ε (list term) (fun v : list term => True))) (@FCONS (recspace (prod N (list term))) a1' (fun n : N => @BOTTOM (prod N (list term))))) a0 a1)) /\ (form' a1))))) -> form' a') -> form' a) r) = ((_dest_form (_mk_form r)) = r).
Proof.
  intro r. _dest_mk_rec.
  - now exists FFalse.
  - now exists (Atom x0 x1).
  - exists (FImp x3 x2). unfold _dest_form. now repeat f_equal.
  - exists (FAll x0 x2). unfold _dest_form. now repeat f_equal.
  - left. reflexivity.
  - right. left. exists n. now exists l.
  - do 2 right. left. exists (_dest_form x0_1). exists (_dest_form x0_2).
    repeat split;auto. now apply IHx0_1. now apply IHx0_2.
  - do 3 right. exists n. exists (_dest_form x0). split. reflexivity. now apply IHx0.
Qed.

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
Proof. ind_align'. Qed.

Inductive universal : form -> Prop :=
| universal_qfree : forall f, qfree f -> universal f
| universal_forall : forall f n, universal f -> universal (FAll n f).

Lemma universal_def : universal = (fun a : form => forall universal' : form -> Prop, (forall a' : form, ((qfree a') \/ (exists x : N, exists p : form, (a' = (FAll x p)) /\ (universal' p))) -> universal' a') -> universal' a).
Proof. ind_align'. Qed.

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

Definition Prenex_right : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).

Lemma Prenex_right_def : Prenex_right = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))))) -> form -> form -> form => forall _216639 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@Ensembles.Union N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))))))).
Proof. exact (eq_refl Prenex_right). Qed.

Definition Prenex_left : form -> form -> form := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form => forall _216680 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))))).

Lemma Prenex_left_def : Prenex_left = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> form -> form -> form => forall _216680 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply N form (fun y : N => @Datatypes.id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@Ensembles.Union N (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).
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

(****************************************************************************)
(* Conversion to Skollem form. *)
(****************************************************************************)
Definition Skolem1 (k n : N) (f : form) := formsubst (valmod (n , (Fn k (map V (list_of_set (free_variables (FEx n f)))))) V) f.

Lemma Skolem1_def : Skolem1 = (fun _221139 : N => fun _221140 : N => fun _221141 : form => formsubst (@valmod term N (@pair N term _221140 (Fn _221139 (@List.map N term V (@list_of_set N (free_variables (FEx _221140 _221141)))))) V) _221141).
Proof. exact (eq_refl Skolem1). Qed.

Function Skolems0 (n k : N) (f : form) {measure size f} :=
  match f with
  | FAll m f => FAll m (Skolems0 n k f)
  | FImp f0 f1 => match f1 with (* Case FEx n f' *) 
                   | FFalse => match f0 with
                     | FAll m f0 => match f0 with
                       | FImp f01 f02 => match f02 with
                         | FFalse => Skolems0 n (N.succ k) (Skolem1 (NUMPAIR n k) m f01)
                         | _ => f end
                       | _ => f end
                     | _ => f end
                   | _ => f end
  | _ => f end.
Proof.
  intros n k _ _ _ _ m _ f _ _ _ _ _. unfold Skolem1. rewrite size_formsubst.
  2 : intros _ _ _ m f _.
  1,2 : simpl ; induction (size f) ; auto ; exact (le_n_S _ _ IHn0).
Qed.

Definition Skolems n f k := Skolems0 n k f.

Lemma Skolems_def : Skolems = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> form -> N -> form) (fun Skolems' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> form -> N -> form => forall _221561 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall J : N, forall r : form, forall k : N, (Skolems' _221561 J r k) = (@PPAT form (fun x : N => fun q : form => FAll x (Skolems' _221561 J q k)) (fun x : N => fun q : form => Skolems' _221561 J (Skolem1 (NUMPAIR J k) x q) (N.succ k)) (fun p : form => p) r)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))).
Proof.
  align_ε'.
  - intros n f k. unfold Skolems. now rewrite Skolems0_equation.
  - intros f' H H'. ext n f k. unfold Skolems.
    functional induction (Skolems0 n k f) ; rewrite H' ; clear H'.
    1,2 : now rewrite IHf0.
    1-5 : match goal with f : _ |- _ => now induction f end.
Qed.

Definition Skopre n f := Skolems n (Prenex f) 0.

Lemma Skopre_def : Skopre = (fun _223892 : N => fun _223893 : form => Skolems _223892 (Prenex _223893) (NUMERAL N0)).
Proof. exact (eq_refl Skopre). Qed.

Definition bumpmod {A : Type'} (M : Structure A) : Structure A :=
  (Dom M , ((fun n l => Fun M (NUMSND n) l) , Pred M)).

Lemma bumpmod_def {_195501 : Type'} : (@bumpmod _195501) = (fun _223909 : prod (_195501 -> Prop) (prod (N -> (list _195501) -> _195501) (N -> (list _195501) -> Prop)) => @pair (_195501 -> Prop) (prod (N -> (list _195501) -> _195501) (N -> (list _195501) -> Prop)) (@Dom _195501 _223909) (@pair (N -> (list _195501) -> _195501) (N -> (list _195501) -> Prop) (fun k : N => fun zs : list _195501 => @Fun _195501 _223909 (NUMSND k) zs) (@Pred _195501 _223909))).
Proof. exact (eq_refl (@bumpmod _195501)). Qed.

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
Proof. exact (eq_refl (@unbumpmod _195825)). Qed.

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
Proof. exact (eq_refl form_of_num). Qed.

Definition SKOLEMIZE f := Skopre (num_of_form (bumpform f) + 1) (bumpform f).

Lemma SKOLEMIZE_def : SKOLEMIZE = (fun _225311 : form => Skopre (N.add (num_of_form (bumpform _225311)) (NUMERAL (BIT1 N0))) (bumpform _225311)).
Proof. exact (eq_refl SKOLEMIZE). Qed.

Definition SKOMOD1 {A : Type'} (f : form) (M : Structure A) : Structure A :=
  COND (forall v : N -> A, valuation M v -> holds M v f)
    (ε (fun M' => Dom M' = Dom M /\ Pred M' = Pred M /\
       (forall n l, Fun M' n l <> Fun M (NUMSND n) l -> exists k, n = (NUMPAIR (num_of_form (bumpform f) + 1) k)) /\ 
       interpretation (language (Singleton (SKOLEMIZE f))) M' /\ 
       (forall v : N -> A, valuation M' v -> holds M' v (SKOLEMIZE f))))
    (Dom M , ((fun n l => ε (fun a : A => IN a (Dom M))), Pred M)).

Lemma SKOMOD1_def {A : Type'} : (@SKOMOD1 A) = (fun _226669 : form => fun _226670 : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => @COND (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (forall v : N -> A, (@valuation A _226670 v) -> @holds A _226670 v _226669) (@ε (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (fun M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => ((@Dom A M') = (@Dom A (@bumpmod A _226670))) /\ (((@Pred A M') = (@Pred A (@bumpmod A _226670))) /\ ((forall g : N, forall zs : list A, (~ ((@Fun A M' g zs) = (@Fun A (@bumpmod A _226670) g zs))) -> exists l : N, g = (NUMPAIR (N.add (num_of_form (bumpform _226669)) (NUMERAL (BIT1 N0))) l)) /\ ((@interpretation A (language (@INSERT form (SKOLEMIZE _226669) (@Ensembles.Empty_set form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (SKOLEMIZE _226669))))))) (@pair (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) (@Dom A _226670) (@pair (N -> (list A) -> A) (N -> (list A) -> Prop) (fun g : N => fun zs : list A => @ε A (fun a : A => @IN A a (@Dom A _226670))) (@Pred A _226670)))).
Proof.
  ext f M. unfold SKOMOD1. repeat f_equal.
  ext M'. repeat f_equal.
  exact (Singleton_from_Empty (SKOLEMIZE f)).
Qed.

Definition SKOMOD {A : Type'} (M : Structure A) : Structure A :=
  (Dom M,
  ((fun n l => match (NUMFST n) with
  | 0 => Fun M (NUMSND n) l
  | _ => Fun (SKOMOD1 (unbumpform (form_of_num (N.pred (NUMFST n)))) M) n l end),
  Pred M)).

Lemma SKOMOD_def {_196878 : Type'} : (@SKOMOD _196878) = (fun _226687 : prod (_196878 -> Prop) (prod (N -> (list _196878) -> _196878) (N -> (list _196878) -> Prop)) => @pair (_196878 -> Prop) (prod (N -> (list _196878) -> _196878) (N -> (list _196878) -> Prop)) (@Dom _196878 _226687) (@pair (N -> (list _196878) -> _196878) (N -> (list _196878) -> Prop) (fun g : N => fun zs : list _196878 => @COND _196878 ((NUMFST g) = (NUMERAL N0)) (@Fun _196878 _226687 (NUMSND g) zs) (@Fun _196878 (@SKOMOD1 _196878 (unbumpform (form_of_num (N.pred (NUMFST g)))) _226687) g zs)) (@Pred _196878 _226687))).
Proof.
  ext M. unfold SKOMOD. repeat f_equal.
  ext n l. apply COND_intro ; induction (NUMFST n) ; auto.
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
Proof. exact (eq_refl SKOLEM). Qed.

(*****************************************************************************)
(* Propositional calculus *)
(*****************************************************************************)

(* Representing Propositional calculus in FOL by considering that every atomic formula
   and every universally quantified formula is simply a propositional variable. *)

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

Definition canonical (L : prod (Ensemble (prod N N)) (Ensemble (prod N N)))
  (M : Structure term) := (Dom M = terms (fst L) /\ (forall n, Fun M n = Fn n)).

Lemma canonical_def : canonical = (fun _230099 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _230100 : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) => ((@Dom term _230100) = (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _230099))) /\ (forall f : N, (@Fun term _230100 f) = (Fn f))).
Proof. exact (eq_refl canonical). Qed.

Lemma prop_of_model_def {_199383 : Type'} : holds = (fun _230111 : prod (_199383 -> Prop) (prod (N -> (list _199383) -> _199383) (N -> (list _199383) -> Prop)) => fun _230112 : N -> _199383 => fun _230113 : form => @holds _199383 _230111 _230112 _230113).
Proof. exact (eq_refl (@holds _199383)). Qed.

Definition canon_of_prop (L : prod (Ensemble (prod N N)) (Ensemble (prod N N)))
  (Predval : form -> Prop)  := (terms (fst L), (Fn, fun (p : N) (l : list term) => Predval (Atom p l))).

Lemma canon_of_prop_def : canon_of_prop = (fun _230132 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _230133 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _230132)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun l : list term => _230133 (Atom p l)))).
Proof. exact (eq_refl canon_of_prop). Qed.

Definition term_of_num := finv num_of_term.

Lemma term_of_num_def : term_of_num = (fun _230920 : N => @ε term (fun t : term => (num_of_term t) = _230920)).
Proof. exact (eq_refl term_of_num). Qed.

Definition LOWMOD (M : Structure term) : Structure N := (IMAGE num_of_term (Dom M), 
  (fun n l => num_of_term (Fun M n (map term_of_num l)),
  fun n l => Pred M n (map term_of_num l))).

Lemma LOWMOD_def : LOWMOD = (fun _230925 : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) => @pair (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) (@GSPEC N (fun GEN_PVAR_501 : N => exists t : term, @SETSPEC N GEN_PVAR_501 (@IN term t (@Dom term _230925)) (num_of_term t))) (@pair (N -> (list N) -> N) (N -> (list N) -> Prop) (fun g : N => fun zs : list N => num_of_term (@Fun term _230925 g (@List.map N term term_of_num zs))) (fun p : N => fun zs : list N => @Pred term _230925 p (@List.map N term term_of_num zs)))).
Proof. exact (eq_refl LOWMOD). Qed.

(*****************************************************************************)
(* herbrand.ml *)
(*****************************************************************************)

Inductive herbase (functions : Ensemble (prod N N)) : term -> Prop :=
| herbase_const : (~ exists k, IN (k,0) functions) -> herbase functions (V 0)
| herbase_Fn : forall n l, IN (n , lengthN l) functions ->
    Forall (herbase functions) l -> herbase functions (Fn n l).

Lemma herbase_def : herbase = (fun fns : (prod N N) -> Prop => fun a : term => forall herbase' : term -> Prop, (forall a' : term, (((a' = (V (NUMERAL N0))) /\ (~ (exists c : N, @IN (prod N N) (@pair N N c (NUMERAL N0)) fns))) \/ (exists f : N, exists l : list term, (a' = (Fn f l)) /\ ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term herbase' l)))) -> herbase' a') -> herbase' a).
Proof.
  ext functions t. apply prop_ext ; intro H.
  intros P' H'. induction t ; apply H'.
  - inversion H. now left.
  - right. exists n. exists l.
    inversion_clear H. repeat split;auto.
    clear H1. induction l;auto. inversion_clear H0.
    inversion_clear H2. apply Forall_cons;auto.
  - apply H ; clear H ; clear t ; intros t H.
    destruct H as [(eq , H) | (n , (l , (eq , (H , H'))))] ; rewrite eq.
    + exact (herbase_const functions H).
    + exact (herbase_Fn functions n l H H').
Qed.

Definition herbrand (L : prod (Ensemble (prod N N)) (Ensemble (prod N N)))
  (M : Structure term) := (Dom M = herbase (fst L) /\ (forall n, Fun M n = Fn n)).

Lemma herbrand_def : herbrand = (fun _232129 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _232130 : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) => ((@Dom term _232130) = (herbase (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _232129))) /\ (forall f : N, (@Fun term _232130 f) = (Fn f))).
Proof. exact (eq_refl herbrand). Qed.

Definition herbrand_of_prop (L : prod (Ensemble (prod N N)) (Ensemble (prod N N)))
  (Predval : form -> Prop)  := (herbase (fst L), (Fn, fun (p : N) (l : list term) => Predval (Atom p l))).

Lemma herbrand_of_prop_def : herbrand_of_prop = (fun _232334 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => fun _232335 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (herbase (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _232334)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun l : list term => _232335 (Atom p l)))).
Proof. exact (eq_refl herbrand_of_prop). Qed.

(*****************************************************************************)
(* fole.ml : FOL with defined equality  *)
(*****************************************************************************)

Definition FEq t t' := Atom 0 (cons t (cons t' nil)).

Lemma FEq_def : FEq = (fun _232588 : term => fun _232589 : term => Atom (NUMERAL N0) (@cons term _232588 (@cons term _232589 (@nil term)))).
Proof. exact (eq_refl FEq). Qed.

Definition uclose f := fold_right_with_perm_args FAll (list_of_set (free_variables f)) f.

Lemma uclose_def : uclose = (fun _232600 : form => @fold_right_with_perm_args N form FAll (@list_of_set N (free_variables _232600)) _232600).
Proof. exact (eq_refl uclose). Qed.

Definition normal {A : Type'} functions (M : Structure A) :=
  (forall t t' v, valuation M v /\ IN t (terms functions) /\ IN t' (terms functions) ->
  holds M v (FEq t t') <-> (termval M v t = termval M v t')).

Lemma normal_def {_201755 : Type'} : (@normal _201755) = (fun _232605 : (prod N N) -> Prop => fun _232606 : prod (_201755 -> Prop) (prod (N -> (list _201755) -> _201755) (N -> (list _201755) -> Prop)) => forall s : term, forall t : term, forall v : N -> _201755, ((@valuation _201755 _232606 v) /\ ((@IN term s (terms _232605)) /\ (@IN term t (terms _232605)))) -> (@holds _201755 _232606 v (FEq s t)) = ((@termval _201755 _232606 v s) = (@termval _201755 _232606 v t))).
Proof.
  ext functions M.
  apply prop_ext;intros H t t' v H' ; apply H in H'.
  now apply prop_ext_eq. now rewrite H'.
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
  align_ε'. reflexivity.
  intros Eq' _ H'. ext (t , t'). now rewrite H'.
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

Definition Eqaxioms (L : prod (Ensemble (prod N N)) (Ensemble (prod N N))) :=
  Union (Singleton FEq_refl)
    (Union (Singleton FEq_trans_sym)
      (Union (IMAGE Eqaxiom_Func (fst L)) (IMAGE Eqaxiom_Pred (snd L)))).

Lemma Eqaxioms_def : Eqaxioms = (fun _232639 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => @Ensembles.Union form (@INSERT form (FAll (NUMERAL N0) (FEq (V (NUMERAL N0)) (V (NUMERAL N0)))) (@Ensembles.Empty_set form)) (@Ensembles.Union form (@INSERT form (FAll (NUMERAL N0) (FAll (NUMERAL (BIT1 N0)) (FAll (NUMERAL (BIT0 (BIT1 N0))) (FImp (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT1 N0)))) (FImp (FEq (V (NUMERAL (BIT0 (BIT1 N0)))) (V (NUMERAL (BIT1 N0)))) (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT0 (BIT1 N0)))))))))) (@Ensembles.Empty_set form)) (@Ensembles.Union form (@GSPEC form (fun GEN_PVAR_508 : form => exists fa : prod N N, @SETSPEC form GEN_PVAR_508 (@IN (prod N N) fa (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _232639)) (Eqaxiom_Func fa))) (@GSPEC form (fun GEN_PVAR_509 : form => exists pa : prod N N, @SETSPEC form GEN_PVAR_509 (@IN (prod N N) pa (@snd ((prod N N) -> Prop) ((prod N N) -> Prop) _232639)) (Eqaxiom_Pred pa)))))).
Proof.
  ext L. unfold NUMERAL,Eqaxioms.
  repeat f_equal ; now rewrite Singleton_from_Empty.
Qed.

(*****************************************************************************)
(* retval : bool with a 3rd possibility, exception *)
(*****************************************************************************)

Inductive retval := TT | FF | Exception.

Definition retval' := {| type := retval ; el := TT |}.
Canonical retval'.

Definition _dest_retval (v : retval) : recspace Prop :=
match v with
| TT => CONSTR 0 (ε (fun _ => True)) (fun _ => BOTTOM)
| FF => CONSTR 1 (ε (fun _ => True)) (fun _ => BOTTOM)
| Exception => CONSTR 2 (ε (fun _ => True)) (fun _ => BOTTOM) end.

Definition _mk_retval := finv _dest_retval.

Lemma _mk_dest_retval : forall v, (_mk_retval (_dest_retval v)) = v.
Proof.
  _mk_dest_rec.
Qed.

Lemma _dest_mk_retval : forall (r : recspace Prop), ((fun a : recspace Prop => forall retval' : (recspace Prop) -> Prop, (forall a' : recspace Prop, ((a' = (@CONSTR Prop (NUMERAL N0) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))) \/ ((a' = (@CONSTR Prop (N.succ (NUMERAL N0)) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))) \/ (a' = (@CONSTR Prop (N.succ (N.succ (NUMERAL N0))) (@ε Prop (fun x : Prop => True)) (fun n : N => @BOTTOM Prop))))) -> retval' a') -> retval' a) r) = ((_dest_retval (_mk_retval r)) = r).
Proof.
  intro r. _dest_mk_rec.
  4-6 : auto.
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
Proof. exact (eq_refl OCC). Qed.

Definition LOOPFREE l := forall n, ~ TC (OCC l) n n.

Lemma LOOPFREE_def : LOOPFREE = (fun _259325 : list (prod N term) => forall z : N, ~ (@TC N (OCC _259325) z z)).
Proof. exact (eq_refl LOOPFREE). Qed.

(* Inductive loopcheck (env : list (prod N term)) : N -> term -> Prop :=
  | loopcheck_isfreein : forall n t, IN n (free_variables_term t) -> loopcheck env n t
  | loopcheck_rec : forall n t n' t', IN n' (free_variables_term t) ->
                    In (n,t') env -> loopcheck env n' t' -> loopcheck env n t. *)

(* come back with a better tactic for partial functions *)

Definition rightsubst (c c' : prod N term) := (fst c',termsubst (valmod c V) (snd c')).

Lemma rightsubst_def : rightsubst = (fun _260241 : prod N term => fun _260242 : prod N term => @pair N term (@fst N term _260242) (termsubst (fun z : N => @COND term (z = (@fst N term _260241)) (@snd N term _260241) (V z)) (@snd N term _260242))).
Proof. exact (eq_refl rightsubst). Qed.

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
  induction l;auto. simpl. now rewrite IHl, list_rightsubst_tail.
Qed.

Lemma self_rightsubst_tail l c :
  self_rightsubst (l ++ c::nil) = let l' := map (rightsubst c) l in
  self_rightsubst l' ++ (list_rightsubst (lsubst l') c) :: nil.
Proof.
  induction l;auto.
  simpl. rewrite IHl.
  now rewrite map_last,lsubst_tail,list_rightsubst_tail.
Qed.

Function SOLVE0 l l' {measure length l'} := (* Defined only for its induction principle. *)
  match l' with
  | nil => l
  | c'::l' => SOLVE0 (c'::(map (rightsubst c') l)) (map (rightsubst c') l') end.
Proof.
  intros _ _ c l _. simpl. rewrite length_map. auto.
Qed.

Lemma SOLVEC_def : SOLVEC = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (prod (list (prod N term)) (list (prod N term))) -> list (prod N term)) (fun SOLVE' : (prod N (prod N (prod N (prod N (prod N N))))) -> (prod (list (prod N term)) (list (prod N term))) -> list (prod N term) => forall _260267 : prod N (prod N (prod N (prod N (prod N N)))), forall pr : prod (list (prod N term)) (list (prod N term)), (SOLVE' _260267 pr) = (@COND (list (prod N term)) ((@snd (list (prod N term)) (list (prod N term)) pr) = (@nil (prod N term))) (@fst (list (prod N term)) (list (prod N term)) pr) (SOLVE' _260267 (@pair (list (prod N term)) (list (prod N term)) (@cons (prod N term) (@mappings.hd (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr)) (@List.map (prod N term) (prod N term) (rightsubst (@mappings.hd (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr))) (@fst (list (prod N term)) (list (prod N term)) pr))) (@List.map (prod N term) (prod N term) (rightsubst (@mappings.hd (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr))) (@tl (prod N term) (@snd (list (prod N term)) (list (prod N term)) pr))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof.
  align_ε'.
  - intros (l,l'). simpl. rewrite COND_list. destruct l'. apply map_id.
    unfold SOLVEC. simpl. unfold SOLVE. rewrite <- map_rev.
    simpl. rewrite self_rightsubst_tail. simpl.
    rewrite (appcons_appapp (list_rightsubst (lsubst (map (rightsubst p) (rev l'))) p)).
    do 2 f_equal. induction l;auto. simpl.
    now rewrite IHl , lsubst_tail , list_rightsubst_tail.
  - intros f' H H'. ext (l,l').
    functional induction (SOLVE0 l l') ; rewrite H' ; rewrite COND_list. (* there must be a better way,
                                                                            this is ridiculous. *)
    unfold SOLVEC , SOLVE. now rewrite map_id.
    simpl. rewrite <- IHl0.
    unfold SOLVEC in *. now rewrite (H (l,c'::l'0)) , COND_list.
Qed.

Lemma SOLVE_def : SOLVE = (fun _260268 : list (prod N term) => fun _260269 : list (prod N term) => SOLVEC (@pair (list (prod N term)) (list (prod N term)) _260268 _260269)).
Proof. exact (eq_refl SOLVE). Qed.

Definition CONFLICTFREE (l : list (N*term)) :=
  forall n, lengthN (FILTER (fun c => fst c = n) l) <= 1.

Lemma CONFLICTFREE_def : CONFLICTFREE = (fun _260280 : list (prod N term) => forall x : N, N.le (@lengthN (prod N term) (@FILTER (prod N term) (@ε ((prod N term) -> Prop) (fun f : (prod N term) -> Prop => forall y : N, forall s : term, @eq Prop (f (@pair N term y s)) (y = x))) _260280)) (NUMERAL (BIT1 N0))).
Proof.
  unfold CONFLICTFREE. ext l.
  apply (f_equal (fun f => forall n : N, lengthN (FILTER (f n) l) <=1)).
  ext n. align_ε'. reflexivity.
  intros f' H H'. ext (n',t). now rewrite H'.
Qed.

(* again, a difficult partial function. *) 
Definition istriv : (list (prod N term)) -> N -> term -> retval := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval) (fun istriv' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval => forall _262675 : prod N (prod N (prod N (prod N (prod N N)))), forall env : list (prod N term), forall x : N, ((LOOPFREE env) /\ (CONFLICTFREE env)) -> forall t : term, (istriv' _262675 env x t) = (@COND retval (t = (V x)) TT (@COND retval (exists y : N, (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env))) (istriv' _262675 env x (@assoc N term (@ε N (fun y : N => (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env)))) env)) (@COND retval (@IN N x (free_variables_term t)) Exception (@COND retval (exists y : N, exists s : term, (@IN N y (free_variables_term t)) /\ ((@List.In (prod N term) (@pair N term y s) env) /\ (~ ((istriv' _262675 env x s) = FF)))) Exception FF))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))).
Lemma istriv_def : istriv = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval) (fun istriv' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list (prod N term)) -> N -> term -> retval => forall _262675 : prod N (prod N (prod N (prod N (prod N N)))), forall env : list (prod N term), forall x : N, ((LOOPFREE env) /\ (CONFLICTFREE env)) -> forall t : term, (istriv' _262675 env x t) = (@COND retval (t = (V x)) TT (@COND retval (exists y : N, (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env))) (istriv' _262675 env x (@assoc N term (@ε N (fun y : N => (t = (V y)) /\ (@List.In N y (@List.map (prod N term) N (@fst N term) env)))) env)) (@COND retval (@IN N x (free_variables_term t)) Exception (@COND retval (exists y : N, exists s : term, (@IN N y (free_variables_term t)) /\ ((@List.In (prod N term) (@pair N term y s) env) /\ (~ ((istriv' _262675 env x s) = FF)))) Exception FF))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof. exact (eq_refl istriv). Qed.

Definition EQV {A : Type} l (a : A) n := In (a, V n) l.

Lemma EQV_def {_208558 : Type'} : (@EQV _208558) = (fun _263122 : list (prod _208558 term) => fun _263123 : _208558 => fun _263124 : N => @List.In (prod _208558 term) (@pair _208558 term _263123 (V _263124)) _263122).
Proof. exact (eq_refl (@EQV _208558)). Qed.

Definition SUB1 t t' := exists n l, t' = Fn n l /\ In t l.

Lemma SUB1_def : SUB1 = (fun _267259 : term => fun _267260 : term => exists f : N, exists args : list term, (_267260 = (Fn f args)) /\ (@List.In term _267259 args)).
Proof. exact (eq_refl SUB1). Qed.

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
Proof. ext f f' f''. ext (t,t'). now induction t'. Qed.

Definition MLEFT c :=
  match c with (env,eqs) =>
    CARD (Union (free_variables_term (Fn 0 (map fst eqs)))
    (Union (free_variables_term (Fn 0 (map snd eqs)))
    (Union (free_variables_term (Fn 0 (map snd env)))
    (free_variables_term (Fn 0 (map (Basics.compose V fst) env)))))) -
    CARD (free_variables_term (Fn 0 (map (Basics.compose V fst) env))) end.

Lemma MLEFT_def : MLEFT = (fun _267440 : prod (list (prod N term)) (list (prod term term)) => N.sub (@CARD N (@Ensembles.Union N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod term term) term (@fst term term) (@snd (list (prod N term)) (list (prod term term)) _267440)))) (@Ensembles.Union N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod term term) term (@snd term term) (@snd (list (prod N term)) (list (prod term term)) _267440)))) (@Ensembles.Union N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod N term) term (@snd N term) (@fst (list (prod N term)) (list (prod term term)) _267440)))) (free_variables_term (Fn (NUMERAL N0) (@List.map (prod N term) term (@Basics.compose (prod N term) N term V (@fst N term)) (@fst (list (prod N term)) (list (prod term term)) _267440)))))))) (@CARD N (free_variables_term (Fn (NUMERAL N0) (@List.map (prod N term) term (@Basics.compose (prod N term) N term V (@fst N term)) (@fst (list (prod N term)) (list (prod term term)) _267440)))))).
Proof. ext (env,eqs). reflexivity. Qed.

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
Proof. ext (env',eqs') (env,eqs). reflexivity. Qed.

Definition CALLORDER c' c :=
  MEASURE MLEFT c' c \/ CRIGHT c' c.

Lemma CALLORDER_def : CALLORDER = (fun _267471 : prod (list (prod N term)) (list (prod term term)) => fun _267472 : prod (list (prod N term)) (list (prod term term)) => (@MEASURE (prod (list (prod N term)) (list (prod term term))) MLEFT (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267471) (@snd (list (prod N term)) (list (prod term term)) _267471)) (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267472) (@snd (list (prod N term)) (list (prod term term)) _267472))) \/ (CRIGHT (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267471) (@snd (list (prod N term)) (list (prod term term)) _267471)) (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) _267472) (@snd (list (prod N term)) (list (prod term term)) _267472)))).
Proof. ext (env',eqs') (env,eqs). reflexivity. Qed.

(*****************************************************************************)
(* Trivial definitions *)
(*****************************************************************************)
Definition V_def' := eq_refl V.
Definition Fn_def' := eq_refl Fn.
Definition FFalse_def' := eq_refl FFalse.
Definition FImp_def' := eq_refl FImp.
Definition Atom_def' := eq_refl Atom.
Definition FAll_def' := eq_refl FAll.
Definition TT_def' := eq_refl TT.
Definition FF_def' := eq_refl FF.
Definition Exception_def' := eq_refl Exception.



