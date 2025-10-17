Require Import Stdlib.NArith.BinNat Stdlib.Reals.Reals mathcomp.classical.classical_sets mathcomp.classical.cardinality mathcomp.ssreflect.choice mathcomp.ssreflect.ssrbool MathComp_HOLLight_Real_With_N.mappings HOLLight_Logic_fole.mappings.
Require Import HOLLight_Logic_fole.terms.
Axiom thm_T_DEF : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Axiom thm_AND_DEF : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Axiom thm_IMP_DEF : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Axiom thm_FORALL_DEF : forall {A : Type'}, (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Axiom thm_EXISTS_DEF : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Axiom thm_OR_DEF : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Axiom thm_F_DEF : False = (forall p : Prop, p).
Axiom thm_NOT_DEF : not = (fun p : Prop => p -> False).
Axiom thm_EXISTS_UNIQUE_DEF : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Axiom thm__FALSITY_ : False = False.
Axiom thm_EQ_REFL : forall {A : Type'}, forall x : A, x = x.
Axiom thm_REFL_CLAUSE : forall {A : Type'}, forall x : A, (x = x) = True.
Axiom thm_EQ_SYM : forall {A : Type'}, forall x : A, forall y : A, (x = y) -> y = x.
Axiom thm_EQ_SYM_EQ : forall {A : Type'}, forall x : A, forall y : A, (x = y) = (y = x).
Axiom thm_EQ_TRANS : forall {A : Type'}, forall x : A, forall y : A, forall z : A, ((x = y) /\ (y = z)) -> x = z.
Axiom thm_BETA_THM : forall {A B : Type'}, forall f : A -> B, forall y : A, ((fun x : A => f x) y) = (f y).
Axiom thm_ABS_SIMP : forall {A B : Type'}, forall t1 : A, forall t2 : B, ((fun x : B => t1) t2) = t1.
Axiom thm_CONJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 /\ (t2 /\ t3)) = ((t1 /\ t2) /\ t3).
Axiom thm_CONJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 /\ t2) = (t2 /\ t1).
Axiom thm_CONJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p /\ q) = (q /\ p)) /\ ((((p /\ q) /\ r) = (p /\ (q /\ r))) /\ (((p /\ (q /\ r)) = (q /\ (p /\ r))) /\ (((p /\ p) = p) /\ ((p /\ (p /\ q)) = (p /\ q))))).
Axiom thm_DISJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 \/ (t2 \/ t3)) = ((t1 \/ t2) \/ t3).
Axiom thm_DISJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 \/ t2) = (t2 \/ t1).
Axiom thm_DISJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p \/ q) = (q \/ p)) /\ ((((p \/ q) \/ r) = (p \/ (q \/ r))) /\ (((p \/ (q \/ r)) = (q \/ (p \/ r))) /\ (((p \/ p) = p) /\ ((p \/ (p \/ q)) = (p \/ q))))).
Axiom thm_IMP_CONJ : forall (p : Prop) (q : Prop) (r : Prop), ((p /\ q) -> r) = (p -> q -> r).
Axiom thm_IMP_CONJ_ALT : forall (q : Prop) (p : Prop) (r : Prop), ((p /\ q) -> r) = (q -> p -> r).
Axiom thm_LEFT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, (p /\ (q \/ r)) = ((p /\ q) \/ (p /\ r)).
Axiom thm_RIGHT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, ((p \/ q) /\ r) = ((p /\ r) \/ (q /\ r)).
Axiom thm_FORALL_SIMP : forall {A : Type'}, forall t : Prop, (forall x : A, t) = t.
Axiom thm_EXISTS_SIMP : forall {A : Type'}, forall t : Prop, (exists x : A, t) = t.
Axiom thm_EQ_CLAUSES : forall t : Prop, ((True = t) = t) /\ (((t = True) = t) /\ (((False = t) = (~ t)) /\ ((t = False) = (~ t)))).
Axiom thm_NOT_CLAUSES_WEAK : ((~ True) = False) /\ ((~ False) = True).
Axiom thm_AND_CLAUSES : forall t : Prop, ((True /\ t) = t) /\ (((t /\ True) = t) /\ (((False /\ t) = False) /\ (((t /\ False) = False) /\ ((t /\ t) = t)))).
Axiom thm_OR_CLAUSES : forall t : Prop, ((True \/ t) = True) /\ (((t \/ True) = True) /\ (((False \/ t) = t) /\ (((t \/ False) = t) /\ ((t \/ t) = t)))).
Axiom thm_IMP_CLAUSES : forall t : Prop, ((True -> t) = t) /\ (((t -> True) = True) /\ (((False -> t) = True) /\ (((t -> t) = True) /\ ((t -> False) = (~ t))))).
Axiom thm_EXISTS_UNIQUE_THM : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = ((exists x : A, P x) /\ (forall x : A, forall x' : A, ((P x) /\ (P x')) -> x = x')).
Axiom thm_EXISTS_REFL : forall {A : Type'}, forall a : A, exists x : A, x = a.
Axiom thm_EXISTS_UNIQUE_REFL : forall {A : Type'}, forall a : A, @ex1 A (fun x : A => x = a).
Axiom thm_UNWIND_THM1 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (exists x : A, (a = x) /\ (P x)) = (P a).
Axiom thm_UNWIND_THM2 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (exists x : A, (x = a) /\ (P x)) = (P a).
Axiom thm_FORALL_UNWIND_THM2 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (forall x : A, (x = a) -> P x) = (P a).
Axiom thm_FORALL_UNWIND_THM1 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (forall x : A, (a = x) -> P x) = (P a).
Axiom thm_SWAP_FORALL_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall y : B, forall x : A, P x y).
Axiom thm_SWAP_EXISTS_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists y : B, exists x : A, P x y).
Axiom thm_FORALL_AND_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (forall x : A, (P x) /\ (Q x)) = ((forall x : A, P x) /\ (forall x : A, Q x)).
Axiom thm_AND_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, ((forall x : A, P x) /\ (forall x : A, Q x)) = (forall x : A, (P x) /\ (Q x)).
Axiom thm_LEFT_AND_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) /\ Q) = (forall x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P /\ (forall x : A, Q x)) = (forall x : A, P /\ (Q x)).
Axiom thm_EXISTS_OR_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (exists x : A, (P x) \/ (Q x)) = ((exists x : A, P x) \/ (exists x : A, Q x)).
Axiom thm_OR_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, ((exists x : A, P x) \/ (exists x : A, Q x)) = (exists x : A, (P x) \/ (Q x)).
Axiom thm_LEFT_OR_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) \/ Q) = (exists x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P \/ (exists x : A, Q x)) = (exists x : A, P \/ (Q x)).
Axiom thm_LEFT_EXISTS_AND_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) /\ Q) = ((exists x : A, P x) /\ Q).
Axiom thm_RIGHT_EXISTS_AND_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (exists x : A, P /\ (Q x)) = (P /\ (exists x : A, Q x)).
Axiom thm_TRIV_EXISTS_AND_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (exists x : A, P /\ Q) = ((exists x : A, P) /\ (exists x : A, Q)).
Axiom thm_LEFT_AND_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) /\ Q) = (exists x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P /\ (exists x : A, Q x)) = (exists x : A, P /\ (Q x)).
Axiom thm_TRIV_AND_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, ((exists x : A, P) /\ (exists x : A, Q)) = (exists x : A, P /\ Q).
Axiom thm_TRIV_FORALL_OR_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (forall x : A, P \/ Q) = ((forall x : A, P) \/ (forall x : A, Q)).
Axiom thm_TRIV_OR_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, ((forall x : A, P) \/ (forall x : A, Q)) = (forall x : A, P \/ Q).
Axiom thm_RIGHT_IMP_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P -> forall x : A, Q x) = (forall x : A, P -> Q x).
Axiom thm_RIGHT_FORALL_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (forall x : A, P -> Q x) = (P -> forall x : A, Q x).
Axiom thm_LEFT_IMP_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) -> Q) = (forall x : A, (P x) -> Q).
Axiom thm_LEFT_FORALL_IMP_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) -> Q) = ((exists x : A, P x) -> Q).
Axiom thm_TRIV_FORALL_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (forall x : A, P -> Q) = ((exists x : A, P) -> forall x : A, Q).
Axiom thm_TRIV_EXISTS_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (exists x : A, P -> Q) = ((forall x : A, P) -> exists x : A, Q).
Axiom thm_MONO_FORALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (forall x : A, P x) -> forall x : A, Q x.
Axiom thm_MONO_EXISTS : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (exists x : A, P x) -> exists x : A, Q x.
Axiom thm_WLOG_RELATION : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (P x y) -> P y x) /\ ((forall x : A, forall y : A, (R' x y) \/ (R' y x)) /\ (forall x : A, forall y : A, (R' x y) -> P x y))) -> forall x : A, forall y : A, P x y.
Axiom thm_EXISTS_UNIQUE_ALT : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, forall y : A, (P y) = (x = y)).
Axiom thm_EXISTS_UNIQUE : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, (P x) /\ (forall y : A, (P y) -> y = x)).
Axiom thm_ETA_AX : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Axiom thm_EQ_EXT : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, (forall x : A, (f x) = (g x)) -> f = g.
Axiom thm_FUN_EQ_THM : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, (f = g) = (forall x : A, (f x) = (g x)).
Axiom thm_SELECT_AX : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Axiom thm_EXISTS_THM : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => P (@ε A P)).
Axiom thm_SELECT_REFL : forall {A : Type'}, forall x : A, (@ε A (fun y : A => y = x)) = x.
Axiom thm_SELECT_UNIQUE : forall {A : Type'}, forall P : A -> Prop, forall x : A, (forall y : A, (P y) = (y = x)) -> (@ε A P) = x.
Axiom thm_EXCLUDED_MIDDLE : forall t : Prop, t \/ (~ t).
Axiom thm_BOOL_CASES_AX : forall t : Prop, (t = True) \/ (t = False).
Axiom thm_DE_MORGAN_THM : forall t1 : Prop, forall t2 : Prop, ((~ (t1 /\ t2)) = ((~ t1) \/ (~ t2))) /\ ((~ (t1 \/ t2)) = ((~ t1) /\ (~ t2))).
Axiom thm_NOT_CLAUSES : (forall t : Prop, (~ (~ t)) = t) /\ (((~ True) = False) /\ ((~ False) = True)).
Axiom thm_NOT_IMP : forall t1 : Prop, forall t2 : Prop, (~ (t1 -> t2)) = (t1 /\ (~ t2)).
Axiom thm_CONTRAPOS_THM : forall t1 : Prop, forall t2 : Prop, ((~ t1) -> ~ t2) = (t2 -> t1).
Axiom thm_NOT_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, (~ (exists x : A, P x)) = (forall x : A, ~ (P x)).
Axiom thm_EXISTS_NOT_THM : forall {A : Type'}, forall P : A -> Prop, (exists x : A, ~ (P x)) = (~ (forall x : A, P x)).
Axiom thm_NOT_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, (~ (forall x : A, P x)) = (exists x : A, ~ (P x)).
Axiom thm_FORALL_NOT_THM : forall {A : Type'}, forall P : A -> Prop, (forall x : A, ~ (P x)) = (~ (exists x : A, P x)).
Axiom thm_FORALL_BOOL_THM : forall (P : Prop -> Prop), (forall b : Prop, P b) = ((P True) /\ (P False)).
Axiom thm_EXISTS_BOOL_THM : forall (P : Prop -> Prop), (exists b : Prop, P b) = ((P True) \/ (P False)).
Axiom thm_LEFT_FORALL_OR_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) \/ Q) = ((forall x : A, P x) \/ Q).
Axiom thm_RIGHT_FORALL_OR_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (forall x : A, P \/ (Q x)) = (P \/ (forall x : A, Q x)).
Axiom thm_LEFT_OR_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) \/ Q) = (forall x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P \/ (forall x : A, Q x)) = (forall x : A, P \/ (Q x)).
Axiom thm_LEFT_IMP_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) -> Q) = (exists x : A, (P x) -> Q).
Axiom thm_LEFT_EXISTS_IMP_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) -> Q) = ((forall x : A, P x) -> Q).
Axiom thm_RIGHT_IMP_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P -> exists x : A, Q x) = (exists x : A, P -> Q x).
Axiom thm_RIGHT_EXISTS_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (exists x : A, P -> Q x) = (P -> exists x : A, Q x).
Axiom thm_COND_DEF : forall {A : Type'}, (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).
Axiom thm_COND_CLAUSES : forall {A : Type'}, forall t1 : A, forall t2 : A, ((@COND A True t1 t2) = t1) /\ ((@COND A False t1 t2) = t2).
Axiom thm_COND_EXPAND : forall b : Prop, forall t1 : Prop, forall t2 : Prop, (@COND Prop b t1 t2) = (((~ b) \/ t1) /\ (b \/ t2)).
Axiom thm_COND_ID : forall {A : Type'}, forall b : Prop, forall t : A, (@COND A b t t) = t.
Axiom thm_COND_RAND : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall x : A, forall y : A, (f (@COND A b x y)) = (@COND B b (f x) (f y)).
Axiom thm_COND_RATOR : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall g : A -> B, forall x : A, (@COND (A -> B) b f g x) = (@COND B b (f x) (g x)).
Axiom thm_COND_ABS : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall g : A -> B, (fun x : A => @COND B b (f x) (g x)) = (@COND (A -> B) b f g).
Axiom thm_COND_SWAP : forall {A : Type'}, forall p : Prop, forall x : A, forall y : A, (@COND A (~ p) x y) = (@COND A p y x).
Axiom thm_MONO_COND : forall (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop), ((A -> B) /\ (C -> D)) -> (@COND Prop b A C) -> @COND Prop b B D.
Axiom thm_COND_ELIM_THM : forall {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A), (P (@COND A c x y)) = ((c -> P x) /\ ((~ c) -> P y)).
Axiom thm_SKOLEM_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, exists y : B, P x y) = (exists y : A -> B, forall x : A, P x (y x)).
Axiom thm_SKOLEM_THM_GEN : forall {A B : Type'}, forall P : A -> Prop, forall R' : A -> B -> Prop, (forall x : A, (P x) -> exists y : B, R' x y) = (exists f : A -> B, forall x : A, (P x) -> R' x (f x)).
Axiom thm_UNIQUE_SKOLEM_ALT : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (exists f : A -> B, forall x : A, forall y : B, (P x y) = ((f x) = y)).
Axiom thm_UNIQUE_SKOLEM_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (@ex1 (A -> B) (fun f : A -> B => forall x : A, P x (f x))).
Axiom thm_bool_INDUCT : forall P : Prop -> Prop, ((P False) /\ (P True)) -> forall x : Prop, P x.
Axiom thm_bool_RECURSION : forall {A : Type'}, forall a : A, forall b : A, exists f : Prop -> A, ((f False) = a) /\ ((f True) = b).
Axiom thm_o_DEF : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, (@o A B C f g) = (fun x : A => f (g x)).
Axiom thm_I_DEF : forall {A : Type'}, (@I A) = (fun x : A => x).
Axiom thm_o_THM : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, forall x : A, (@o A B C f g x) = (f (g x)).
Axiom thm_o_ASSOC : forall {A B C D : Type'}, forall f : C -> D, forall g : B -> C, forall h : A -> B, (@o A C D f (@o A B C g h)) = (@o A B D (@o B C D f g) h).
Axiom thm_I_THM : forall {A : Type'}, forall x : A, (@I A x) = x.
Axiom thm_I_O_ID : forall {A B : Type'}, forall f : A -> B, ((@o A B B (@I B) f) = f) /\ ((@o A A B f (@I A)) = f).
Axiom thm_EXISTS_ONE_REP : exists b : Prop, b.
Axiom thm_one_DEF : tt = (@ε unit (fun x : unit => True)).
Axiom thm_one : forall v : unit, v = tt.
Axiom thm_one_axiom : forall {A : Type'}, forall f : A -> unit, forall g : A -> unit, f = g.
Axiom thm_one_INDUCT : forall P : unit -> Prop, (P tt) -> forall x : unit, P x.
Axiom thm_one_RECURSION : forall {A : Type'}, forall e : A, exists fn : unit -> A, (fn tt) = e.
Axiom thm_one_Axiom : forall {A : Type'}, forall e : A, @ex1 (unit -> A) (fun fn : unit -> A => (fn tt) = e).
Axiom thm_FORALL_ONE_THM : forall (P : unit -> Prop), (forall x : unit, P x) = (P tt).
Axiom thm_EXISTS_ONE_THM : forall (P : unit -> Prop), (exists x : unit, P x) = (P tt).
Axiom thm_ETA_ONE : forall {A : Type'}, forall f : unit -> A, (fun x : unit => f tt) = f.
Axiom thm_LET_DEF : forall {A B : Type'}, forall f : A -> B, forall x : A, (@LET A B f x) = (f x).
Axiom thm_LET_END_DEF : forall {A : Type'}, forall t : A, (@LET_END A t) = t.
Axiom thm_GABS_DEF : forall {A : Type'}, forall P : A -> Prop, (@ε A P) = (@ε A P).
Axiom thm_GEQ_DEF : forall {A : Type'}, forall a : A, forall b : A, (@eq A a b) = (a = b).
Axiom thm__SEQPATTERN : forall {A B : Type'}, (@_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Axiom thm__UNGUARDED_PATTERN : and = (fun p : Prop => fun r : Prop => p /\ r).
Axiom thm__GUARDED_PATTERN : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Axiom thm__MATCH : forall {A B : Type'}, (@_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Axiom thm__FUNCTION : forall {A B : Type'}, (@_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Axiom thm_mk_pair_def : forall {A B : Type'}, forall x : A, forall y : B, (@mk_pair A B x y) = (fun a : A => fun b : B => (a = x) /\ (b = y)).
Axiom thm_PAIR_EXISTS_THM : forall {A B : Type'}, exists x : A -> B -> Prop, exists a : A, exists b : B, x = (@mk_pair A B a b).
Axiom thm_REP_ABS_PAIR : forall {A B : Type'}, forall x : A, forall y : B, (@REP_prod A B (@ABS_prod A B (@mk_pair A B x y))) = (@mk_pair A B x y).
Axiom thm_COMMA_DEF : forall {A B : Type'}, forall x : A, forall y : B, (@pair A B x y) = (@ABS_prod A B (@mk_pair A B x y)).
Axiom thm_FST_DEF : forall {A B : Type'}, forall p : prod A B, (@fst A B p) = (@ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Axiom thm_SND_DEF : forall {A B : Type'}, forall p : prod A B, (@snd A B p) = (@ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Axiom thm_PAIR_EQ : forall {A B : Type'}, forall x : A, forall y : B, forall a : A, forall b : B, ((@pair A B x y) = (@pair A B a b)) = ((x = a) /\ (y = b)).
Axiom thm_PAIR_SURJECTIVE : forall {A B : Type'}, forall p : prod A B, exists x : A, exists y : B, p = (@pair A B x y).
Axiom thm_FST : forall {A B : Type'}, forall x : A, forall y : B, (@fst A B (@pair A B x y)) = x.
Axiom thm_SND : forall {A B : Type'}, forall x : A, forall y : B, (@snd A B (@pair A B x y)) = y.
Axiom thm_PAIR : forall {A B : Type'}, forall x : prod A B, (@pair A B (@fst A B x) (@snd A B x)) = x.
Axiom thm_pair_INDUCT : forall {A B : Type'}, forall P : (prod A B) -> Prop, (forall x : A, forall y : B, P (@pair A B x y)) -> forall p : prod A B, P p.
Axiom thm_pair_RECURSION : forall {A B C : Type'}, forall PAIR' : A -> B -> C, exists fn : (prod A B) -> C, forall a0 : A, forall a1 : B, (fn (@pair A B a0 a1)) = (PAIR' a0 a1).
Axiom thm_CURRY_DEF : forall {A B C : Type'}, forall f : (prod A B) -> C, forall x : A, forall y : B, (@CURRY A B C f x y) = (f (@pair A B x y)).
Axiom thm_UNCURRY_DEF : forall {A B C : Type'}, forall f : A -> B -> C, forall x : A, forall y : B, (@UNCURRY A B C f (@pair A B x y)) = (f x y).
Axiom thm_PASSOC_DEF : forall {A B C D : Type'}, forall f : (prod (prod A B) C) -> D, forall x : A, forall y : B, forall z : C, (@PASSOC A B C D f (@pair A (prod B C) x (@pair B C y z))) = (f (@pair (prod A B) C (@pair A B x y) z)).
Axiom thm_FORALL_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (forall p : prod A B, P p) = (forall p1 : A, forall p2 : B, P (@pair A B p1 p2)).
Axiom thm_EXISTS_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (exists p : prod A B, P p) = (exists p1 : A, exists p2 : B, P (@pair A B p1 p2)).
Axiom thm_LAMBDA_PAIR_THM : forall {A B C : Type'}, forall t : (prod A B) -> C, (fun p : prod A B => t p) = (@ε ((prod A B) -> C) (fun f : (prod A B) -> C => forall x : A, forall y : B, @eq C (f (@pair A B x y)) (t (@pair A B x y)))).
Axiom thm_LAMBDA_PAIR : forall {A B C : Type'}, forall f : A -> B -> C, (@ε ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, @eq C (f' (@pair A B x y)) (f x y))) = (fun p : prod A B => f (@fst A B p) (@snd A B p)).
Axiom thm_LAMBDA_TRIPLE_THM : forall {A B C D : Type'}, forall f : (prod A (prod B C)) -> D, (fun t : prod A (prod B C) => f t) = (@ε ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))).
Axiom thm_LAMBDA_TRIPLE : forall {A B C D : Type'}, forall f : A -> B -> C -> D, (@ε ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f x y z))) = (fun t : prod A (prod B C) => f (@fst A (prod B C) t) (@fst B C (@snd A (prod B C) t)) (@snd B C (@snd A (prod B C) t))).
Axiom thm_PAIRED_ETA_THM : forall {A B C D E : Type'}, (forall f : (prod A B) -> C, (@ε ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, @eq C (f' (@pair A B x y)) (f (@pair A B x y)))) = f) /\ ((forall f : (prod A (prod B C)) -> D, (@ε ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))) = f) /\ (forall f : (prod A (prod B (prod C D))) -> E, (@ε ((prod A (prod B (prod C D))) -> E) (fun f' : (prod A (prod B (prod C D))) -> E => forall w : A, forall x : B, forall y : C, forall z : D, @eq E (f' (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))) (f (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))))) = f)).
Axiom thm_FORALL_UNCURRY : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (forall f : A -> B -> C, P f) = (forall f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_UNCURRY : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_CURRY : forall {A B C : Type'}, forall P : ((prod A B) -> C) -> Prop, (exists f : (prod A B) -> C, P f) = (exists f : A -> B -> C, P (@ε ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, @eq C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_CURRY : forall {A B C : Type'}, forall P : ((prod A B) -> C) -> Prop, (forall f : (prod A B) -> C, P f) = (forall f : A -> B -> C, P (@ε ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, @eq C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_EXISTS_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_FORALL_PAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> prod B C) -> Prop, (forall f : A -> prod B C, P f) = (forall g : A -> B, forall h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_EXISTS_PAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> prod B C) -> Prop, (exists f : A -> prod B C, P f) = (exists g : A -> B, exists h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_FORALL_UNPAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> B) -> (A -> C) -> Prop, (forall f : A -> B, forall g : A -> C, P f g) = (forall h : A -> prod B C, P (@o A (prod B C) B (@fst B C) h) (@o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_UNPAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> B) -> (A -> C) -> Prop, (exists f : A -> B, exists g : A -> C, P f g) = (exists h : A -> prod B C, P (@o A (prod B C) B (@fst B C) h) (@o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_SWAP_FUN_THM : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : B -> A -> C, P (fun a : A => fun b : B => f b a)).
Axiom thm_FORALL_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (all (@ε ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (forall x : A, forall y : B, P x y).
Axiom thm_EXISTS_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (ex (@ε ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (exists x : A, exists y : B, P x y).
Axiom thm_FORALL_TRIPLED_THM : forall {A B C : Type'}, forall P : A -> B -> C -> Prop, (all (@ε ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, @eq Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (forall x : A, forall y : B, forall z : C, P x y z).
Axiom thm_EXISTS_TRIPLED_THM : forall {A B C : Type'}, forall P : A -> B -> C -> Prop, (ex (@ε ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, @eq Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (exists x : A, exists y : B, exists z : C, P x y z).
Axiom thm_CHOICE_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (@ε (prod A B) (@ε ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (@ε (prod A B) (fun p : prod A B => P (@fst A B p) (@snd A B p))).
Axiom thm_CHOICE_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, forall Q : (prod A B) -> Prop, ((exists x : A, exists y : B, P x y) /\ (forall x : A, forall y : B, (P x y) -> Q (@pair A B x y))) -> Q (@ε (prod A B) (@ε ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))).
Axiom thm_ONE_ONE : forall {A B : Type'}, forall f : A -> B, (@ONE_ONE A B f) = (forall x1 : A, forall x2 : A, ((f x1) = (f x2)) -> x1 = x2).
Axiom thm_ONTO : forall {A B : Type'}, forall f : A -> B, (@ONTO A B f) = (forall y : B, exists x : A, y = (f x)).
Axiom thm_INFINITY_AX : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Axiom thm_IND_SUC_0_EXISTS : exists f : ind -> ind, exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).
Axiom thm_NUM_REP_RULES : (NUM_REP IND_0) /\ (forall i : ind, (NUM_REP i) -> NUM_REP (IND_SUC i)).
Axiom thm_NUM_REP_CASES : forall a : ind, (NUM_REP a) = ((a = IND_0) \/ (exists i : ind, (a = (IND_SUC i)) /\ (NUM_REP i))).
Axiom thm_NUM_REP_INDUCT : forall NUM_REP' : ind -> Prop, ((NUM_REP' IND_0) /\ (forall i : ind, (NUM_REP' i) -> NUM_REP' (IND_SUC i))) -> forall a : ind, (NUM_REP a) -> NUM_REP' a.
Axiom thm_ZERO_DEF : N0 = (mk_num IND_0).
Axiom thm_SUC_DEF : forall n : N, (N.succ n) = (mk_num (IND_SUC (dest_num n))).
Axiom thm_SUC_INJ : forall m : N, forall n : N, ((N.succ m) = (N.succ n)) = (m = n).
Axiom thm_NOT_SUC : forall n : N, ~ ((N.succ n) = N0).
Axiom thm_num_INDUCTION : forall P : N -> Prop, ((P N0) /\ (forall n : N, (P n) -> P (N.succ n))) -> forall n : N, P n.
Axiom thm_num_Axiom : forall {A : Type'}, forall e : A, forall f : A -> N -> A, @ex1 (N -> A) (fun fn : N -> A => ((fn N0) = e) /\ (forall n : N, (fn (N.succ n)) = (f (fn n) n))).
Axiom thm_num_CASES : forall m : N, (m = N0) \/ (exists n : N, m = (N.succ n)).
Axiom thm_PRE : ((N.pred N0) = N0) /\ (forall n : N, (N.pred (N.succ n)) = n).
Axiom thm_ADD : (forall n : N, (N.add N0 n) = n) /\ (forall m : N, forall n : N, (N.add (N.succ m) n) = (N.succ (N.add m n))).
Axiom thm_ADD_0 : forall m : N, (N.add m N0) = m.
Axiom thm_ADD_SUC : forall m : N, forall n : N, (N.add m (N.succ n)) = (N.succ (N.add m n)).
Axiom thm_ADD_CLAUSES : (forall n : N, (N.add N0 n) = n) /\ ((forall m : N, (N.add m N0) = m) /\ ((forall m : N, forall n : N, (N.add (N.succ m) n) = (N.succ (N.add m n))) /\ (forall m : N, forall n : N, (N.add m (N.succ n)) = (N.succ (N.add m n))))).
Axiom thm_ADD_SYM : forall m : N, forall n : N, (N.add m n) = (N.add n m).
Axiom thm_ADD_ASSOC : forall m : N, forall n : N, forall p : N, (N.add m (N.add n p)) = (N.add (N.add m n) p).
Axiom thm_ADD_AC : forall (n : N) (m : N) (p : N), ((N.add m n) = (N.add n m)) /\ (((N.add (N.add m n) p) = (N.add m (N.add n p))) /\ ((N.add m (N.add n p)) = (N.add n (N.add m p)))).
Axiom thm_ADD_EQ_0 : forall m : N, forall n : N, ((N.add m n) = N0) = ((m = N0) /\ (n = N0)).
Axiom thm_EQ_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, ((N.add m n) = (N.add m p)) = (n = p).
Axiom thm_EQ_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, ((N.add m p) = (N.add n p)) = (m = n).
Axiom thm_EQ_ADD_LCANCEL_0 : forall m : N, forall n : N, ((N.add m n) = m) = (n = N0).
Axiom thm_EQ_ADD_RCANCEL_0 : forall m : N, forall n : N, ((N.add m n) = n) = (m = N0).
Axiom thm_BIT0 : forall n : N, (BIT0 n) = (N.add n n).
Axiom thm_BIT1 : forall n : N, (BIT1 n) = (N.succ (N.add n n)).
Axiom thm_BIT0_THM : forall n : N, ((BIT0 n)) = (N.add (n) (n)).
Axiom thm_BIT1_THM : forall n : N, ((BIT1 n)) = (N.succ (N.add (n) (n))).
Axiom thm_ONE : ((BIT1 N0)) = (N.succ N0).
Axiom thm_TWO : ((BIT0 (BIT1 N0))) = (N.succ ((BIT1 N0))).
Axiom thm_ADD1 : forall m : N, (N.succ m) = (N.add m ((BIT1 N0))).
Axiom thm_MULT : (forall n : N, (N.mul N0 n) = N0) /\ (forall m : N, forall n : N, (N.mul (N.succ m) n) = (N.add (N.mul m n) n)).
Axiom thm_MULT_0 : forall m : N, (N.mul m N0) = N0.
Axiom thm_MULT_SUC : forall m : N, forall n : N, (N.mul m (N.succ n)) = (N.add m (N.mul m n)).
Axiom thm_MULT_CLAUSES : (forall n : N, (N.mul N0 n) = N0) /\ ((forall m : N, (N.mul m N0) = N0) /\ ((forall n : N, (N.mul ((BIT1 N0)) n) = n) /\ ((forall m : N, (N.mul m ((BIT1 N0))) = m) /\ ((forall m : N, forall n : N, (N.mul (N.succ m) n) = (N.add (N.mul m n) n)) /\ (forall m : N, forall n : N, (N.mul m (N.succ n)) = (N.add m (N.mul m n))))))).
Axiom thm_MULT_SYM : forall m : N, forall n : N, (N.mul m n) = (N.mul n m).
Axiom thm_LEFT_ADD_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul m (N.add n p)) = (N.add (N.mul m n) (N.mul m p)).
Axiom thm_RIGHT_ADD_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul (N.add m n) p) = (N.add (N.mul m p) (N.mul n p)).
Axiom thm_MULT_ASSOC : forall m : N, forall n : N, forall p : N, (N.mul m (N.mul n p)) = (N.mul (N.mul m n) p).
Axiom thm_MULT_AC : forall (n : N) (m : N) (p : N), ((N.mul m n) = (N.mul n m)) /\ (((N.mul (N.mul m n) p) = (N.mul m (N.mul n p))) /\ ((N.mul m (N.mul n p)) = (N.mul n (N.mul m p)))).
Axiom thm_MULT_EQ_0 : forall m : N, forall n : N, ((N.mul m n) = N0) = ((m = N0) \/ (n = N0)).
Axiom thm_EQ_MULT_LCANCEL : forall m : N, forall n : N, forall p : N, ((N.mul m n) = (N.mul m p)) = ((m = N0) \/ (n = p)).
Axiom thm_EQ_MULT_RCANCEL : forall m : N, forall n : N, forall p : N, ((N.mul m p) = (N.mul n p)) = ((m = n) \/ (p = N0)).
Axiom thm_MULT_2 : forall n : N, (N.mul ((BIT0 (BIT1 N0))) n) = (N.add n n).
Axiom thm_MULT_EQ_1 : forall m : N, forall n : N, ((N.mul m n) = ((BIT1 N0))) = ((m = ((BIT1 N0))) /\ (n = ((BIT1 N0)))).
Axiom thm_EXP : (forall m : N, (N.pow m N0) = ((BIT1 N0))) /\ (forall m : N, forall n : N, (N.pow m (N.succ n)) = (N.mul m (N.pow m n))).
Axiom thm_EXP_EQ_0 : forall m : N, forall n : N, ((N.pow m n) = N0) = ((m = N0) /\ (~ (n = N0))).
Axiom thm_EXP_EQ_1 : forall x : N, forall n : N, ((N.pow x n) = ((BIT1 N0))) = ((x = ((BIT1 N0))) \/ (n = N0)).
Axiom thm_EXP_ZERO : forall n : N, (N.pow N0 n) = (@COND N (n = N0) ((BIT1 N0)) N0).
Axiom thm_EXP_ADD : forall m : N, forall n : N, forall p : N, (N.pow m (N.add n p)) = (N.mul (N.pow m n) (N.pow m p)).
Axiom thm_EXP_ONE : forall n : N, (N.pow ((BIT1 N0)) n) = ((BIT1 N0)).
Axiom thm_EXP_1 : forall n : N, (N.pow n ((BIT1 N0))) = n.
Axiom thm_EXP_2 : forall n : N, (N.pow n ((BIT0 (BIT1 N0)))) = (N.mul n n).
Axiom thm_MULT_EXP : forall p : N, forall m : N, forall n : N, (N.pow (N.mul m n) p) = (N.mul (N.pow m p) (N.pow n p)).
Axiom thm_EXP_MULT : forall m : N, forall n : N, forall p : N, (N.pow m (N.mul n p)) = (N.pow (N.pow m n) p).
Axiom thm_EXP_EXP : forall x : N, forall m : N, forall n : N, (N.pow (N.pow x m) n) = (N.pow x (N.mul m n)).
Axiom thm_LE : (forall m : N, (N.le m N0) = (m = N0)) /\ (forall m : N, forall n : N, (N.le m (N.succ n)) = ((m = (N.succ n)) \/ (N.le m n))).
Axiom thm_LT : (forall m : N, (N.lt m N0) = False) /\ (forall m : N, forall n : N, (N.lt m (N.succ n)) = ((m = n) \/ (N.lt m n))).
Axiom thm_GE : forall n : N, forall m : N, (N.ge m n) = (N.le n m).
Axiom thm_GT : forall n : N, forall m : N, (N.gt m n) = (N.lt n m).
Axiom thm_MAX : forall m : N, forall n : N, (N.max m n) = (@COND N (N.le m n) n m).
Axiom thm_MIN : forall m : N, forall n : N, (N.min m n) = (@COND N (N.le m n) m n).
Axiom thm_LE_SUC_LT : forall m : N, forall n : N, (N.le (N.succ m) n) = (N.lt m n).
Axiom thm_LT_SUC_LE : forall m : N, forall n : N, (N.lt m (N.succ n)) = (N.le m n).
Axiom thm_LE_SUC : forall m : N, forall n : N, (N.le (N.succ m) (N.succ n)) = (N.le m n).
Axiom thm_LT_SUC : forall m : N, forall n : N, (N.lt (N.succ m) (N.succ n)) = (N.lt m n).
Axiom thm_LE_0 : forall n : N, N.le N0 n.
Axiom thm_LT_0 : forall n : N, N.lt N0 (N.succ n).
Axiom thm_LE_REFL : forall n : N, N.le n n.
Axiom thm_LT_REFL : forall n : N, ~ (N.lt n n).
Axiom thm_LT_IMP_NE : forall m : N, forall n : N, (N.lt m n) -> ~ (m = n).
Axiom thm_LE_ANTISYM : forall m : N, forall n : N, ((N.le m n) /\ (N.le n m)) = (m = n).
Axiom thm_LT_ANTISYM : forall m : N, forall n : N, ~ ((N.lt m n) /\ (N.lt n m)).
Axiom thm_LET_ANTISYM : forall m : N, forall n : N, ~ ((N.le m n) /\ (N.lt n m)).
Axiom thm_LTE_ANTISYM : forall m : N, forall n : N, ~ ((N.lt m n) /\ (N.le n m)).
Axiom thm_LE_TRANS : forall m : N, forall n : N, forall p : N, ((N.le m n) /\ (N.le n p)) -> N.le m p.
Axiom thm_LT_TRANS : forall m : N, forall n : N, forall p : N, ((N.lt m n) /\ (N.lt n p)) -> N.lt m p.
Axiom thm_LET_TRANS : forall m : N, forall n : N, forall p : N, ((N.le m n) /\ (N.lt n p)) -> N.lt m p.
Axiom thm_LTE_TRANS : forall m : N, forall n : N, forall p : N, ((N.lt m n) /\ (N.le n p)) -> N.lt m p.
Axiom thm_LE_CASES : forall m : N, forall n : N, (N.le m n) \/ (N.le n m).
Axiom thm_LT_CASES : forall m : N, forall n : N, (N.lt m n) \/ ((N.lt n m) \/ (m = n)).
Axiom thm_LET_CASES : forall m : N, forall n : N, (N.le m n) \/ (N.lt n m).
Axiom thm_LTE_CASES : forall m : N, forall n : N, (N.lt m n) \/ (N.le n m).
Axiom thm_LE_LT : forall m : N, forall n : N, (N.le m n) = ((N.lt m n) \/ (m = n)).
Axiom thm_LT_LE : forall m : N, forall n : N, (N.lt m n) = ((N.le m n) /\ (~ (m = n))).
Axiom thm_NOT_LE : forall m : N, forall n : N, (~ (N.le m n)) = (N.lt n m).
Axiom thm_NOT_LT : forall m : N, forall n : N, (~ (N.lt m n)) = (N.le n m).
Axiom thm_LT_IMP_LE : forall m : N, forall n : N, (N.lt m n) -> N.le m n.
Axiom thm_EQ_IMP_LE : forall m : N, forall n : N, (m = n) -> N.le m n.
Axiom thm_LT_NZ : forall n : N, (N.lt N0 n) = (~ (n = N0)).
Axiom thm_LE_1 : (forall n : N, (~ (n = N0)) -> N.lt N0 n) /\ ((forall n : N, (~ (n = N0)) -> N.le ((BIT1 N0)) n) /\ ((forall n : N, (N.lt N0 n) -> ~ (n = N0)) /\ ((forall n : N, (N.lt N0 n) -> N.le ((BIT1 N0)) n) /\ ((forall n : N, (N.le ((BIT1 N0)) n) -> N.lt N0 n) /\ (forall n : N, (N.le ((BIT1 N0)) n) -> ~ (n = N0)))))).
Axiom thm_LE_EXISTS : forall m : N, forall n : N, (N.le m n) = (exists d : N, n = (N.add m d)).
Axiom thm_LT_EXISTS : forall m : N, forall n : N, (N.lt m n) = (exists d : N, n = (N.add m (N.succ d))).
Axiom thm_LE_ADD : forall m : N, forall n : N, N.le m (N.add m n).
Axiom thm_LE_ADDR : forall m : N, forall n : N, N.le n (N.add m n).
Axiom thm_LT_ADD : forall m : N, forall n : N, (N.lt m (N.add m n)) = (N.lt N0 n).
Axiom thm_LT_ADDR : forall m : N, forall n : N, (N.lt n (N.add m n)) = (N.lt N0 m).
Axiom thm_LE_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.add m n) (N.add m p)) = (N.le n p).
Axiom thm_LE_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.add m p) (N.add n p)) = (N.le m n).
Axiom thm_LT_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.add m n) (N.add m p)) = (N.lt n p).
Axiom thm_LT_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.add m p) (N.add n p)) = (N.lt m n).
Axiom thm_LE_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.le m p) /\ (N.le n q)) -> N.le (N.add m n) (N.add p q).
Axiom thm_LET_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.le m p) /\ (N.lt n q)) -> N.lt (N.add m n) (N.add p q).
Axiom thm_LTE_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.lt m p) /\ (N.le n q)) -> N.lt (N.add m n) (N.add p q).
Axiom thm_LT_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.lt m p) /\ (N.lt n q)) -> N.lt (N.add m n) (N.add p q).
Axiom thm_LT_MULT : forall m : N, forall n : N, (N.lt N0 (N.mul m n)) = ((N.lt N0 m) /\ (N.lt N0 n)).
Axiom thm_LE_MULT2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.le m n) /\ (N.le p q)) -> N.le (N.mul m p) (N.mul n q).
Axiom thm_LT_LMULT : forall m : N, forall n : N, forall p : N, ((~ (m = N0)) /\ (N.lt n p)) -> N.lt (N.mul m n) (N.mul m p).
Axiom thm_LE_MULT_LCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.mul m n) (N.mul m p)) = ((m = N0) \/ (N.le n p)).
Axiom thm_LE_MULT_RCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.mul m p) (N.mul n p)) = ((N.le m n) \/ (p = N0)).
Axiom thm_LT_MULT_LCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.mul m n) (N.mul m p)) = ((~ (m = N0)) /\ (N.lt n p)).
Axiom thm_LT_MULT_RCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.mul m p) (N.mul n p)) = ((N.lt m n) /\ (~ (p = N0))).
Axiom thm_LT_MULT2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.lt m n) /\ (N.lt p q)) -> N.lt (N.mul m p) (N.mul n q).
Axiom thm_LE_SQUARE_REFL : forall n : N, N.le n (N.mul n n).
Axiom thm_LT_POW2_REFL : forall n : N, N.lt n (N.pow ((BIT0 (BIT1 N0))) n).
Axiom thm_WLOG_LE : forall (P : N -> N -> Prop), ((forall m : N, forall n : N, (P m n) = (P n m)) /\ (forall m : N, forall n : N, (N.le m n) -> P m n)) -> forall m : N, forall n : N, P m n.
Axiom thm_WLOG_LT : forall (P : N -> N -> Prop), ((forall m : N, P m m) /\ ((forall m : N, forall n : N, (P m n) = (P n m)) /\ (forall m : N, forall n : N, (N.lt m n) -> P m n))) -> forall m : N, forall y : N, P m y.
Axiom thm_WLOG_LE_3 : forall P : N -> N -> N -> Prop, ((forall x : N, forall y : N, forall z : N, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : N, forall y : N, forall z : N, ((N.le x y) /\ (N.le y z)) -> P x y z)) -> forall x : N, forall y : N, forall z : N, P x y z.
Axiom thm_num_WF : forall P : N -> Prop, (forall n : N, (forall m : N, (N.lt m n) -> P m) -> P n) -> forall n : N, P n.
Axiom thm_num_WOP : forall P : N -> Prop, (exists n : N, P n) = (exists n : N, (P n) /\ (forall m : N, (N.lt m n) -> ~ (P m))).
Axiom thm_num_MAX : forall P : N -> Prop, ((exists x : N, P x) /\ (exists M : N, forall x : N, (P x) -> N.le x M)) = (exists m : N, (P m) /\ (forall x : N, (P x) -> N.le x m)).
Axiom thm_LE_INDUCT : forall P : N -> N -> Prop, ((forall m : N, P m m) /\ (forall m : N, forall n : N, ((N.le m n) /\ (P m n)) -> P m (N.succ n))) -> forall m : N, forall n : N, (N.le m n) -> P m n.
Axiom thm_num_INDUCTION_DOWN : forall P : N -> Prop, forall m : N, ((forall n : N, (N.le m n) -> P n) /\ (forall n : N, ((N.lt n m) /\ (P (N.add n ((BIT1 N0))))) -> P n)) -> forall n : N, P n.
Axiom thm_EVEN : ((N.Even N0) = True) /\ (forall n : N, (N.Even (N.succ n)) = (~ (N.Even n))).
Axiom thm_ODD : ((N.Odd N0) = False) /\ (forall n : N, (N.Odd (N.succ n)) = (~ (N.Odd n))).
Axiom thm_NOT_EVEN : forall n : N, (~ (N.Even n)) = (N.Odd n).
Axiom thm_NOT_ODD : forall n : N, (~ (N.Odd n)) = (N.Even n).
Axiom thm_EVEN_OR_ODD : forall n : N, (N.Even n) \/ (N.Odd n).
Axiom thm_EVEN_AND_ODD : forall n : N, ~ ((N.Even n) /\ (N.Odd n)).
Axiom thm_EVEN_ADD : forall m : N, forall n : N, (N.Even (N.add m n)) = ((N.Even m) = (N.Even n)).
Axiom thm_EVEN_MULT : forall m : N, forall n : N, (N.Even (N.mul m n)) = ((N.Even m) \/ (N.Even n)).
Axiom thm_EVEN_EXP : forall m : N, forall n : N, (N.Even (N.pow m n)) = ((N.Even m) /\ (~ (n = N0))).
Axiom thm_ODD_ADD : forall m : N, forall n : N, (N.Odd (N.add m n)) = (~ ((N.Odd m) = (N.Odd n))).
Axiom thm_ODD_MULT : forall m : N, forall n : N, (N.Odd (N.mul m n)) = ((N.Odd m) /\ (N.Odd n)).
Axiom thm_ODD_EXP : forall m : N, forall n : N, (N.Odd (N.pow m n)) = ((N.Odd m) \/ (n = N0)).
Axiom thm_EVEN_DOUBLE : forall n : N, N.Even (N.mul ((BIT0 (BIT1 N0))) n).
Axiom thm_ODD_DOUBLE : forall n : N, N.Odd (N.succ (N.mul ((BIT0 (BIT1 N0))) n)).
Axiom thm_EVEN_EXISTS_LEMMA : forall n : N, ((N.Even n) -> exists m : N, n = (N.mul ((BIT0 (BIT1 N0))) m)) /\ ((~ (N.Even n)) -> exists m : N, n = (N.succ (N.mul ((BIT0 (BIT1 N0))) m))).
Axiom thm_EVEN_EXISTS : forall n : N, (N.Even n) = (exists m : N, n = (N.mul ((BIT0 (BIT1 N0))) m)).
Axiom thm_ODD_EXISTS : forall n : N, (N.Odd n) = (exists m : N, n = (N.succ (N.mul ((BIT0 (BIT1 N0))) m))).
Axiom thm_EVEN_ODD_DECOMPOSITION : forall n : N, (exists k : N, exists m : N, (N.Odd m) /\ (n = (N.mul (N.pow ((BIT0 (BIT1 N0))) k) m))) = (~ (n = N0)).
Axiom thm_SUB : (forall m : N, (N.sub m N0) = m) /\ (forall m : N, forall n : N, (N.sub m (N.succ n)) = (N.pred (N.sub m n))).
Axiom thm_SUB_0 : forall m : N, ((N.sub N0 m) = N0) /\ ((N.sub m N0) = m).
Axiom thm_SUB_PRESUC : forall m : N, forall n : N, (N.pred (N.sub (N.succ m) n)) = (N.sub m n).
Axiom thm_SUB_SUC : forall m : N, forall n : N, (N.sub (N.succ m) (N.succ n)) = (N.sub m n).
Axiom thm_SUB_REFL : forall n : N, (N.sub n n) = N0.
Axiom thm_ADD_SUB : forall m : N, forall n : N, (N.sub (N.add m n) n) = m.
Axiom thm_ADD_SUB2 : forall m : N, forall n : N, (N.sub (N.add m n) m) = n.
Axiom thm_SUB_EQ_0 : forall m : N, forall n : N, ((N.sub m n) = N0) = (N.le m n).
Axiom thm_ADD_SUBR2 : forall m : N, forall n : N, (N.sub m (N.add m n)) = N0.
Axiom thm_ADD_SUBR : forall m : N, forall n : N, (N.sub n (N.add m n)) = N0.
Axiom thm_SUB_ADD : forall m : N, forall n : N, (N.le n m) -> (N.add (N.sub m n) n) = m.
Axiom thm_SUB_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, (N.sub (N.add m n) (N.add m p)) = (N.sub n p).
Axiom thm_SUB_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, (N.sub (N.add m p) (N.add n p)) = (N.sub m n).
Axiom thm_LEFT_SUB_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul m (N.sub n p)) = (N.sub (N.mul m n) (N.mul m p)).
Axiom thm_RIGHT_SUB_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul (N.sub m n) p) = (N.sub (N.mul m p) (N.mul n p)).
Axiom thm_EVEN_SUB : forall m : N, forall n : N, (N.Even (N.sub m n)) = ((N.le m n) \/ ((N.Even m) = (N.Even n))).
Axiom thm_ODD_SUB : forall m : N, forall n : N, (N.Odd (N.sub m n)) = ((N.lt n m) /\ (~ ((N.Odd m) = (N.Odd n)))).
Axiom thm_FACT : ((fact N0) = ((BIT1 N0))) /\ (forall n : N, (fact (N.succ n)) = (N.mul (N.succ n) (fact n))).
Axiom thm_FACT_LT : forall n : N, N.lt N0 (fact n).
Axiom thm_FACT_LE : forall n : N, N.le ((BIT1 N0)) (fact n).
Axiom thm_FACT_NZ : forall n : N, ~ ((fact n) = N0).
Axiom thm_FACT_MONO : forall m : N, forall n : N, (N.le m n) -> N.le (fact m) (fact n).
Axiom thm_EXP_LT_0 : forall n : N, forall x : N, (N.lt N0 (N.pow x n)) = ((~ (x = N0)) \/ (n = N0)).
Axiom thm_LT_EXP : forall x : N, forall m : N, forall n : N, (N.lt (N.pow x m) (N.pow x n)) = (((N.le ((BIT0 (BIT1 N0))) x) /\ (N.lt m n)) \/ ((x = N0) /\ ((~ (m = N0)) /\ (n = N0)))).
Axiom thm_LE_EXP : forall x : N, forall m : N, forall n : N, (N.le (N.pow x m) (N.pow x n)) = (@COND Prop (x = N0) ((m = N0) -> n = N0) ((x = ((BIT1 N0))) \/ (N.le m n))).
Axiom thm_EQ_EXP : forall x : N, forall m : N, forall n : N, ((N.pow x m) = (N.pow x n)) = (@COND Prop (x = N0) ((m = N0) = (n = N0)) ((x = ((BIT1 N0))) \/ (m = n))).
Axiom thm_EXP_MONO_LE_IMP : forall x : N, forall y : N, forall n : N, (N.le x y) -> N.le (N.pow x n) (N.pow y n).
Axiom thm_EXP_MONO_LT_IMP : forall x : N, forall y : N, forall n : N, ((N.lt x y) /\ (~ (n = N0))) -> N.lt (N.pow x n) (N.pow y n).
Axiom thm_EXP_MONO_LE : forall x : N, forall y : N, forall n : N, (N.le (N.pow x n) (N.pow y n)) = ((N.le x y) \/ (n = N0)).
Axiom thm_EXP_MONO_LT : forall x : N, forall y : N, forall n : N, (N.lt (N.pow x n) (N.pow y n)) = ((N.lt x y) /\ (~ (n = N0))).
Axiom thm_EXP_MONO_EQ : forall x : N, forall y : N, forall n : N, ((N.pow x n) = (N.pow y n)) = ((x = y) \/ (n = N0)).
Axiom thm_DIVMOD_EXIST : forall m : N, forall n : N, (~ (n = N0)) -> exists q : N, exists r : N, (m = (N.add (N.mul q n) r)) /\ (N.lt r n).
Axiom thm_DIVMOD_EXIST_0 : forall m : N, forall n : N, exists q : N, exists r : N, @COND Prop (n = N0) ((q = N0) /\ (r = m)) ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)).
Axiom thm_DIVISION : forall m : N, forall n : N, (~ (n = N0)) -> (m = (N.add (N.mul (N.div m n) n) (N.modulo m n))) /\ (N.lt (N.modulo m n) n).
Axiom thm_DIV_ZERO : forall n : N, (N.div n N0) = N0.
Axiom thm_MOD_ZERO : forall n : N, (N.modulo n N0) = n.
Axiom thm_DIVISION_SIMP : (forall m : N, forall n : N, (N.add (N.mul (N.div m n) n) (N.modulo m n)) = m) /\ (forall m : N, forall n : N, (N.add (N.mul n (N.div m n)) (N.modulo m n)) = m).
Axiom thm_EQ_DIVMOD : forall p : N, forall m : N, forall n : N, (((N.div m p) = (N.div n p)) /\ ((N.modulo m p) = (N.modulo n p))) = (m = n).
Axiom thm_MOD_LT_EQ : forall m : N, forall n : N, (N.lt (N.modulo m n) n) = (~ (n = N0)).
Axiom thm_MOD_LT_EQ_LT : forall m : N, forall n : N, (N.lt (N.modulo m n) n) = (N.lt N0 n).
Axiom thm_DIVMOD_UNIQ_LEMMA : forall m : N, forall n : N, forall q1 : N, forall r1 : N, forall q2 : N, forall r2 : N, (((m = (N.add (N.mul q1 n) r1)) /\ (N.lt r1 n)) /\ ((m = (N.add (N.mul q2 n) r2)) /\ (N.lt r2 n))) -> (q1 = q2) /\ (r1 = r2).
Axiom thm_DIVMOD_UNIQ : forall m : N, forall n : N, forall q : N, forall r : N, ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)) -> ((N.div m n) = q) /\ ((N.modulo m n) = r).
Axiom thm_MOD_UNIQ : forall m : N, forall n : N, forall q : N, forall r : N, ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)) -> (N.modulo m n) = r.
Axiom thm_DIV_UNIQ : forall m : N, forall n : N, forall q : N, forall r : N, ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)) -> (N.div m n) = q.
Axiom thm_MOD_0 : forall n : N, (N.modulo N0 n) = N0.
Axiom thm_DIV_0 : forall n : N, (N.div N0 n) = N0.
Axiom thm_MOD_MULT : forall m : N, forall n : N, (N.modulo (N.mul m n) m) = N0.
Axiom thm_DIV_MULT : forall m : N, forall n : N, (~ (m = N0)) -> (N.div (N.mul m n) m) = n.
Axiom thm_MOD_LT : forall m : N, forall n : N, (N.lt m n) -> (N.modulo m n) = m.
Axiom thm_MOD_EQ_SELF : forall m : N, forall n : N, ((N.modulo m n) = m) = ((n = N0) \/ (N.lt m n)).
Axiom thm_MOD_CASES : forall n : N, forall p : N, (N.lt n (N.mul ((BIT0 (BIT1 N0))) p)) -> (N.modulo n p) = (@COND N (N.lt n p) n (N.sub n p)).
Axiom thm_MOD_ADD_CASES : forall m : N, forall n : N, forall p : N, ((N.lt m p) /\ (N.lt n p)) -> (N.modulo (N.add m n) p) = (@COND N (N.lt (N.add m n) p) (N.add m n) (N.sub (N.add m n) p)).
Axiom thm_MOD_EQ : forall m : N, forall n : N, forall p : N, forall q : N, (m = (N.add n (N.mul q p))) -> (N.modulo m p) = (N.modulo n p).
Axiom thm_DIV_LE : forall m : N, forall n : N, N.le (N.div m n) m.
Axiom thm_DIV_MUL_LE : forall m : N, forall n : N, N.le (N.mul n (N.div m n)) m.
Axiom thm_MOD_LE_TWICE : forall m : N, forall n : N, ((N.lt N0 m) /\ (N.le m n)) -> N.le (N.mul ((BIT0 (BIT1 N0))) (N.modulo n m)) n.
Axiom thm_MOD_1 : forall n : N, (N.modulo n ((BIT1 N0))) = N0.
Axiom thm_DIV_1 : forall n : N, (N.div n ((BIT1 N0))) = n.
Axiom thm_DIV_LT : forall m : N, forall n : N, (N.lt m n) -> (N.div m n) = N0.
Axiom thm_MOD_MOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.modulo m (N.mul n p)) n) = (N.modulo m n).
Axiom thm_MOD_MOD_REFL : forall m : N, forall n : N, (N.modulo (N.modulo m n) n) = (N.modulo m n).
Axiom thm_MOD_MOD_LE : forall m : N, forall n : N, forall p : N, ((~ (n = N0)) /\ (N.le n p)) -> (N.modulo (N.modulo m n) p) = (N.modulo m n).
Axiom thm_MOD_EVEN_2 : forall m : N, forall n : N, (N.Even n) -> (N.modulo (N.modulo m n) ((BIT0 (BIT1 N0)))) = (N.modulo m ((BIT0 (BIT1 N0)))).
Axiom thm_DIV_MULT2 : forall m : N, forall n : N, forall p : N, (~ (m = N0)) -> (N.div (N.mul m n) (N.mul m p)) = (N.div n p).
Axiom thm_MOD_MULT2 : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul m n) (N.mul m p)) = (N.mul m (N.modulo n p)).
Axiom thm_MOD_EXISTS : forall m : N, forall n : N, (exists q : N, m = (N.mul n q)) = (@COND Prop (n = N0) (m = N0) ((N.modulo m n) = N0)).
Axiom thm_LE_RDIV_EQ : forall a : N, forall b : N, forall n : N, (~ (a = N0)) -> (N.le n (N.div b a)) = (N.le (N.mul a n) b).
Axiom thm_RDIV_LT_EQ : forall a : N, forall b : N, forall n : N, (~ (a = N0)) -> (N.lt (N.div b a) n) = (N.lt b (N.mul a n)).
Axiom thm_LE_LDIV_EQ : forall a : N, forall b : N, forall n : N, (~ (a = N0)) -> (N.le (N.div b a) n) = (N.lt b (N.mul a (N.add n ((BIT1 N0))))).
Axiom thm_LDIV_LT_EQ : forall a : N, forall b : N, forall n : N, (~ (a = N0)) -> (N.lt n (N.div b a)) = (N.le (N.mul a (N.add n ((BIT1 N0)))) b).
Axiom thm_LE_LDIV : forall a : N, forall b : N, forall n : N, ((~ (a = N0)) /\ (N.le b (N.mul a n))) -> N.le (N.div b a) n.
Axiom thm_DIV_MONO : forall m : N, forall n : N, forall p : N, (N.le m n) -> N.le (N.div m p) (N.div n p).
Axiom thm_DIV_MONO_LT : forall m : N, forall n : N, forall p : N, ((~ (p = N0)) /\ (N.le (N.add m p) n)) -> N.lt (N.div m p) (N.div n p).
Axiom thm_DIV_EQ_0 : forall m : N, forall n : N, (~ (n = N0)) -> ((N.div m n) = N0) = (N.lt m n).
Axiom thm_MOD_DIV_EQ_0 : forall m : N, forall n : N, (~ (n = N0)) -> (N.div (N.modulo m n) n) = N0.
Axiom thm_MOD_EQ_0 : forall m : N, forall n : N, ((N.modulo m n) = N0) = (exists q : N, m = (N.mul q n)).
Axiom thm_DIV_EQ_SELF : forall m : N, forall n : N, ((N.div m n) = m) = ((m = N0) \/ (n = ((BIT1 N0)))).
Axiom thm_MOD_REFL : forall n : N, (N.modulo n n) = N0.
Axiom thm_EVEN_MOD : forall n : N, (N.Even n) = ((N.modulo n ((BIT0 (BIT1 N0)))) = N0).
Axiom thm_ODD_MOD : forall n : N, (N.Odd n) = ((N.modulo n ((BIT0 (BIT1 N0)))) = ((BIT1 N0))).
Axiom thm_MOD_2_CASES : forall n : N, (N.modulo n ((BIT0 (BIT1 N0)))) = (@COND N (N.Even n) N0 ((BIT1 N0))).
Axiom thm_EVEN_MOD_EVEN : forall m : N, forall n : N, (N.Even n) -> (N.Even (N.modulo m n)) = (N.Even m).
Axiom thm_ODD_MOD_EVEN : forall m : N, forall n : N, (N.Even n) -> (N.Odd (N.modulo m n)) = (N.Odd m).
Axiom thm_HALF_DOUBLE : (forall n : N, (N.div (N.mul ((BIT0 (BIT1 N0))) n) ((BIT0 (BIT1 N0)))) = n) /\ (forall n : N, (N.div (N.mul n ((BIT0 (BIT1 N0)))) ((BIT0 (BIT1 N0)))) = n).
Axiom thm_DOUBLE_HALF : (forall n : N, (N.Even n) -> (N.mul ((BIT0 (BIT1 N0))) (N.div n ((BIT0 (BIT1 N0))))) = n) /\ (forall n : N, (N.Even n) -> (N.mul (N.div n ((BIT0 (BIT1 N0)))) ((BIT0 (BIT1 N0)))) = n).
Axiom thm_MOD_MULT_RMOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul m (N.modulo p n)) n) = (N.modulo (N.mul m p) n).
Axiom thm_MOD_MULT_LMOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul (N.modulo m n) p) n) = (N.modulo (N.mul m p) n).
Axiom thm_MOD_MULT_MOD2 : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul (N.modulo m n) (N.modulo p n)) n) = (N.modulo (N.mul m p) n).
Axiom thm_MOD_EXP_MOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.pow (N.modulo m n) p) n) = (N.modulo (N.pow m p) n).
Axiom thm_MOD_MULT_ADD : (forall m : N, forall n : N, forall p : N, (N.modulo (N.add (N.mul m n) p) n) = (N.modulo p n)) /\ ((forall m : N, forall n : N, forall p : N, (N.modulo (N.add (N.mul n m) p) n) = (N.modulo p n)) /\ ((forall m : N, forall n : N, forall p : N, (N.modulo (N.add p (N.mul m n)) n) = (N.modulo p n)) /\ (forall m : N, forall n : N, forall p : N, (N.modulo (N.add p (N.mul n m)) n) = (N.modulo p n)))).
Axiom thm_DIV_MULT_ADD : (forall a : N, forall b : N, forall n : N, (~ (n = N0)) -> (N.div (N.add (N.mul a n) b) n) = (N.add a (N.div b n))) /\ ((forall a : N, forall b : N, forall n : N, (~ (n = N0)) -> (N.div (N.add (N.mul n a) b) n) = (N.add a (N.div b n))) /\ ((forall a : N, forall b : N, forall n : N, (~ (n = N0)) -> (N.div (N.add b (N.mul a n)) n) = (N.add (N.div b n) a)) /\ (forall a : N, forall b : N, forall n : N, (~ (n = N0)) -> (N.div (N.add b (N.mul n a)) n) = (N.add (N.div b n) a)))).
Axiom thm_MOD_ADD_MOD : forall a : N, forall b : N, forall n : N, (N.modulo (N.add (N.modulo a n) (N.modulo b n)) n) = (N.modulo (N.add a b) n).
Axiom thm_DIV_ADD_MOD : forall a : N, forall b : N, forall n : N, (~ (n = N0)) -> ((N.modulo (N.add a b) n) = (N.add (N.modulo a n) (N.modulo b n))) = ((N.div (N.add a b) n) = (N.add (N.div a n) (N.div b n))).
Axiom thm_MOD_ADD_EQ_EQ : forall n : N, forall x : N, forall y : N, ((N.modulo (N.add x y) n) = (N.add (N.modulo x n) (N.modulo y n))) = ((n = N0) \/ (N.lt (N.add (N.modulo x n) (N.modulo y n)) n)).
Axiom thm_DIV_ADD_EQ_EQ : forall n : N, forall x : N, forall y : N, ((N.div (N.add x y) n) = (N.add (N.div x n) (N.div y n))) = ((n = N0) \/ (N.lt (N.add (N.modulo x n) (N.modulo y n)) n)).
Axiom thm_DIV_ADD_EQ : forall n : N, forall x : N, forall y : N, (N.lt (N.add (N.modulo x n) (N.modulo y n)) n) -> (N.div (N.add x y) n) = (N.add (N.div x n) (N.div y n)).
Axiom thm_MOD_ADD_EQ : forall n : N, forall x : N, forall y : N, (N.lt (N.add (N.modulo x n) (N.modulo y n)) n) -> (N.modulo (N.add x y) n) = (N.add (N.modulo x n) (N.modulo y n)).
Axiom thm_DIV_REFL : forall n : N, (~ (n = N0)) -> (N.div n n) = ((BIT1 N0)).
Axiom thm_MOD_LE : forall m : N, forall n : N, N.le (N.modulo m n) m.
Axiom thm_DIV_MONO2 : forall m : N, forall n : N, forall p : N, ((~ (p = N0)) /\ (N.le p m)) -> N.le (N.div n m) (N.div n p).
Axiom thm_DIV_LE_EXCLUSION : forall a : N, forall b : N, forall c : N, forall d : N, ((~ (b = N0)) /\ (N.lt (N.mul b c) (N.mul (N.add a ((BIT1 N0))) d))) -> N.le (N.div c d) (N.div a b).
Axiom thm_DIV_EQ_EXCLUSION : forall a : N, forall b : N, forall c : N, forall d : N, ((N.lt (N.mul b c) (N.mul (N.add a ((BIT1 N0))) d)) /\ (N.lt (N.mul a d) (N.mul (N.add c ((BIT1 N0))) b))) -> (N.div a b) = (N.div c d).
Axiom thm_MULT_DIV_LE : forall m : N, forall n : N, forall p : N, N.le (N.mul m (N.div n p)) (N.div (N.mul m n) p).
Axiom thm_DIV_DIV : forall m : N, forall n : N, forall p : N, (N.div (N.div m n) p) = (N.div m (N.mul n p)).
Axiom thm_DIV_MOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.div m n) p) = (N.div (N.modulo m (N.mul n p)) n).
Axiom thm_MOD_MULT_MOD : forall m : N, forall n : N, forall p : N, (N.modulo m (N.mul n p)) = (N.add (N.mul n (N.modulo (N.div m n) p)) (N.modulo m n)).
Axiom thm_MOD_MOD_EXP_MIN : forall x : N, forall p : N, forall m : N, forall n : N, (N.modulo (N.modulo x (N.pow p m)) (N.pow p n)) = (N.modulo x (N.pow p (N.min m n))).
Axiom thm_MOD_EXP : forall m : N, forall n : N, forall p : N, (~ (m = N0)) -> (N.modulo (N.pow m n) (N.pow m p)) = (@COND N ((N.le p n) \/ (m = ((BIT1 N0)))) N0 (N.pow m n)).
Axiom thm_DIV_EXP : forall m : N, forall n : N, forall p : N, (~ (m = N0)) -> (N.div (N.pow m n) (N.pow m p)) = (@COND N (N.le p n) (N.pow m (N.sub n p)) (@COND N (m = ((BIT1 N0))) ((BIT1 N0)) N0)).
Axiom thm_FORALL_LT_MOD_THM : forall P : N -> Prop, forall n : N, (forall a : N, (N.lt a n) -> P a) = ((n = N0) \/ (forall a : N, P (N.modulo a n))).
Axiom thm_FORALL_MOD_THM : forall P : N -> Prop, forall n : N, (~ (n = N0)) -> (forall a : N, P (N.modulo a n)) = (forall a : N, (N.lt a n) -> P a).
Axiom thm_EXISTS_LT_MOD_THM : forall P : N -> Prop, forall n : N, (exists a : N, (N.lt a n) /\ (P a)) = ((~ (n = N0)) /\ (exists a : N, P (N.modulo a n))).
Axiom thm_EXISTS_MOD_THM : forall P : N -> Prop, forall n : N, (~ (n = N0)) -> (exists a : N, P (N.modulo a n)) = (exists a : N, (N.lt a n) /\ (P a)).
Axiom thm_PRE_ELIM_THM : forall (n : N) (P : N -> Prop), (P (N.pred n)) = (forall m : N, ((n = (N.succ m)) \/ ((m = N0) /\ (n = N0))) -> P m).
Axiom thm_SUB_ELIM_THM : forall (a : N) (b : N) (P : N -> Prop), (P (N.sub a b)) = (forall d : N, ((a = (N.add b d)) \/ ((N.lt a b) /\ (d = N0))) -> P d).
Axiom thm_DIVMOD_ELIM_THM : forall (m : N) (n : N) (P : N -> N -> Prop), (P (N.div m n) (N.modulo m n)) = (forall q : N, forall r : N, (((n = N0) /\ ((q = N0) /\ (r = m))) \/ ((m = (N.add (N.mul q n) r)) /\ (N.lt r n))) -> P q r).
Axiom thm_minimal : forall P : N -> Prop, (minimal P) = (@ε N (fun n : N => (P n) /\ (forall m : N, (N.lt m n) -> ~ (P m)))).
Axiom thm_MINIMAL : forall P : N -> Prop, (exists n : N, P n) = ((P (minimal P)) /\ (forall m : N, (N.lt m (minimal P)) -> ~ (P m))).
Axiom thm_MINIMAL_UNIQUE : forall P : N -> Prop, forall n : N, ((P n) /\ (forall m : N, (N.lt m n) -> ~ (P m))) -> (minimal P) = n.
Axiom thm_LE_MINIMAL : forall P : N -> Prop, forall n : N, (exists r : N, P r) -> (N.le n (minimal P)) = (forall i : N, (P i) -> N.le n i).
Axiom thm_MINIMAL_LE : forall P : N -> Prop, forall n : N, (exists r : N, P r) -> (N.le (minimal P) n) = (exists i : N, (N.le i n) /\ (P i)).
Axiom thm_MINIMAL_UBOUND : forall P : N -> Prop, forall n : N, (P n) -> N.le (minimal P) n.
Axiom thm_MINIMAL_LBOUND : forall P : N -> Prop, forall n : N, ((exists r : N, P r) /\ (forall m : N, (N.lt m n) -> ~ (P m))) -> N.le n (minimal P).
Axiom thm_MINIMAL_MONO : forall P : N -> Prop, forall Q : N -> Prop, ((exists n : N, P n) /\ (forall n : N, (P n) -> Q n)) -> N.le (minimal Q) (minimal P).
Axiom thm_TRANSITIVE_STEPWISE_LT_EQ : forall R' : N -> N -> Prop, (forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z) -> (forall m : N, forall n : N, (N.lt m n) -> R' m n) = (forall n : N, R' n (N.succ n)).
Axiom thm_TRANSITIVE_STEPWISE_LT : forall R' : N -> N -> Prop, ((forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : N, R' n (N.succ n))) -> forall m : N, forall n : N, (N.lt m n) -> R' m n.
Axiom thm_TRANSITIVE_STEPWISE_LE_EQ : forall R' : N -> N -> Prop, ((forall x : N, R' x x) /\ (forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z)) -> (forall m : N, forall n : N, (N.le m n) -> R' m n) = (forall n : N, R' n (N.succ n)).
Axiom thm_TRANSITIVE_STEPWISE_LE : forall R' : N -> N -> Prop, ((forall x : N, R' x x) /\ ((forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : N, R' n (N.succ n)))) -> forall m : N, forall n : N, (N.le m n) -> R' m n.
Axiom thm_DEPENDENT_CHOICE_FIXED : forall {A : Type'}, forall P : N -> A -> Prop, forall R' : N -> A -> A -> Prop, forall a : A, ((P N0 a) /\ (forall n : N, forall x : A, (P n x) -> exists y : A, (P (N.succ n) y) /\ (R' n x y))) -> exists f : N -> A, ((f N0) = a) /\ ((forall n : N, P n (f n)) /\ (forall n : N, R' n (f n) (f (N.succ n)))).
Axiom thm_DEPENDENT_CHOICE : forall {A : Type'}, forall P : N -> A -> Prop, forall R' : N -> A -> A -> Prop, ((exists a : A, P N0 a) /\ (forall n : N, forall x : A, (P n x) -> exists y : A, (P (N.succ n) y) /\ (R' n x y))) -> exists f : N -> A, (forall n : N, P n (f n)) /\ (forall n : N, R' n (f n) (f (N.succ n))).
Axiom thm_WF : forall {A : Type'}, forall lt2 : A -> A -> Prop, (@well_founded A lt2) = (forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y))).
Axiom thm_WF_EQ : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (forall P : A -> Prop, (exists x : A, P x) = (exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y)))).
Axiom thm_WF_IND : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (forall P : A -> Prop, (forall x : A, (forall y : A, (lt2 y x) -> P y) -> P x) -> forall x : A, P x).
Axiom thm_WF_DCHAIN : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (~ (exists s : N -> A, forall n : N, lt2 (s (N.succ n)) (s n))).
Axiom thm_WF_DHAIN_TRANSITIVE : forall {A : Type'}, forall lt2 : A -> A -> Prop, (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) -> (@well_founded A lt2) = (~ (exists s : N -> A, forall i : N, forall j : N, (N.lt i j) -> lt2 (s j) (s i))).
Axiom thm_WF_UREC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> B, forall g : A -> B, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g.
Axiom thm_WF_UREC_WF : forall {A : Type'} (lt2 : A -> A -> Prop), (forall H : (A -> Prop) -> A -> Prop, (forall f : A -> Prop, forall g : A -> Prop, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> Prop, forall g : A -> Prop, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g) -> @well_founded A lt2.
Axiom thm_WF_REC_INVARIANT : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, forall S' : A -> B -> Prop, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> ((f z) = (g z)) /\ (S' z (f z))) -> ((H f x) = (H g x)) /\ (S' x (H f x))) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC_WF : forall {A : Type'} (lt2 : A -> A -> Prop), (forall H : (A -> N) -> A -> N, (forall f : A -> N, forall g : A -> N, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> N, forall x : A, (f x) = (H f x)) -> @well_founded A lt2.
Axiom thm_WF_EREC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> @ex1 (A -> B) (fun f : A -> B => forall x : A, (f x) = (H f x)).
Axiom thm_WF_REC_EXISTS : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall P : (A -> B) -> A -> B -> Prop, ((forall f : A -> B, forall g : A -> B, forall x : A, forall y : B, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (P f x y) = (P g x y)) /\ (forall f : A -> B, forall x : A, (forall z : A, (lt2 z x) -> P f z (f z)) -> exists y : B, P f x y)) -> exists f : A -> B, forall x : A, P f x (f x).
Axiom thm_WF_SUBSET : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall lt3 : A -> A -> Prop, ((forall x : A, forall y : A, (lt2 x y) -> lt3 x y) /\ (@well_founded A lt3)) -> @well_founded A lt2.
Axiom thm_WF_RESTRICT : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall P : A -> Prop, (@well_founded A lt2) -> @well_founded A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (lt2 x y))).
Axiom thm_WF_MEASURE_GEN : forall {A B : Type'}, forall lt2 : B -> B -> Prop, forall m : A -> B, (@well_founded B lt2) -> @well_founded A (fun x : A => fun x' : A => lt2 (m x) (m x')).
Axiom thm_WF_LEX_DEPENDENT : forall {A B : Type'}, forall R' : A -> A -> Prop, forall S' : A -> B -> B -> Prop, ((@well_founded A R') /\ (forall a : A, @well_founded B (S' a))) -> @well_founded (prod A B) (@ε ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, @eq ((prod A B) -> Prop) (f (@pair A B r1 s1)) (@ε ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, @eq Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' r1 s1 s2))))))).
Axiom thm_WF_LEX : forall {A B : Type'}, forall R' : A -> A -> Prop, forall S' : B -> B -> Prop, ((@well_founded A R') /\ (@well_founded B S')) -> @well_founded (prod A B) (@ε ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, @eq ((prod A B) -> Prop) (f (@pair A B r1 s1)) (@ε ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, @eq Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' s1 s2))))))).
Axiom thm_WF_POINTWISE : forall {A B : Type'} (lt2 : A -> A -> Prop) (lt3 : B -> B -> Prop), ((@well_founded A lt2) /\ (@well_founded B lt3)) -> @well_founded (prod A B) (@ε ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall x1 : A, forall y1 : B, @eq ((prod A B) -> Prop) (f (@pair A B x1 y1)) (@ε ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall x2 : A, forall y2 : B, @eq Prop (f' (@pair A B x2 y2)) ((lt2 x1 x2) /\ (lt3 y1 y2)))))).
Axiom thm_WF_num : @well_founded N N.lt.
Axiom thm_WF_REC_num : forall {A : Type'}, forall H : (N -> A) -> N -> A, (forall f : N -> A, forall g : N -> A, forall n : N, (forall m : N, (N.lt m n) -> (f m) = (g m)) -> (H f n) = (H g n)) -> exists f : N -> A, forall n : N, (f n) = (H f n).
Axiom thm_MEASURE : forall {A : Type'}, forall m : A -> N, (@MEASURE A m) = (fun x : A => fun y : A => N.lt (m x) (m y)).
Axiom thm_WF_MEASURE : forall {A : Type'}, forall m : A -> N, @well_founded A (@MEASURE A m).
Axiom thm_MEASURE_LE : forall {A : Type'} (a : A) (b : A), forall m : A -> N, (forall y : A, (@MEASURE A m y a) -> @MEASURE A m y b) = (N.le (m a) (m b)).
Axiom thm_WF_ANTISYM : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall x : A, forall y : A, (@well_founded A lt2) -> ~ ((lt2 x y) /\ (lt2 y x)).
Axiom thm_WF_REFL : forall {A : Type'} (lt2 : A -> A -> Prop), forall x : A, (@well_founded A lt2) -> ~ (lt2 x x).
Axiom thm_WF_FALSE : forall {A : Type'}, @well_founded A (fun x : A => fun y : A => False).
Axiom thm_MINIMAL_BAD_SEQUENCE : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall bad : (N -> A) -> Prop, ((@well_founded A lt2) /\ ((forall x : N -> A, (~ (bad x)) -> exists n : N, forall y : N -> A, (forall k : N, (N.lt k n) -> (y k) = (x k)) -> ~ (bad y)) /\ (exists x : N -> A, bad x))) -> exists y : N -> A, (bad y) /\ (forall z : N -> A, forall n : N, ((bad z) /\ (forall k : N, (N.lt k n) -> (z k) = (y k))) -> ~ (lt2 (z n) (y n))).
Axiom thm_WF_REC_TAIL : forall {A B : Type'}, forall P : A -> Prop, forall g : A -> A, forall h : A -> B, exists f : A -> B, forall x : A, (f x) = (@COND B (P x) (f (g x)) (h x)).
Axiom thm_WF_REC_TAIL_GENERAL : forall {A B : Type'} (lt2 : A -> A -> Prop), forall P : (A -> B) -> A -> Prop, forall G : (A -> B) -> A -> A, forall H : (A -> B) -> A -> B, ((@well_founded A lt2) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> ((P f x) = (P g x)) /\ (((G f x) = (G g x)) /\ ((H f x) = (H g x)))) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) /\ (forall f : A -> B, forall x : A, forall y : A, ((P f x) /\ (lt2 y (G f x))) -> lt2 y x)))) -> exists f : A -> B, forall x : A, (f x) = (@COND B (P f x) (f (G f x)) (H f x)).
Axiom thm_ARITH_ZERO : ((N0) = N0) /\ ((BIT0 N0) = N0).
Axiom thm_BIT0_0 : (BIT0 N0) = N0.
Axiom thm_BIT1_0 : (BIT1 N0) = ((BIT1 N0)).
Axiom thm_ARITH_SUC : (forall n : N, (N.succ (n)) = ((N.succ n))) /\ (((N.succ N0) = (BIT1 N0)) /\ ((forall n : N, (N.succ (BIT0 n)) = (BIT1 n)) /\ (forall n : N, (N.succ (BIT1 n)) = (BIT0 (N.succ n))))).
Axiom thm_ARITH_PRE : (forall n : N, (N.pred (n)) = ((N.pred n))) /\ (((N.pred N0) = N0) /\ ((forall n : N, (N.pred (BIT0 n)) = (@COND N (n = N0) N0 (BIT1 (N.pred n)))) /\ (forall n : N, (N.pred (BIT1 n)) = (BIT0 n)))).
Axiom thm_ARITH_ADD : (forall m : N, forall n : N, (N.add (m) (n)) = ((N.add m n))) /\ (((N.add N0 N0) = N0) /\ ((forall n : N, (N.add N0 (BIT0 n)) = (BIT0 n)) /\ ((forall n : N, (N.add N0 (BIT1 n)) = (BIT1 n)) /\ ((forall n : N, (N.add (BIT0 n) N0) = (BIT0 n)) /\ ((forall n : N, (N.add (BIT1 n) N0) = (BIT1 n)) /\ ((forall m : N, forall n : N, (N.add (BIT0 m) (BIT0 n)) = (BIT0 (N.add m n))) /\ ((forall m : N, forall n : N, (N.add (BIT0 m) (BIT1 n)) = (BIT1 (N.add m n))) /\ ((forall m : N, forall n : N, (N.add (BIT1 m) (BIT0 n)) = (BIT1 (N.add m n))) /\ (forall m : N, forall n : N, (N.add (BIT1 m) (BIT1 n)) = (BIT0 (N.succ (N.add m n)))))))))))).
Axiom thm_ARITH_MULT : (forall m : N, forall n : N, (N.mul (m) (n)) = ((N.mul m n))) /\ (((N.mul N0 N0) = N0) /\ ((forall n : N, (N.mul N0 (BIT0 n)) = N0) /\ ((forall n : N, (N.mul N0 (BIT1 n)) = N0) /\ ((forall n : N, (N.mul (BIT0 n) N0) = N0) /\ ((forall n : N, (N.mul (BIT1 n) N0) = N0) /\ ((forall m : N, forall n : N, (N.mul (BIT0 m) (BIT0 n)) = (BIT0 (BIT0 (N.mul m n)))) /\ ((forall m : N, forall n : N, (N.mul (BIT0 m) (BIT1 n)) = (N.add (BIT0 m) (BIT0 (BIT0 (N.mul m n))))) /\ ((forall m : N, forall n : N, (N.mul (BIT1 m) (BIT0 n)) = (N.add (BIT0 n) (BIT0 (BIT0 (N.mul m n))))) /\ (forall m : N, forall n : N, (N.mul (BIT1 m) (BIT1 n)) = (N.add (BIT1 m) (N.add (BIT0 n) (BIT0 (BIT0 (N.mul m n)))))))))))))).
Axiom thm_ARITH_EXP : (forall m : N, forall n : N, (N.pow (m) (n)) = ((N.pow m n))) /\ (((N.pow N0 N0) = (BIT1 N0)) /\ ((forall m : N, (N.pow (BIT0 m) N0) = (BIT1 N0)) /\ ((forall m : N, (N.pow (BIT1 m) N0) = (BIT1 N0)) /\ ((forall n : N, (N.pow N0 (BIT0 n)) = (N.mul (N.pow N0 n) (N.pow N0 n))) /\ ((forall m : N, forall n : N, (N.pow (BIT0 m) (BIT0 n)) = (N.mul (N.pow (BIT0 m) n) (N.pow (BIT0 m) n))) /\ ((forall m : N, forall n : N, (N.pow (BIT1 m) (BIT0 n)) = (N.mul (N.pow (BIT1 m) n) (N.pow (BIT1 m) n))) /\ ((forall n : N, (N.pow N0 (BIT1 n)) = N0) /\ ((forall m : N, forall n : N, (N.pow (BIT0 m) (BIT1 n)) = (N.mul (BIT0 m) (N.mul (N.pow (BIT0 m) n) (N.pow (BIT0 m) n)))) /\ (forall m : N, forall n : N, (N.pow (BIT1 m) (BIT1 n)) = (N.mul (BIT1 m) (N.mul (N.pow (BIT1 m) n) (N.pow (BIT1 m) n)))))))))))).
Axiom thm_ARITH_EVEN : (forall n : N, (N.Even (n)) = (N.Even n)) /\ (((N.Even N0) = True) /\ ((forall n : N, (N.Even (BIT0 n)) = True) /\ (forall n : N, (N.Even (BIT1 n)) = False))).
Axiom thm_ARITH_ODD : (forall n : N, (N.Odd (n)) = (N.Odd n)) /\ (((N.Odd N0) = False) /\ ((forall n : N, (N.Odd (BIT0 n)) = False) /\ (forall n : N, (N.Odd (BIT1 n)) = True))).
Axiom thm_ARITH_LE : (forall m : N, forall n : N, (N.le (m) (n)) = (N.le m n)) /\ (((N.le N0 N0) = True) /\ ((forall n : N, (N.le (BIT0 n) N0) = (N.le n N0)) /\ ((forall n : N, (N.le (BIT1 n) N0) = False) /\ ((forall n : N, (N.le N0 (BIT0 n)) = True) /\ ((forall n : N, (N.le N0 (BIT1 n)) = True) /\ ((forall m : N, forall n : N, (N.le (BIT0 m) (BIT0 n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (N.le (BIT0 m) (BIT1 n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (N.le (BIT1 m) (BIT0 n)) = (N.lt m n)) /\ (forall m : N, forall n : N, (N.le (BIT1 m) (BIT1 n)) = (N.le m n)))))))))).
Axiom thm_ARITH_LT : (forall m : N, forall n : N, (N.lt (m) (n)) = (N.lt m n)) /\ (((N.lt N0 N0) = False) /\ ((forall n : N, (N.lt (BIT0 n) N0) = False) /\ ((forall n : N, (N.lt (BIT1 n) N0) = False) /\ ((forall n : N, (N.lt N0 (BIT0 n)) = (N.lt N0 n)) /\ ((forall n : N, (N.lt N0 (BIT1 n)) = True) /\ ((forall m : N, forall n : N, (N.lt (BIT0 m) (BIT0 n)) = (N.lt m n)) /\ ((forall m : N, forall n : N, (N.lt (BIT0 m) (BIT1 n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (N.lt (BIT1 m) (BIT0 n)) = (N.lt m n)) /\ (forall m : N, forall n : N, (N.lt (BIT1 m) (BIT1 n)) = (N.lt m n)))))))))).
Axiom thm_ARITH_EQ : (forall m : N, forall n : N, ((m) = (n)) = (m = n)) /\ (((N0 = N0) = True) /\ ((forall n : N, ((BIT0 n) = N0) = (n = N0)) /\ ((forall n : N, ((BIT1 n) = N0) = False) /\ ((forall n : N, (N0 = (BIT0 n)) = (N0 = n)) /\ ((forall n : N, (N0 = (BIT1 n)) = False) /\ ((forall m : N, forall n : N, ((BIT0 m) = (BIT0 n)) = (m = n)) /\ ((forall m : N, forall n : N, ((BIT0 m) = (BIT1 n)) = False) /\ ((forall m : N, forall n : N, ((BIT1 m) = (BIT0 n)) = False) /\ (forall m : N, forall n : N, ((BIT1 m) = (BIT1 n)) = (m = n)))))))))).
Axiom thm_ARITH_SUB : (forall m : N, forall n : N, (N.sub (m) (n)) = ((N.sub m n))) /\ (((N.sub N0 N0) = N0) /\ ((forall n : N, (N.sub N0 (BIT0 n)) = N0) /\ ((forall n : N, (N.sub N0 (BIT1 n)) = N0) /\ ((forall n : N, (N.sub (BIT0 n) N0) = (BIT0 n)) /\ ((forall n : N, (N.sub (BIT1 n) N0) = (BIT1 n)) /\ ((forall m : N, forall n : N, (N.sub (BIT0 m) (BIT0 n)) = (BIT0 (N.sub m n))) /\ ((forall m : N, forall n : N, (N.sub (BIT0 m) (BIT1 n)) = (N.pred (BIT0 (N.sub m n)))) /\ ((forall m : N, forall n : N, (N.sub (BIT1 m) (BIT0 n)) = (@COND N (N.le n m) (BIT1 (N.sub m n)) N0)) /\ (forall m : N, forall n : N, (N.sub (BIT1 m) (BIT1 n)) = (BIT0 (N.sub m n))))))))))).
Axiom thm_EXP_2_NE_0 : forall n : N, ~ ((N.pow ((BIT0 (BIT1 N0))) n) = N0).
Axiom thm_INJ_INVERSE2 : forall {A B C : Type'}, forall P : A -> B -> C, (forall x1 : A, forall y1 : B, forall x2 : A, forall y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) /\ (y1 = y2))) -> exists X : C -> A, exists Y : C -> B, forall x : A, forall y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y).
Axiom thm_NUMPAIR : forall x : N, forall y : N, (NUMPAIR x y) = (N.mul (N.pow ((BIT0 (BIT1 N0))) x) (N.add (N.mul ((BIT0 (BIT1 N0))) y) ((BIT1 N0)))).
Axiom thm_NUMPAIR_INJ_LEMMA : forall x1 : N, forall y1 : N, forall x2 : N, forall y2 : N, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) -> x1 = x2.
Axiom thm_NUMPAIR_INJ : forall x1 : N, forall y1 : N, forall x2 : N, forall y2 : N, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((x1 = x2) /\ (y1 = y2)).
Axiom thm_NUMSUM : forall b : Prop, forall x : N, (NUMSUM b x) = (@COND N b (N.succ (N.mul ((BIT0 (BIT1 N0))) x)) (N.mul ((BIT0 (BIT1 N0))) x)).
Axiom thm_NUMSUM_INJ : forall b1 : Prop, forall x1 : N, forall b2 : Prop, forall x2 : N, ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((b1 = b2) /\ (x1 = x2)).
Axiom thm_INJN : forall {A : Type'}, forall m : N, (@INJN A m) = (fun n : N => fun a : A => n = m).
Axiom thm_INJN_INJ : forall {A : Type'}, forall n1 : N, forall n2 : N, ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Axiom thm_INJA : forall {A : Type'}, forall a : A, (@INJA A a) = (fun n : N => fun b : A => b = a).
Axiom thm_INJA_INJ : forall {A : Type'}, forall a1 : A, forall a2 : A, ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Axiom thm_INJF : forall {A : Type'}, forall f : N -> N -> A -> Prop, (@INJF A f) = (fun n : N => f (NUMFST n) (NUMSND n)).
Axiom thm_INJF_INJ : forall {A : Type'}, forall f1 : N -> N -> A -> Prop, forall f2 : N -> N -> A -> Prop, ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Axiom thm_INJP : forall {A : Type'}, forall f1 : N -> A -> Prop, forall f2 : N -> A -> Prop, (@INJP A f1 f2) = (fun n : N => fun a : A => @COND Prop (NUMLEFT n) (f1 (NUMRIGHT n) a) (f2 (NUMRIGHT n) a)).
Axiom thm_INJP_INJ : forall {A : Type'}, forall f1 : N -> A -> Prop, forall f1' : N -> A -> Prop, forall f2 : N -> A -> Prop, forall f2' : N -> A -> Prop, ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((f1 = f1') /\ (f2 = f2')).
Axiom thm_ZCONSTR : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> N -> A -> Prop, (@ZCONSTR A c i r) = (@INJP A (@INJN A (N.succ c)) (@INJP A (@INJA A i) (@INJF A r))).
Axiom thm_ZBOT : forall {A : Type'}, (@ZBOT A) = (@INJP A (@INJN A N0) (@ε (N -> A -> Prop) (fun z : N -> A -> Prop => True))).
Axiom thm_ZCONSTR_ZBOT : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> N -> A -> Prop, ~ ((@ZCONSTR A c i r) = (@ZBOT A)).
Axiom thm_ZRECSPACE_RULES : forall {A : Type'}, (@ZRECSPACE A (@ZBOT A)) /\ (forall c : N, forall i : A, forall r : N -> N -> A -> Prop, (forall n : N, @ZRECSPACE A (r n)) -> @ZRECSPACE A (@ZCONSTR A c i r)).
Axiom thm_ZRECSPACE_CASES : forall {A : Type'}, forall a : N -> A -> Prop, (@ZRECSPACE A a) = ((a = (@ZBOT A)) \/ (exists c : N, exists i : A, exists r : N -> N -> A -> Prop, (a = (@ZCONSTR A c i r)) /\ (forall n : N, @ZRECSPACE A (r n)))).
Axiom thm_ZRECSPACE_INDUCT : forall {A : Type'}, forall ZRECSPACE' : (N -> A -> Prop) -> Prop, ((ZRECSPACE' (@ZBOT A)) /\ (forall c : N, forall i : A, forall r : N -> N -> A -> Prop, (forall n : N, ZRECSPACE' (r n)) -> ZRECSPACE' (@ZCONSTR A c i r))) -> forall a : N -> A -> Prop, (@ZRECSPACE A a) -> ZRECSPACE' a.
Axiom thm_BOTTOM : forall {A : Type'}, (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Axiom thm_CONSTR : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> recspace A, (@CONSTR A c i r) = (@_mk_rec A (@ZCONSTR A c i (fun n : N => @_dest_rec A (r n)))).
Axiom thm_MK_REC_INJ : forall {A : Type'}, forall x : N -> A -> Prop, forall y : N -> A -> Prop, ((@_mk_rec A x) = (@_mk_rec A y)) -> ((@ZRECSPACE A x) /\ (@ZRECSPACE A y)) -> x = y.
Axiom thm_DEST_REC_INJ : forall {A : Type'}, forall x : recspace A, forall y : recspace A, ((@_dest_rec A x) = (@_dest_rec A y)) = (x = y).
Axiom thm_CONSTR_BOT : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> recspace A, ~ ((@CONSTR A c i r) = (@BOTTOM A)).
Axiom thm_CONSTR_INJ : forall {A : Type'}, forall c1 : N, forall i1 : A, forall r1 : N -> recspace A, forall c2 : N, forall i2 : A, forall r2 : N -> recspace A, ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = ((c1 = c2) /\ ((i1 = i2) /\ (r1 = r2))).
Axiom thm_CONSTR_IND : forall {A : Type'}, forall P : (recspace A) -> Prop, ((P (@BOTTOM A)) /\ (forall c : N, forall i : A, forall r : N -> recspace A, (forall n : N, P (r n)) -> P (@CONSTR A c i r))) -> forall x : recspace A, P x.
Axiom thm_CONSTR_REC : forall {A B : Type'}, forall Fn' : N -> A -> (N -> recspace A) -> (N -> B) -> B, exists f : (recspace A) -> B, forall c : N, forall i : A, forall r : N -> recspace A, (f (@CONSTR A c i r)) = (Fn' c i r (fun n : N => f (r n))).
Axiom thm_FCONS : forall {A : Type'}, (forall a : A, forall f : N -> A, (@FCONS A a f N0) = a) /\ (forall a : A, forall f : N -> A, forall n : N, (@FCONS A a f (N.succ n)) = (f n)).
Axiom thm_FCONS_UNDO : forall {A : Type'}, forall f : N -> A, f = (@FCONS A (f N0) (@o N N A f N.succ)).
Axiom thm_FNIL : forall {A : Type'}, forall n : N, (@FNIL A n) = (@ε A (fun x : A => True)).
Axiom thm_sum_INDUCT : forall {A B : Type'}, forall P : (Datatypes.sum A B) -> Prop, ((forall a : A, P (@inl A B a)) /\ (forall a : B, P (@inr A B a))) -> forall x : Datatypes.sum A B, P x.
Axiom thm_sum_RECURSION : forall {A B Z' : Type'}, forall INL' : A -> Z', forall INR' : B -> Z', exists fn : (Datatypes.sum A B) -> Z', (forall a : A, (fn (@inl A B a)) = (INL' a)) /\ (forall a : B, (fn (@inr A B a)) = (INR' a)).
Axiom thm_OUTL : forall {A B : Type'} (x : A), (@OUTL A B (@inl A B x)) = x.
Axiom thm_OUTR : forall {A B : Type'} (y : B), (@OUTR A B (@inr A B y)) = y.
Axiom thm_option_INDUCT : forall {A : Type'}, forall P : (option A) -> Prop, ((P (@None A)) /\ (forall a : A, P (@Some A a))) -> forall x : option A, P x.
Axiom thm_option_RECURSION : forall {A Z' : Type'}, forall NONE' : Z', forall SOME' : A -> Z', exists fn : (option A) -> Z', ((fn (@None A)) = NONE') /\ (forall a : A, (fn (@Some A a)) = (SOME' a)).
Axiom thm_list_INDUCT : forall {A : Type'}, forall P : (list A) -> Prop, ((P (@nil A)) /\ (forall a0 : A, forall a1 : list A, (P a1) -> P (@cons A a0 a1))) -> forall x : list A, P x.
Axiom thm_list_RECURSION : forall {A Z' : Type'}, forall NIL' : Z', forall CONS' : A -> (list A) -> Z' -> Z', exists fn : (list A) -> Z', ((fn (@nil A)) = NIL') /\ (forall a0 : A, forall a1 : list A, (fn (@cons A a0 a1)) = (CONS' a0 a1 (fn a1))).
Axiom thm_FORALL_OPTION_THM : forall {A : Type'}, forall P : (option A) -> Prop, (forall x : option A, P x) = ((P (@None A)) /\ (forall a : A, P (@Some A a))).
Axiom thm_EXISTS_OPTION_THM : forall {A : Type'}, forall P : (option A) -> Prop, (exists x : option A, P x) = ((P (@None A)) \/ (exists a : A, P (@Some A a))).
Axiom thm_option_DISTINCT : forall {A : Type'}, forall a : A, ~ ((@Some A a) = (@None A)).
Axiom thm_option_INJ : forall {A : Type'}, forall a : A, forall b : A, ((@Some A a) = (@Some A b)) = (a = b).
Axiom thm_ISO : forall {A B : Type'}, forall g : B -> A, forall f : A -> B, (@cancel2 A B f g) = ((forall x : B, (f (g x)) = x) /\ (forall y : A, (g (f y)) = y)).
Axiom thm_ISO_REFL : forall {A : Type'}, @cancel2 A A (fun x : A => x) (fun x : A => x).
Axiom thm_ISO_FUN : forall {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A'), ((@cancel2 A A' f f') /\ (@cancel2 B B' g g')) -> @cancel2 (A -> B) (A' -> B') (fun h : A -> B => fun a' : A' => g (h (f' a'))) (fun h : A' -> B' => fun a : A => g' (h (f a))).
Axiom thm_ISO_USAGE : forall {A B : Type'} (g : B -> A) (f : A -> B), (@cancel2 A B f g) -> (forall P : A -> Prop, (forall x : A, P x) = (forall x : B, P (g x))) /\ ((forall P : A -> Prop, (exists x : A, P x) = (exists x : B, P (g x))) /\ (forall a : A, forall b : B, (a = (g b)) = ((f a) = b))).
Axiom thm_HD : forall {A : Type'} (t : list A) (h : A), (@hd A (@cons A h t)) = h.
Axiom thm_TL : forall {A : Type'} (h : A) (t : list A), (@tl A (@cons A h t)) = t.
Axiom thm_APPEND : forall {A : Type'}, (forall l : list A, (@app A (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (@app A (@cons A h t) l) = (@cons A h (@app A t l))).
Axiom thm_REVERSE : forall {A : Type'} (l : list A) (x : A), ((@List.rev A (@nil A)) = (@nil A)) /\ ((@List.rev A (@cons A x l)) = (@app A (@List.rev A l) (@cons A x (@nil A)))).
Axiom thm_LENGTH : forall {A : Type'}, ((@lengthN A (@nil A)) = N0) /\ (forall h : A, forall t : list A, (@lengthN A (@cons A h t)) = (N.succ (@lengthN A t))).
Axiom thm_MAP : forall {A B : Type'}, (forall f : A -> B, (@List.map A B f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (@List.map A B f (@cons A h t)) = (@cons B (f h) (@List.map A B f t))).
Axiom thm_LAST : forall {A : Type'} (h : A) (t : list A), (@last A (@cons A h t)) = (@COND A (t = (@nil A)) h (@last A t)).
Axiom thm_BUTLAST : forall {A : Type'} (h : A) (t : list A), ((@List.removelast A (@nil A)) = (@nil A)) /\ ((@List.removelast A (@cons A h t)) = (@COND (list A) (t = (@nil A)) (@nil A) (@cons A h (@List.removelast A t)))).
Axiom thm_REPLICATE : forall {A : Type'} (n : N) (x : A), ((@repeatN A N0 x) = (@nil A)) /\ ((@repeatN A (N.succ n) x) = (@cons A x (@repeatN A n x))).
Axiom thm_NULL : forall {A : Type'} (h : A) (t : list A), ((@is_nil A (@nil A)) = True) /\ ((@is_nil A (@cons A h t)) = False).
Axiom thm_ALL : forall {A : Type'} (h : A) (P : A -> Prop) (t : list A), ((@List.Forall A P (@nil A)) = True) /\ ((@List.Forall A P (@cons A h t)) = ((P h) /\ (@List.Forall A P t))).
Axiom thm_EX : forall {A : Type'} (h : A) (P : A -> Prop) (t : list A), ((@List.Exists A P (@nil A)) = False) /\ ((@List.Exists A P (@cons A h t)) = ((P h) \/ (@List.Exists A P t))).
Axiom thm_ITLIST : forall {A B : Type'} (h : A) (f : A -> B -> B) (t : list A) (b : B), ((@fold_right_with_perm_args A B f (@nil A) b) = b) /\ ((@fold_right_with_perm_args A B f (@cons A h t) b) = (f h (@fold_right_with_perm_args A B f t b))).
Axiom thm_MEM : forall {A : Type'} (h : A) (x : A) (t : list A), ((@List.In A x (@nil A)) = False) /\ ((@List.In A x (@cons A h t)) = ((x = h) \/ (@List.In A x t))).
Axiom thm_ALL2_DEF : forall {A B : Type'} (h1' : A) (P : A -> B -> Prop) (t1 : list A) (l2 : list B), ((@List.Forall2 A B P (@nil A) l2) = (l2 = (@nil B))) /\ ((@List.Forall2 A B P (@cons A h1' t1) l2) = (@COND Prop (l2 = (@nil B)) False ((P h1' (@hd B l2)) /\ (@List.Forall2 A B P t1 (@tl B l2))))).
Axiom thm_ALL2 : forall {A B : Type'} (h1' : A) (h2' : B) (P : A -> B -> Prop) (t1 : list A) (t2 : list B), ((@List.Forall2 A B P (@nil A) (@nil B)) = True) /\ (((@List.Forall2 A B P (@cons A h1' t1) (@nil B)) = False) /\ (((@List.Forall2 A B P (@nil A) (@cons B h2' t2)) = False) /\ ((@List.Forall2 A B P (@cons A h1' t1) (@cons B h2' t2)) = ((P h1' h2') /\ (@List.Forall2 A B P t1 t2))))).
Axiom thm_MAP2_DEF : forall {A B C : Type'} (h1' : A) (f : A -> B -> C) (t1 : list A) (l : list B), ((@map2 A B C f (@nil A) l) = (@nil C)) /\ ((@map2 A B C f (@cons A h1' t1) l) = (@cons C (f h1' (@hd B l)) (@map2 A B C f t1 (@tl B l)))).
Axiom thm_MAP2 : forall {A B C : Type'} (h1' : A) (h2' : B) (f : A -> B -> C) (t1 : list A) (t2 : list B), ((@map2 A B C f (@nil A) (@nil B)) = (@nil C)) /\ ((@map2 A B C f (@cons A h1' t1) (@cons B h2' t2)) = (@cons C (f h1' h2') (@map2 A B C f t1 t2))).
Axiom thm_EL : forall {A : Type'} (n : N) (l : list A), ((@Nth A N0 l) = (@hd A l)) /\ ((@Nth A (N.succ n) l) = (@Nth A n (@tl A l))).
Axiom thm_FILTER : forall {A : Type'} (h : A) (P : A -> Prop) (t : list A), ((@FILTER A P (@nil A)) = (@nil A)) /\ ((@FILTER A P (@cons A h t)) = (@COND (list A) (P h) (@cons A h (@FILTER A P t)) (@FILTER A P t))).
Axiom thm_ASSOC : forall {A B : Type'} (h : prod A B) (a : A) (t : list (prod A B)), (@assoc A B a (@cons (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (@assoc A B a t)).
Axiom thm_ITLIST2_DEF : forall {A B C : Type'} (h1' : A) (f : A -> B -> C -> C) (t1 : list A) (l2 : list B) (b : C), ((@fold_right2 A B C f (@nil A) l2 b) = b) /\ ((@fold_right2 A B C f (@cons A h1' t1) l2 b) = (f h1' (@hd B l2) (@fold_right2 A B C f t1 (@tl B l2) b))).
Axiom thm_ITLIST2 : forall {A B C : Type'} (h1' : A) (h2' : B) (f : A -> B -> C -> C) (t1 : list A) (t2 : list B) (b : C), ((@fold_right2 A B C f (@nil A) (@nil B) b) = b) /\ ((@fold_right2 A B C f (@cons A h1' t1) (@cons B h2' t2) b) = (f h1' h2' (@fold_right2 A B C f t1 t2 b))).
Axiom thm_ZIP_DEF : forall {A B : Type'} (h1' : A) (t1 : list A) (l2 : list B), ((@zip A B (@nil A) l2) = (@nil (prod A B))) /\ ((@zip A B (@cons A h1' t1) l2) = (@cons (prod A B) (@pair A B h1' (@hd B l2)) (@zip A B t1 (@tl B l2)))).
Axiom thm_ZIP : forall {A B : Type'} (h1' : A) (h2' : B) (t1 : list A) (t2 : list B), ((@zip A B (@nil A) (@nil B)) = (@nil (prod A B))) /\ ((@zip A B (@cons A h1' t1) (@cons B h2' t2)) = (@cons (prod A B) (@pair A B h1' h2') (@zip A B t1 t2))).
Axiom thm_ALLPAIRS : forall {A B : Type'} (h : A) (f : A -> B -> Prop) (t : list A) (l : list B), ((@Forallpairs A B f (@nil A) l) = True) /\ ((@Forallpairs A B f (@cons A h t) l) = ((@List.Forall B (f h) l) /\ (@Forallpairs A B f t l))).
Axiom thm_PAIRWISE : forall {A : Type'} (h : A) (r : A -> A -> Prop) (t : list A), ((@List.ForallOrdPairs A r (@nil A)) = True) /\ ((@List.ForallOrdPairs A r (@cons A h t)) = ((@List.Forall A (r h) t) /\ (@List.ForallOrdPairs A r t))).
Axiom thm_list_of_seq : forall {A : Type'} (s : N -> A) (n : N), ((@list_of_Nseq A s N0) = (@nil A)) /\ ((@list_of_Nseq A s (N.succ n)) = (@app A (@list_of_Nseq A s n) (@cons A (s n) (@nil A)))).
Axiom thm_NOT_CONS_NIL : forall {A : Type'}, forall h : A, forall t : list A, ~ ((@cons A h t) = (@nil A)).
Axiom thm_LAST_CLAUSES : forall {A : Type'} (h : A) (k : A) (t : list A), ((@last A (@cons A h (@nil A))) = h) /\ ((@last A (@cons A h (@cons A k t))) = (@last A (@cons A k t))).
Axiom thm_APPEND_NIL : forall {A : Type'}, forall l : list A, (@app A l (@nil A)) = l.
Axiom thm_APPEND_ASSOC : forall {A : Type'}, forall l : list A, forall m : list A, forall n : list A, (@app A l (@app A m n)) = (@app A (@app A l m) n).
Axiom thm_REVERSE_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@List.rev A (@app A l m)) = (@app A (@List.rev A m) (@List.rev A l)).
Axiom thm_REVERSE_REVERSE : forall {A : Type'}, forall l : list A, (@List.rev A (@List.rev A l)) = l.
Axiom thm_REVERSE_EQ_EMPTY : forall {A : Type'}, forall l : list A, ((@List.rev A l) = (@nil A)) = (l = (@nil A)).
Axiom thm_CONS_11 : forall {A : Type'}, forall h1' : A, forall h2' : A, forall t1 : list A, forall t2 : list A, ((@cons A h1' t1) = (@cons A h2' t2)) = ((h1' = h2') /\ (t1 = t2)).
Axiom thm_list_CASES : forall {A : Type'}, forall l : list A, (l = (@nil A)) \/ (exists h : A, exists t : list A, l = (@cons A h t)).
Axiom thm_LIST_EQ : forall {A : Type'}, forall l1 : list A, forall l2 : list A, (l1 = l2) = (((@lengthN A l1) = (@lengthN A l2)) /\ (forall n : N, (N.lt n (@lengthN A l2)) -> (@Nth A n l1) = (@Nth A n l2))).
Axiom thm_LENGTH_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@lengthN A (@app A l m)) = (N.add (@lengthN A l) (@lengthN A m)).
Axiom thm_MAP_APPEND : forall {A B : Type'}, forall f : A -> B, forall l1 : list A, forall l2 : list A, (@List.map A B f (@app A l1 l2)) = (@app B (@List.map A B f l1) (@List.map A B f l2)).
Axiom thm_LENGTH_MAP : forall {A B : Type'}, forall l : list A, forall f : A -> B, (@lengthN B (@List.map A B f l)) = (@lengthN A l).
Axiom thm_LENGTH_EQ_NIL : forall {A : Type'}, forall l : list A, ((@lengthN A l) = N0) = (l = (@nil A)).
Axiom thm_LENGTH_EQ_CONS : forall {A : Type'}, forall l : list A, forall n : N, ((@lengthN A l) = (N.succ n)) = (exists h : A, exists t : list A, (l = (@cons A h t)) /\ ((@lengthN A t) = n)).
Axiom thm_LENGTH_REVERSE : forall {A : Type'}, forall l : list A, (@lengthN A (@List.rev A l)) = (@lengthN A l).
Axiom thm_MAP_o : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall l : list A, (@List.map A C (@o A B C g f) l) = (@List.map B C g (@List.map A B f l)).
Axiom thm_MAP_EQ : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, forall l : list A, (@List.Forall A (fun x : A => (f x) = (g x)) l) -> (@List.map A B f l) = (@List.map A B g l).
Axiom thm_ALL_IMP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((forall x : A, ((@List.In A x l) /\ (P x)) -> Q x) /\ (@List.Forall A P l)) -> @List.Forall A Q l.
Axiom thm_NOT_EX : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (~ (@List.Exists A P l)) = (@List.Forall A (fun x : A => ~ (P x)) l).
Axiom thm_NOT_ALL : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (~ (@List.Forall A P l)) = (@List.Exists A (fun x : A => ~ (P x)) l).
Axiom thm_ALL_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : list A, (@List.Forall B P (@List.map A B f l)) = (@List.Forall A (@o A B Prop P f) l).
Axiom thm_ALL_EQ : forall {A : Type'} (R' : A -> Prop) (P : A -> Prop) (Q : A -> Prop), forall l : list A, ((@List.Forall A R' l) /\ (forall x : A, (R' x) -> (P x) = (Q x))) -> (@List.Forall A P l) = (@List.Forall A Q l).
Axiom thm_ALL_T : forall {A : Type'}, forall l : list A, @List.Forall A (fun x : A => True) l.
Axiom thm_MAP_EQ_ALL2 : forall {A B : Type'}, forall f : A -> B, forall l : list A, forall m : list A, (@List.Forall2 A A (fun x : A => fun y : A => (f x) = (f y)) l m) -> (@List.map A B f l) = (@List.map A B f m).
Axiom thm_ALL2_MAP : forall {A B : Type'}, forall P : B -> A -> Prop, forall f : A -> B, forall l : list A, (@List.Forall2 B A P (@List.map A B f l) l) = (@List.Forall A (fun a : A => P (f a) a) l).
Axiom thm_MAP_EQ_DEGEN : forall {A : Type'}, forall l : list A, forall f : A -> A, (@List.Forall A (fun x : A => (f x) = x) l) -> (@List.map A A f l) = l.
Axiom thm_ALL2_AND_RIGHT : forall {A B : Type'}, forall l : list A, forall m : list B, forall P : A -> Prop, forall Q : A -> B -> Prop, (@List.Forall2 A B (fun x : A => fun y : B => (P x) /\ (Q x y)) l m) = ((@List.Forall A P l) /\ (@List.Forall2 A B Q l m)).
Axiom thm_ITLIST_APPEND : forall {A B : Type'}, forall f : A -> B -> B, forall a : B, forall l1 : list A, forall l2 : list A, (@fold_right_with_perm_args A B f (@app A l1 l2) a) = (@fold_right_with_perm_args A B f l1 (@fold_right_with_perm_args A B f l2 a)).
Axiom thm_ITLIST_EXTRA : forall {A B : Type'} (a : A) (b : B), forall f : A -> B -> B, forall l : list A, (@fold_right_with_perm_args A B f (@app A l (@cons A a (@nil A))) b) = (@fold_right_with_perm_args A B f l (f a b)).
Axiom thm_ALL_MP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((@List.Forall A (fun x : A => (P x) -> Q x) l) /\ (@List.Forall A P l)) -> @List.Forall A Q l.
Axiom thm_AND_ALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), forall l : list A, ((@List.Forall A P l) /\ (@List.Forall A Q l)) = (@List.Forall A (fun x : A => (P x) /\ (Q x)) l).
Axiom thm_EX_IMP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((forall x : A, ((@List.In A x l) /\ (P x)) -> Q x) /\ (@List.Exists A P l)) -> @List.Exists A Q l.
Axiom thm_ALL_MEM : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (forall x : A, (@List.In A x l) -> P x) = (@List.Forall A P l).
Axiom thm_LENGTH_REPLICATE : forall {A : Type'}, forall n : N, forall x : A, (@lengthN A (@repeatN A n x)) = n.
Axiom thm_MEM_REPLICATE : forall {A : Type'}, forall n : N, forall x : A, forall y : A, (@List.In A x (@repeatN A n y)) = ((x = y) /\ (~ (n = N0))).
Axiom thm_EX_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : list A, (@List.Exists B P (@List.map A B f l)) = (@List.Exists A (@o A B Prop P f) l).
Axiom thm_EXISTS_EX : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list B, (exists x : A, @List.Exists B (P x) l) = (@List.Exists B (fun s : B => exists x : A, P x s) l).
Axiom thm_FORALL_ALL : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list B, (forall x : A, @List.Forall B (P x) l) = (@List.Forall B (fun s : B => forall x : A, P x s) l).
Axiom thm_MEM_APPEND : forall {A : Type'}, forall x : A, forall l1 : list A, forall l2 : list A, (@List.In A x (@app A l1 l2)) = ((@List.In A x l1) \/ (@List.In A x l2)).
Axiom thm_MEM_MAP : forall {A B : Type'}, forall f : A -> B, forall y : B, forall l : list A, (@List.In B y (@List.map A B f l)) = (exists x : A, (@List.In A x l) /\ (y = (f x))).
Axiom thm_FILTER_APPEND : forall {A : Type'}, forall P : A -> Prop, forall l1 : list A, forall l2 : list A, (@FILTER A P (@app A l1 l2)) = (@app A (@FILTER A P l1) (@FILTER A P l2)).
Axiom thm_FILTER_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : list A, (@FILTER B P (@List.map A B f l)) = (@List.map A B f (@FILTER A (@o A B Prop P f) l)).
Axiom thm_MEM_FILTER : forall {A : Type'}, forall P : A -> Prop, forall l : list A, forall x : A, (@List.In A x (@FILTER A P l)) = ((P x) /\ (@List.In A x l)).
Axiom thm_EX_MEM : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (exists x : A, (P x) /\ (@List.In A x l)) = (@List.Exists A P l).
Axiom thm_MAP_FST_ZIP : forall {A B : Type'}, forall l1 : list A, forall l2 : list B, ((@lengthN A l1) = (@lengthN B l2)) -> (@List.map (prod A B) A (@fst A B) (@zip A B l1 l2)) = l1.
Axiom thm_MAP_SND_ZIP : forall {A B : Type'}, forall l1 : list A, forall l2 : list B, ((@lengthN A l1) = (@lengthN B l2)) -> (@List.map (prod A B) B (@snd A B) (@zip A B l1 l2)) = l2.
Axiom thm_LENGTH_ZIP : forall {A B : Type'}, forall l1 : list A, forall l2 : list B, ((@lengthN A l1) = (@lengthN B l2)) -> (@lengthN (prod A B) (@zip A B l1 l2)) = (@lengthN B l2).
Axiom thm_MEM_ASSOC : forall {A B : Type'}, forall l : list (prod A B), forall x : A, (@List.In (prod A B) (@pair A B x (@assoc A B x l)) l) = (@List.In A x (@List.map (prod A B) A (@fst A B) l)).
Axiom thm_ALL_APPEND : forall {A : Type'}, forall P : A -> Prop, forall l1 : list A, forall l2 : list A, (@List.Forall A P (@app A l1 l2)) = ((@List.Forall A P l1) /\ (@List.Forall A P l2)).
Axiom thm_MEM_EL : forall {A : Type'}, forall l : list A, forall n : N, (N.lt n (@lengthN A l)) -> @List.In A (@Nth A n l) l.
Axiom thm_MEM_EXISTS_EL : forall {A : Type'}, forall l : list A, forall x : A, (@List.In A x l) = (exists i : N, (N.lt i (@lengthN A l)) /\ (x = (@Nth A i l))).
Axiom thm_ALL_EL : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (forall i : N, (N.lt i (@lengthN A l)) -> P (@Nth A i l)) = (@List.Forall A P l).
Axiom thm_ALL2_MAP2 : forall {A B C D : Type'} (P : B -> D -> Prop), forall f : A -> B, forall g : C -> D, forall l : list A, forall m : list C, (@List.Forall2 B D P (@List.map A B f l) (@List.map C D g m)) = (@List.Forall2 A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_AND_ALL2 : forall {A B : Type'}, forall P : A -> B -> Prop, forall Q : A -> B -> Prop, forall l : list A, forall m : list B, ((@List.Forall2 A B P l m) /\ (@List.Forall2 A B Q l m)) = (@List.Forall2 A B (fun x : A => fun y : B => (P x y) /\ (Q x y)) l m).
Axiom thm_ALLPAIRS_SYM : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list A, forall m : list B, (@Forallpairs A B P l m) = (@Forallpairs B A (fun x : B => fun y : A => P y x) m l).
Axiom thm_ALLPAIRS_MEM : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list A, forall m : list B, (forall x : A, forall y : B, ((@List.In A x l) /\ (@List.In B y m)) -> P x y) = (@Forallpairs A B P l m).
Axiom thm_ALLPAIRS_MAP : forall {A B C D : Type'}, forall P : B -> D -> Prop, forall f : A -> B, forall g : C -> D, forall l : list A, forall m : list C, (@Forallpairs B D P (@List.map A B f l) (@List.map C D g m)) = (@Forallpairs A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_ALLPAIRS_EQ : forall {A B : Type'} (R' : A -> B -> Prop) (R'' : A -> B -> Prop), forall l : list A, forall m : list B, forall P : A -> Prop, forall Q : B -> Prop, ((@List.Forall A P l) /\ ((@List.Forall B Q m) /\ (forall p : A, forall q : B, ((P p) /\ (Q q)) -> (R' p q) = (R'' p q)))) -> (@Forallpairs A B R' l m) = (@Forallpairs A B R'' l m).
Axiom thm_ALL2_ALL : forall {A : Type'}, forall P : A -> A -> Prop, forall l : list A, (@List.Forall2 A A P l l) = (@List.Forall A (fun x : A => P x x) l).
Axiom thm_APPEND_EQ_NIL : forall {A : Type'}, forall l : list A, forall m : list A, ((@app A l m) = (@nil A)) = ((l = (@nil A)) /\ (m = (@nil A))).
Axiom thm_APPEND_LCANCEL : forall {A : Type'}, forall l1 : list A, forall l2 : list A, forall l3 : list A, ((@app A l1 l2) = (@app A l1 l3)) = (l2 = l3).
Axiom thm_APPEND_RCANCEL : forall {A : Type'}, forall l1 : list A, forall l2 : list A, forall l3 : list A, ((@app A l1 l3) = (@app A l2 l3)) = (l1 = l2).
Axiom thm_LENGTH_MAP2 : forall {A B C : Type'}, forall f : A -> B -> C, forall l : list A, forall m : list B, ((@lengthN A l) = (@lengthN B m)) -> (@lengthN C (@map2 A B C f l m)) = (@lengthN B m).
Axiom thm_EL_MAP2 : forall {A B C : Type'}, forall f : A -> B -> C, forall l : list A, forall m : list B, forall k : N, ((N.lt k (@lengthN A l)) /\ (N.lt k (@lengthN B m))) -> (@Nth C k (@map2 A B C f l m)) = (f (@Nth A k l) (@Nth B k m)).
Axiom thm_MAP_EQ_NIL : forall {A B : Type'}, forall f : A -> B, forall l : list A, ((@List.map A B f l) = (@nil B)) = (l = (@nil A)).
Axiom thm_INJECTIVE_MAP : forall {A B : Type'}, forall f : A -> B, (forall l : list A, forall m : list A, ((@List.map A B f l) = (@List.map A B f m)) -> l = m) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_SURJECTIVE_MAP : forall {A B : Type'}, forall f : A -> B, (forall m : list B, exists l : list A, (@List.map A B f l) = m) = (forall y : B, exists x : A, (f x) = y).
Axiom thm_MAP_ID : forall {A : Type'}, forall l : list A, (@List.map A A (fun x : A => x) l) = l.
Axiom thm_MAP_I : forall {A : Type'}, (@List.map A A (@I A)) = (@I (list A)).
Axiom thm_BUTLAST_CLAUSES : forall {A : Type'}, ((@List.removelast A (@nil A)) = (@nil A)) /\ ((forall a : A, (@List.removelast A (@cons A a (@nil A))) = (@nil A)) /\ (forall a : A, forall h : A, forall t : list A, (@List.removelast A (@cons A a (@cons A h t))) = (@cons A a (@List.removelast A (@cons A h t))))).
Axiom thm_BUTLAST_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@List.removelast A (@app A l m)) = (@COND (list A) (m = (@nil A)) (@List.removelast A l) (@app A l (@List.removelast A m))).
Axiom thm_APPEND_BUTLAST_LAST : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@app A (@List.removelast A l) (@cons A (@last A l) (@nil A))) = l.
Axiom thm_LAST_APPEND : forall {A : Type'}, forall p : list A, forall q : list A, (@last A (@app A p q)) = (@COND A (q = (@nil A)) (@last A p) (@last A q)).
Axiom thm_LENGTH_TL : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@lengthN A (@tl A l)) = (N.sub (@lengthN A l) ((BIT1 N0))).
Axiom thm_LAST_REVERSE : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@last A (@List.rev A l)) = (@hd A l).
Axiom thm_HD_REVERSE : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@hd A (@List.rev A l)) = (@last A l).
Axiom thm_EL_APPEND : forall {A : Type'}, forall k : N, forall l : list A, forall m : list A, (@Nth A k (@app A l m)) = (@COND A (N.lt k (@lengthN A l)) (@Nth A k l) (@Nth A (N.sub k (@lengthN A l)) m)).
Axiom thm_EL_TL : forall {A : Type'} (l : list A), forall n : N, (@Nth A n (@tl A l)) = (@Nth A (N.add n ((BIT1 N0))) l).
Axiom thm_EL_CONS : forall {A : Type'}, forall n : N, forall h : A, forall t : list A, (@Nth A n (@cons A h t)) = (@COND A (n = N0) h (@Nth A (N.sub n ((BIT1 N0))) t)).
Axiom thm_LAST_EL : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@last A l) = (@Nth A (N.sub (@lengthN A l) ((BIT1 N0))) l).
Axiom thm_HD_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@hd A (@app A l m)) = (@COND A (l = (@nil A)) (@hd A m) (@hd A l)).
Axiom thm_CONS_HD_TL : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> l = (@cons A (@hd A l) (@tl A l)).
Axiom thm_EL_MAP : forall {A B : Type'}, forall f : A -> B, forall n : N, forall l : list A, (N.lt n (@lengthN A l)) -> (@Nth B n (@List.map A B f l)) = (f (@Nth A n l)).
Axiom thm_MAP_REVERSE : forall {A B : Type'}, forall f : A -> B, forall l : list A, (@List.rev B (@List.map A B f l)) = (@List.map A B f (@List.rev A l)).
Axiom thm_ALL_FILTER : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, (@List.Forall A P (@FILTER A Q l)) = (@List.Forall A (fun x : A => (Q x) -> P x) l).
Axiom thm_APPEND_SING : forall {A : Type'}, forall h : A, forall t : list A, (@app A (@cons A h (@nil A)) t) = (@cons A h t).
Axiom thm_MEM_APPEND_DECOMPOSE_LEFT : forall {A : Type'}, forall x : A, forall l : list A, (@List.In A x l) = (exists l1 : list A, exists l2 : list A, (~ (@List.In A x l1)) /\ (l = (@app A l1 (@cons A x l2)))).
Axiom thm_MEM_APPEND_DECOMPOSE : forall {A : Type'}, forall x : A, forall l : list A, (@List.In A x l) = (exists l1 : list A, exists l2 : list A, l = (@app A l1 (@cons A x l2))).
Axiom thm_PAIRWISE_APPEND : forall {A : Type'}, forall R' : A -> A -> Prop, forall l : list A, forall m : list A, (@List.ForallOrdPairs A R' (@app A l m)) = ((@List.ForallOrdPairs A R' l) /\ ((@List.ForallOrdPairs A R' m) /\ (forall x : A, forall y : A, ((@List.In A x l) /\ (@List.In A y m)) -> R' x y))).
Axiom thm_PAIRWISE_MAP : forall {A B : Type'}, forall R' : B -> B -> Prop, forall f : A -> B, forall l : list A, (@List.ForallOrdPairs B R' (@List.map A B f l)) = (@List.ForallOrdPairs A (fun x : A => fun y : A => R' (f x) (f y)) l).
Axiom thm_PAIRWISE_IMPLIES : forall {A : Type'}, forall R' : A -> A -> Prop, forall R'' : A -> A -> Prop, forall l : list A, ((@List.ForallOrdPairs A R' l) /\ (forall x : A, forall y : A, ((@List.In A x l) /\ ((@List.In A y l) /\ (R' x y))) -> R'' x y)) -> @List.ForallOrdPairs A R'' l.
Axiom thm_PAIRWISE_TRANSITIVE : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall l : list A, (forall x' : A, forall y' : A, forall z : A, ((R' x' y') /\ (R' y' z)) -> R' x' z) -> (@List.ForallOrdPairs A R' (@cons A x (@cons A y l))) = ((R' x y) /\ (@List.ForallOrdPairs A R' (@cons A y l))).
Axiom thm_LENGTH_LIST_OF_SEQ : forall {A : Type'}, forall s : N -> A, forall n : N, (@lengthN A (@list_of_Nseq A s n)) = n.
Axiom thm_EL_LIST_OF_SEQ : forall {A : Type'}, forall s : N -> A, forall m : N, forall n : N, (N.lt m n) -> (@Nth A m (@list_of_Nseq A s n)) = (s m).
Axiom thm_LIST_OF_SEQ_EQ_NIL : forall {A : Type'}, forall s : N -> A, forall n : N, ((@list_of_Nseq A s n) = (@nil A)) = (n = N0).
Axiom thm_MONO_ALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop) (l : list A), (forall x : A, (P x) -> Q x) -> (@List.Forall A P l) -> @List.Forall A Q l.
Axiom thm_MONO_ALL2 : forall {A B : Type'} (P : A -> B -> Prop) (Q : A -> B -> Prop) (l : list A) (l' : list B), (forall x : A, forall y : B, (P x y) -> Q x y) -> (@List.Forall2 A B P l l') -> @List.Forall2 A B Q l l'.
Axiom thm_char_INDUCT : forall P : Ascii.ascii -> Prop, (forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, P (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) -> forall x : Ascii.ascii, P x.
Axiom thm_char_RECURSION : forall {Z' : Type'}, forall f : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Z', exists fn : Ascii.ascii -> Z', forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, (fn (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) = (f a0 a1 a2 a3 a4 a5 a6 a7).
Axiom thm_dist : forall n : N, forall m : N, (dist (@pair N N m n)) = (N.add (N.sub m n) (N.sub n m)).
Axiom thm_DIST_REFL : forall n : N, (dist (@pair N N n n)) = N0.
Axiom thm_DIST_LZERO : forall n : N, (dist (@pair N N N0 n)) = n.
Axiom thm_DIST_RZERO : forall n : N, (dist (@pair N N n N0)) = n.
Axiom thm_DIST_SYM : forall m : N, forall n : N, (dist (@pair N N m n)) = (dist (@pair N N n m)).
Axiom thm_DIST_LADD : forall m : N, forall p : N, forall n : N, (dist (@pair N N (N.add m n) (N.add m p))) = (dist (@pair N N n p)).
Axiom thm_DIST_RADD : forall m : N, forall p : N, forall n : N, (dist (@pair N N (N.add m p) (N.add n p))) = (dist (@pair N N m n)).
Axiom thm_DIST_LADD_0 : forall m : N, forall n : N, (dist (@pair N N (N.add m n) m)) = n.
Axiom thm_DIST_RADD_0 : forall m : N, forall n : N, (dist (@pair N N m (N.add m n))) = n.
Axiom thm_DIST_LMUL : forall m : N, forall n : N, forall p : N, (N.mul m (dist (@pair N N n p))) = (dist (@pair N N (N.mul m n) (N.mul m p))).
Axiom thm_DIST_RMUL : forall m : N, forall n : N, forall p : N, (N.mul (dist (@pair N N m n)) p) = (dist (@pair N N (N.mul m p) (N.mul n p))).
Axiom thm_DIST_EQ_0 : forall m : N, forall n : N, ((dist (@pair N N m n)) = N0) = (m = n).
Axiom thm_DIST_ELIM_THM : forall (y : N) (x : N) (P : N -> Prop), (P (dist (@pair N N x y))) = (forall d : N, ((x = (N.add y d)) -> P d) /\ ((y = (N.add x d)) -> P d)).
Axiom thm_DIST_TRIANGLE_LE : forall m : N, forall n : N, forall p : N, forall q : N, (N.le (N.add (dist (@pair N N m n)) (dist (@pair N N n p))) q) -> N.le (dist (@pair N N m p)) q.
Axiom thm_DIST_TRIANGLES_LE : forall m : N, forall n : N, forall p : N, forall q : N, forall r : N, forall s : N, ((N.le (dist (@pair N N m n)) r) /\ (N.le (dist (@pair N N p q)) s)) -> N.le (dist (@pair N N m p)) (N.add (dist (@pair N N n q)) (N.add r s)).
Axiom thm_BOUNDS_LINEAR : forall A : N, forall B : N, forall C : N, (forall n : N, N.le (N.mul A n) (N.add (N.mul B n) C)) = (N.le A B).
Axiom thm_BOUNDS_LINEAR_0 : forall A : N, forall B : N, (forall n : N, N.le (N.mul A n) B) = (A = N0).
Axiom thm_BOUNDS_DIVIDED : forall P : N -> N, (exists B : N, forall n : N, N.le (P n) B) = (exists A : N, exists B : N, forall n : N, N.le (N.mul n (P n)) (N.add (N.mul A n) B)).
Axiom thm_BOUNDS_NOTZERO : forall P : N -> N -> N, forall A : N, forall B : N, (((P N0 N0) = N0) /\ (forall m : N, forall n : N, N.le (P m n) (N.add (N.mul A (N.add m n)) B))) -> exists B' : N, forall m : N, forall n : N, N.le (P m n) (N.mul B' (N.add m n)).
Axiom thm_BOUNDS_IGNORE : forall P : N -> N, forall Q : N -> N, (exists B : N, forall i : N, N.le (P i) (N.add (Q i) B)) = (exists B : N, exists N' : N, forall i : N, (N.le N' i) -> N.le (P i) (N.add (Q i) B)).
Axiom thm_is_nadd : forall x : N -> N, (is_nadd x) = (exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (x n)) (N.mul n (x m)))) (N.mul B (N.add m n))).
Axiom thm_is_nadd_0 : is_nadd (fun n : N => N0).
Axiom thm_NADD_CAUCHY : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (dest_nadd x n)) (N.mul n (dest_nadd x m)))) (N.mul B (N.add m n)).
Axiom thm_NADD_BOUND : forall x : nadd, exists A : N, exists B : N, forall n : N, N.le (dest_nadd x n) (N.add (N.mul A n) B).
Axiom thm_NADD_MULTIPLICATIVE : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.mul m n)) (N.mul m (dest_nadd x n)))) (N.add (N.mul B m) B).
Axiom thm_NADD_ADDITIVE : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.add m n)) (N.add (dest_nadd x m) (dest_nadd x n)))) B.
Axiom thm_NADD_SUC : forall x : nadd, exists B : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.succ n)) (dest_nadd x n))) B.
Axiom thm_NADD_DIST_LEMMA : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.add m n)) (dest_nadd x m))) (N.mul B n).
Axiom thm_NADD_DIST : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x m) (dest_nadd x n))) (N.mul B (dist (@pair N N m n))).
Axiom thm_NADD_ALTMUL : forall x : nadd, forall y : nadd, exists A : N, exists B : N, forall n : N, N.le (dist (@pair N N (N.mul n (dest_nadd x (dest_nadd y n))) (N.mul (dest_nadd x n) (dest_nadd y n)))) (N.add (N.mul A n) B).
Axiom thm_nadd_eq : forall x : nadd, forall y : nadd, (nadd_eq x y) = (exists B : N, forall n : N, N.le (dist (@pair N N (dest_nadd x n) (dest_nadd y n))) B).
Axiom thm_NADD_EQ_REFL : forall x : nadd, nadd_eq x x.
Axiom thm_NADD_EQ_SYM : forall x : nadd, forall y : nadd, (nadd_eq x y) = (nadd_eq y x).
Axiom thm_NADD_EQ_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_eq x y) /\ (nadd_eq y z)) -> nadd_eq x z.
Axiom thm_nadd_of_num : forall k : N, (nadd_of_num k) = (mk_nadd (fun n : N => N.mul k n)).
Axiom thm_NADD_OF_NUM : forall k : N, (dest_nadd (nadd_of_num k)) = (fun n : N => N.mul k n).
Axiom thm_NADD_OF_NUM_WELLDEF : forall m : N, forall n : N, (m = n) -> nadd_eq (nadd_of_num m) (nadd_of_num n).
Axiom thm_NADD_OF_NUM_EQ : forall m : N, forall n : N, (nadd_eq (nadd_of_num m) (nadd_of_num n)) = (m = n).
Axiom thm_nadd_le : forall x : nadd, forall y : nadd, (nadd_le x y) = (exists B : N, forall n : N, N.le (dest_nadd x n) (N.add (dest_nadd y n) B)).
Axiom thm_NADD_LE_WELLDEF_LEMMA : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ ((nadd_eq y y') /\ (nadd_le x y))) -> nadd_le x' y'.
Axiom thm_NADD_LE_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> (nadd_le x y) = (nadd_le x' y').
Axiom thm_NADD_LE_REFL : forall x : nadd, nadd_le x x.
Axiom thm_NADD_LE_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_le x y) /\ (nadd_le y z)) -> nadd_le x z.
Axiom thm_NADD_LE_ANTISYM : forall x : nadd, forall y : nadd, ((nadd_le x y) /\ (nadd_le y x)) = (nadd_eq x y).
Axiom thm_NADD_LE_TOTAL_LEMMA : forall x : nadd, forall y : nadd, (~ (nadd_le x y)) -> forall B : N, exists n : N, (~ (n = N0)) /\ (N.lt (N.add (dest_nadd y n) B) (dest_nadd x n)).
Axiom thm_NADD_LE_TOTAL : forall x : nadd, forall y : nadd, (nadd_le x y) \/ (nadd_le y x).
Axiom thm_NADD_ARCH : forall x : nadd, exists n : N, nadd_le x (nadd_of_num n).
Axiom thm_NADD_OF_NUM_LE : forall m : N, forall n : N, (nadd_le (nadd_of_num m) (nadd_of_num n)) = (N.le m n).
Axiom thm_nadd_add : forall x : nadd, forall y : nadd, (nadd_add x y) = (mk_nadd (fun n : N => N.add (dest_nadd x n) (dest_nadd y n))).
Axiom thm_NADD_ADD : forall x : nadd, forall y : nadd, (dest_nadd (nadd_add x y)) = (fun n : N => N.add (dest_nadd x n) (dest_nadd y n)).
Axiom thm_NADD_ADD_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_add x y) (nadd_add x' y').
Axiom thm_NADD_ADD_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_add x y) (nadd_add y x).
Axiom thm_NADD_ADD_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z).
Axiom thm_NADD_ADD_LID : forall x : nadd, nadd_eq (nadd_add (nadd_of_num N0) x) x.
Axiom thm_NADD_ADD_LCANCEL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_eq (nadd_add x y) (nadd_add x z)) -> nadd_eq y z.
Axiom thm_NADD_LE_ADD : forall x : nadd, forall y : nadd, nadd_le x (nadd_add x y).
Axiom thm_NADD_LE_EXISTS : forall x : nadd, forall y : nadd, (nadd_le x y) -> exists d : nadd, nadd_eq y (nadd_add x d).
Axiom thm_NADD_OF_NUM_ADD : forall m : N, forall n : N, nadd_eq (nadd_add (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (N.add m n)).
Axiom thm_nadd_mul : forall x : nadd, forall y : nadd, (nadd_mul x y) = (mk_nadd (fun n : N => dest_nadd x (dest_nadd y n))).
Axiom thm_NADD_MUL : forall x : nadd, forall y : nadd, (dest_nadd (nadd_mul x y)) = (fun n : N => dest_nadd x (dest_nadd y n)).
Axiom thm_NADD_MUL_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_mul x y) (nadd_mul y x).
Axiom thm_NADD_MUL_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_mul y z)) (nadd_mul (nadd_mul x y) z).
Axiom thm_NADD_MUL_LID : forall x : nadd, nadd_eq (nadd_mul (nadd_of_num ((BIT1 N0))) x) x.
Axiom thm_NADD_LDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_add y z)) (nadd_add (nadd_mul x y) (nadd_mul x z)).
Axiom thm_NADD_MUL_WELLDEF_LEMMA : forall x : nadd, forall y : nadd, forall y' : nadd, (nadd_eq y y') -> nadd_eq (nadd_mul x y) (nadd_mul x y').
Axiom thm_NADD_MUL_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_mul x y) (nadd_mul x' y').
Axiom thm_NADD_OF_NUM_MUL : forall m : N, forall n : N, nadd_eq (nadd_mul (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (N.mul m n)).
Axiom thm_NADD_LE_0 : forall x : nadd, nadd_le (nadd_of_num N0) x.
Axiom thm_NADD_EQ_IMP_LE : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_le x y.
Axiom thm_NADD_LE_LMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le y z) -> nadd_le (nadd_mul x y) (nadd_mul x z).
Axiom thm_NADD_LE_RMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le x y) -> nadd_le (nadd_mul x z) (nadd_mul y z).
Axiom thm_NADD_LE_RADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x z) (nadd_add y z)) = (nadd_le x y).
Axiom thm_NADD_LE_LADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x y) (nadd_add x z)) = (nadd_le y z).
Axiom thm_NADD_RDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul (nadd_add x y) z) (nadd_add (nadd_mul x z) (nadd_mul y z)).
Axiom thm_NADD_ARCH_MULT : forall x : nadd, forall k : N, (~ (nadd_eq x (nadd_of_num N0))) -> exists N' : N, nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num N') x).
Axiom thm_NADD_ARCH_ZERO : forall x : nadd, forall k : nadd, (forall n : N, nadd_le (nadd_mul (nadd_of_num n) x) k) -> nadd_eq x (nadd_of_num N0).
Axiom thm_NADD_ARCH_LEMMA : forall x : nadd, forall y : nadd, forall z : nadd, (forall n : N, nadd_le (nadd_mul (nadd_of_num n) x) (nadd_add (nadd_mul (nadd_of_num n) y) z)) -> nadd_le x y.
Axiom thm_NADD_COMPLETE : forall P : nadd -> Prop, ((exists x : nadd, P x) /\ (exists M : nadd, forall x : nadd, (P x) -> nadd_le x M)) -> exists M : nadd, (forall x : nadd, (P x) -> nadd_le x M) /\ (forall M' : nadd, (forall x : nadd, (P x) -> nadd_le x M') -> nadd_le M M').
Axiom thm_NADD_UBOUND : forall x : nadd, exists B : N, exists N' : N, forall n : N, (N.le N' n) -> N.le (dest_nadd x n) (N.mul B n).
Axiom thm_NADD_NONZERO : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists N' : N, forall n : N, (N.le N' n) -> ~ ((dest_nadd x n) = N0).
Axiom thm_NADD_LBOUND : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists A : N, exists N' : N, forall n : N, (N.le N' n) -> N.le n (N.mul A (dest_nadd x n)).
Axiom thm_nadd_rinv : forall x : nadd, (nadd_rinv x) = (fun n : N => N.div (N.mul n n) (dest_nadd x n)).
Axiom thm_NADD_MUL_LINV_LEMMA0 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists A : N, exists B : N, forall n : N, N.le (nadd_rinv x n) (N.add (N.mul A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA1 : forall x : nadd, forall n : N, (~ ((dest_nadd x n) = N0)) -> N.le (dist (@pair N N (N.mul (dest_nadd x n) (nadd_rinv x n)) (N.mul n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA2 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists N' : N, forall n : N, (N.le N' n) -> N.le (dist (@pair N N (N.mul (dest_nadd x n) (nadd_rinv x n)) (N.mul n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA3 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists N' : N, forall m : N, forall n : N, (N.le N' n) -> N.le (dist (@pair N N (N.mul m (N.mul (dest_nadd x m) (N.mul (dest_nadd x n) (nadd_rinv x n)))) (N.mul m (N.mul (dest_nadd x m) (N.mul n n))))) (N.mul m (N.mul (dest_nadd x m) (dest_nadd x n))).
Axiom thm_NADD_MUL_LINV_LEMMA4 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (N.mul (N.mul (dest_nadd x m) (dest_nadd x n)) (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m))))) (N.add (N.mul (N.mul m n) (dist (@pair N N (N.mul m (dest_nadd x n)) (N.mul n (dest_nadd x m))))) (N.mul (N.mul (dest_nadd x m) (dest_nadd x n)) (N.add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA5 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists B : N, exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (N.mul (N.mul (dest_nadd x m) (dest_nadd x n)) (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m))))) (N.mul B (N.mul (N.mul m n) (N.add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA6 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists B : N, exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (N.mul (N.mul m n) (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m))))) (N.mul B (N.mul (N.mul m n) (N.add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA7 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists B : N, exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m)))) (N.mul B (N.add m n)).
Axiom thm_NADD_MUL_LINV_LEMMA7a : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> forall N' : N, exists A : N, exists B : N, forall m : N, forall n : N, (N.le m N') -> N.le (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m)))) (N.add (N.mul A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA8 : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m)))) (N.mul B (N.add m n)).
Axiom thm_nadd_inv : forall x : nadd, (nadd_inv x) = (@COND nadd (nadd_eq x (nadd_of_num N0)) (nadd_of_num N0) (mk_nadd (nadd_rinv x))).
Axiom thm_NADD_INV : forall x : nadd, (dest_nadd (nadd_inv x)) = (@COND (N -> N) (nadd_eq x (nadd_of_num N0)) (fun n : N => N0) (nadd_rinv x)).
Axiom thm_NADD_MUL_LINV : forall x : nadd, (~ (nadd_eq x (nadd_of_num N0))) -> nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num ((BIT1 N0))).
Axiom thm_NADD_INV_0 : nadd_eq (nadd_inv (nadd_of_num N0)) (nadd_of_num N0).
Axiom thm_NADD_INV_WELLDEF : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_eq (nadd_inv x) (nadd_inv y).
Axiom thm_HREAL_OF_NUM_EQ : forall m : N, forall n : N, ((hreal_of_num m) = (hreal_of_num n)) = (m = n).
Axiom thm_HREAL_OF_NUM_LE : forall m : N, forall n : N, (hreal_le (hreal_of_num m) (hreal_of_num n)) = (N.le m n).
Axiom thm_HREAL_OF_NUM_ADD : forall m : N, forall n : N, (hreal_add (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (N.add m n)).
Axiom thm_HREAL_OF_NUM_MUL : forall m : N, forall n : N, (hreal_mul (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (N.mul m n)).
Axiom thm_HREAL_LE_REFL : forall x : hreal, hreal_le x x.
Axiom thm_HREAL_LE_TRANS : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_le x y) /\ (hreal_le y z)) -> hreal_le x z.
Axiom thm_HREAL_LE_ANTISYM : forall x : hreal, forall y : hreal, ((hreal_le x y) /\ (hreal_le y x)) = (x = y).
Axiom thm_HREAL_LE_TOTAL : forall x : hreal, forall y : hreal, (hreal_le x y) \/ (hreal_le y x).
Axiom thm_HREAL_LE_ADD : forall x : hreal, forall y : hreal, hreal_le x (hreal_add x y).
Axiom thm_HREAL_LE_EXISTS : forall x : hreal, forall y : hreal, (hreal_le x y) -> exists d : hreal, y = (hreal_add x d).
Axiom thm_HREAL_ARCH : forall x : hreal, exists n : N, hreal_le x (hreal_of_num n).
Axiom thm_HREAL_ADD_SYM : forall x : hreal, forall y : hreal, (hreal_add x y) = (hreal_add y x).
Axiom thm_HREAL_ADD_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_add x (hreal_add y z)) = (hreal_add (hreal_add x y) z).
Axiom thm_HREAL_ADD_LID : forall x : hreal, (hreal_add (hreal_of_num N0) x) = x.
Axiom thm_HREAL_ADD_LCANCEL : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_add x y) = (hreal_add x z)) -> y = z.
Axiom thm_HREAL_MUL_SYM : forall x : hreal, forall y : hreal, (hreal_mul x y) = (hreal_mul y x).
Axiom thm_HREAL_MUL_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_mul y z)) = (hreal_mul (hreal_mul x y) z).
Axiom thm_HREAL_MUL_LID : forall x : hreal, (hreal_mul (hreal_of_num ((BIT1 N0))) x) = x.
Axiom thm_HREAL_ADD_LDISTRIB : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_add y z)) = (hreal_add (hreal_mul x y) (hreal_mul x z)).
Axiom thm_HREAL_MUL_LINV : forall x : hreal, (~ (x = (hreal_of_num N0))) -> (hreal_mul (hreal_inv x) x) = (hreal_of_num ((BIT1 N0))).
Axiom thm_HREAL_INV_0 : (hreal_inv (hreal_of_num N0)) = (hreal_of_num N0).
Axiom thm_HREAL_LE_EXISTS_DEF : forall m : hreal, forall n : hreal, (hreal_le m n) = (exists d : hreal, n = (hreal_add m d)).
Axiom thm_HREAL_EQ_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m n) = (hreal_add m p)) = (n = p).
Axiom thm_HREAL_EQ_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m p) = (hreal_add n p)) = (m = n).
Axiom thm_HREAL_LE_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m n) (hreal_add m p)) = (hreal_le n p).
Axiom thm_HREAL_LE_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m p) (hreal_add n p)) = (hreal_le m n).
Axiom thm_HREAL_ADD_RID : forall n : hreal, (hreal_add n (hreal_of_num N0)) = n.
Axiom thm_HREAL_ADD_RDISTRIB : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_mul (hreal_add m n) p) = (hreal_add (hreal_mul m p) (hreal_mul n p)).
Axiom thm_HREAL_MUL_LZERO : forall m : hreal, (hreal_mul (hreal_of_num N0) m) = (hreal_of_num N0).
Axiom thm_HREAL_MUL_RZERO : forall m : hreal, (hreal_mul m (hreal_of_num N0)) = (hreal_of_num N0).
Axiom thm_HREAL_ADD_AC : forall (n : hreal) (m : hreal) (p : hreal), ((hreal_add m n) = (hreal_add n m)) /\ (((hreal_add (hreal_add m n) p) = (hreal_add m (hreal_add n p))) /\ ((hreal_add m (hreal_add n p)) = (hreal_add n (hreal_add m p)))).
Axiom thm_HREAL_LE_ADD2 : forall a : hreal, forall b : hreal, forall c : hreal, forall d : hreal, ((hreal_le a b) /\ (hreal_le c d)) -> hreal_le (hreal_add a c) (hreal_add b d).
Axiom thm_HREAL_LE_MUL_RCANCEL_IMP : forall a : hreal, forall b : hreal, forall c : hreal, (hreal_le a b) -> hreal_le (hreal_mul a c) (hreal_mul b c).
Axiom thm_treal_of_num : forall n : N, (treal_of_num n) = (@pair hreal hreal (hreal_of_num n) (hreal_of_num N0)).
Axiom thm_treal_neg : forall y : hreal, forall x : hreal, (treal_neg (@pair hreal hreal x y)) = (@pair hreal hreal y x).
Axiom thm_treal_add : forall x1 : hreal, forall x2 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_add (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add x1 x2) (hreal_add y1 y2)).
Axiom thm_treal_mul : forall x1 : hreal, forall y2 : hreal, forall y1 : hreal, forall x2 : hreal, (treal_mul (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2)) (hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))).
Axiom thm_treal_le : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (hreal_le (hreal_add x1 y2) (hreal_add x2 y1)).
Axiom thm_treal_inv : forall y : hreal, forall x : hreal, (treal_inv (@pair hreal hreal x y)) = (@COND (prod hreal hreal) (x = y) (@pair hreal hreal (hreal_of_num N0) (hreal_of_num N0)) (@COND (prod hreal hreal) (hreal_le y x) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => x = (hreal_add y d)))) (hreal_of_num N0)) (@pair hreal hreal (hreal_of_num N0) (hreal_inv (@ε hreal (fun d : hreal => y = (hreal_add x d))))))).
Axiom thm_treal_eq : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Axiom thm_TREAL_EQ_REFL : forall x : prod hreal hreal, treal_eq x x.
Axiom thm_TREAL_EQ_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) = (treal_eq y x).
Axiom thm_TREAL_EQ_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_eq x y) /\ (treal_eq y z)) -> treal_eq x z.
Axiom thm_TREAL_EQ_AP : forall x : prod hreal hreal, forall y : prod hreal hreal, (x = y) -> treal_eq x y.
Axiom thm_TREAL_OF_NUM_EQ : forall m : N, forall n : N, (treal_eq (treal_of_num m) (treal_of_num n)) = (m = n).
Axiom thm_TREAL_OF_NUM_LE : forall m : N, forall n : N, (treal_le (treal_of_num m) (treal_of_num n)) = (N.le m n).
Axiom thm_TREAL_OF_NUM_ADD : forall m : N, forall n : N, treal_eq (treal_add (treal_of_num m) (treal_of_num n)) (treal_of_num (N.add m n)).
Axiom thm_TREAL_OF_NUM_MUL : forall m : N, forall n : N, treal_eq (treal_mul (treal_of_num m) (treal_of_num n)) (treal_of_num (N.mul m n)).
Axiom thm_TREAL_ADD_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_add x y) = (treal_add y x).
Axiom thm_TREAL_MUL_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_mul x y) = (treal_mul y x).
Axiom thm_TREAL_ADD_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_add x y) (treal_add y x).
Axiom thm_TREAL_ADD_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z).
Axiom thm_TREAL_ADD_LID : forall x : prod hreal hreal, treal_eq (treal_add (treal_of_num N0) x) x.
Axiom thm_TREAL_ADD_LINV : forall x : prod hreal hreal, treal_eq (treal_add (treal_neg x) x) (treal_of_num N0).
Axiom thm_TREAL_MUL_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_mul x y) (treal_mul y x).
Axiom thm_TREAL_MUL_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z).
Axiom thm_TREAL_MUL_LID : forall x : prod hreal hreal, treal_eq (treal_mul (treal_of_num ((BIT1 N0))) x) x.
Axiom thm_TREAL_ADD_LDISTRIB : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_add y z)) (treal_add (treal_mul x y) (treal_mul x z)).
Axiom thm_TREAL_LE_REFL : forall x : prod hreal hreal, treal_le x x.
Axiom thm_TREAL_LE_ANTISYM : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le x y) /\ (treal_le y x)) = (treal_eq x y).
Axiom thm_TREAL_LE_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_le x y) /\ (treal_le y z)) -> treal_le x z.
Axiom thm_TREAL_LE_TOTAL : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_le x y) \/ (treal_le y x).
Axiom thm_TREAL_LE_LADD_IMP : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, (treal_le y z) -> treal_le (treal_add x y) (treal_add x z).
Axiom thm_TREAL_LE_MUL : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le (treal_of_num N0) x) /\ (treal_le (treal_of_num N0) y)) -> treal_le (treal_of_num N0) (treal_mul x y).
Axiom thm_TREAL_INV_0 : treal_eq (treal_inv (treal_of_num N0)) (treal_of_num N0).
Axiom thm_TREAL_MUL_LINV : forall x : prod hreal hreal, (~ (treal_eq x (treal_of_num N0))) -> treal_eq (treal_mul (treal_inv x) x) (treal_of_num ((BIT1 N0))).
Axiom thm_TREAL_OF_NUM_WELLDEF : forall m : N, forall n : N, (m = n) -> treal_eq (treal_of_num m) (treal_of_num n).
Axiom thm_TREAL_NEG_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_neg x1) (treal_neg x2).
Axiom thm_TREAL_ADD_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_add x1 y) (treal_add x2 y).
Axiom thm_TREAL_ADD_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_add x1 y1) (treal_add x2 y2).
Axiom thm_TREAL_MUL_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_mul x1 y) (treal_mul x2 y).
Axiom thm_TREAL_MUL_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_mul x1 y1) (treal_mul x2 y2).
Axiom thm_TREAL_EQ_IMP_LE : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_le x y.
Axiom thm_TREAL_LE_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> (treal_le x1 y1) = (treal_le x2 y2).
Axiom thm_TREAL_INV_WELLDEF : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_eq (treal_inv x) (treal_inv y).
Axiom thm_REAL_ADD_SYM : forall x : R, forall y : R, (Rplus x y) = (Rplus y x).
Axiom thm_REAL_ADD_ASSOC : forall x : R, forall y : R, forall z : R, (Rplus x (Rplus y z)) = (Rplus (Rplus x y) z).
Axiom thm_REAL_ADD_LID : forall x : R, (Rplus (R_of_N N0) x) = x.
Axiom thm_REAL_ADD_LINV : forall x : R, (Rplus (Ropp x) x) = (R_of_N N0).
Axiom thm_REAL_MUL_SYM : forall x : R, forall y : R, (Rmult x y) = (Rmult y x).
Axiom thm_REAL_MUL_ASSOC : forall x : R, forall y : R, forall z : R, (Rmult x (Rmult y z)) = (Rmult (Rmult x y) z).
Axiom thm_REAL_MUL_LID : forall x : R, (Rmult (R_of_N ((BIT1 N0))) x) = x.
Axiom thm_REAL_ADD_LDISTRIB : forall x : R, forall y : R, forall z : R, (Rmult x (Rplus y z)) = (Rplus (Rmult x y) (Rmult x z)).
Axiom thm_REAL_LE_ANTISYM : forall x : R, forall y : R, ((Rle x y) /\ (Rle y x)) = (x = y).
Axiom thm_REAL_LE_LADD_IMP : forall x : R, forall y : R, forall z : R, (Rle y z) -> Rle (Rplus x y) (Rplus x z).
Axiom thm_REAL_INV_0 : (Rinv (R_of_N N0)) = (R_of_N N0).
Axiom thm_REAL_MUL_LINV : forall x : R, (~ (x = (R_of_N N0))) -> (Rmult (Rinv x) x) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_OF_NUM_EQ : forall m : N, forall n : N, ((R_of_N m) = (R_of_N n)) = (m = n).
Axiom thm_REAL_OF_NUM_LE : forall m : N, forall n : N, (Rle (R_of_N m) (R_of_N n)) = (N.le m n).
Axiom thm_REAL_OF_NUM_ADD : forall m : N, forall n : N, (Rplus (R_of_N m) (R_of_N n)) = (R_of_N (N.add m n)).
Axiom thm_REAL_OF_NUM_MUL : forall m : N, forall n : N, (Rmult (R_of_N m) (R_of_N n)) = (R_of_N (N.mul m n)).
Axiom thm_real_sub : forall x : R, forall y : R, (Rminus x y) = (Rplus x (Ropp y)).
Axiom thm_real_lt : forall y : R, forall x : R, (Rlt x y) = (~ (Rle y x)).
Axiom thm_real_ge : forall y : R, forall x : R, (Rge x y) = (Rle y x).
Axiom thm_real_gt : forall y : R, forall x : R, (Rgt x y) = (Rlt y x).
Axiom thm_real_abs : forall x : R, (Rabs x) = (@COND R (Rle (R_of_N N0) x) x (Ropp x)).
Axiom thm_real_pow : forall (x : R), ((Rpow x N0) = (R_of_N ((BIT1 N0)))) /\ (forall n : N, (Rpow x (N.succ n)) = (Rmult x (Rpow x n))).
Axiom thm_real_div : forall x : R, forall y : R, (Rdiv x y) = (Rmult x (Rinv y)).
Axiom thm_real_max : forall n : R, forall m : R, (Rmax m n) = (@COND R (Rle m n) n m).
Axiom thm_real_min : forall m : R, forall n : R, (Rmin m n) = (@COND R (Rle m n) m n).
Axiom thm_REAL_HREAL_LEMMA1 : exists r : hreal -> R, (forall x : R, (Rle (R_of_N N0) x) = (exists y : hreal, x = (r y))) /\ (forall y : hreal, forall z : hreal, (hreal_le y z) = (Rle (r y) (r z))).
Axiom thm_REAL_HREAL_LEMMA2 : exists h : R -> hreal, exists r : hreal -> R, (forall x : hreal, (h (r x)) = x) /\ ((forall x : R, (Rle (R_of_N N0) x) -> (r (h x)) = x) /\ ((forall x : hreal, Rle (R_of_N N0) (r x)) /\ (forall x : hreal, forall y : hreal, (hreal_le x y) = (Rle (r x) (r y))))).
Axiom thm_REAL_COMPLETE_SOMEPOS : forall P : R -> Prop, ((exists x : R, (P x) /\ (Rle (R_of_N N0) x)) /\ (exists M : R, forall x : R, (P x) -> Rle x M)) -> exists M : R, (forall x : R, (P x) -> Rle x M) /\ (forall M' : R, (forall x : R, (P x) -> Rle x M') -> Rle M M').
Axiom thm_REAL_COMPLETE : forall P : R -> Prop, ((exists x : R, P x) /\ (exists M : R, forall x : R, (P x) -> Rle x M)) -> exists M : R, (forall x : R, (P x) -> Rle x M) /\ (forall M' : R, (forall x : R, (P x) -> Rle x M') -> Rle M M').
Axiom thm_REAL_ADD_AC : forall (n : R) (m : R) (p : R), ((Rplus m n) = (Rplus n m)) /\ (((Rplus (Rplus m n) p) = (Rplus m (Rplus n p))) /\ ((Rplus m (Rplus n p)) = (Rplus n (Rplus m p)))).
Axiom thm_REAL_ADD_RINV : forall x : R, (Rplus x (Ropp x)) = (R_of_N N0).
Axiom thm_REAL_EQ_ADD_LCANCEL : forall x : R, forall y : R, forall z : R, ((Rplus x y) = (Rplus x z)) = (y = z).
Axiom thm_REAL_EQ_ADD_RCANCEL : forall x : R, forall y : R, forall z : R, ((Rplus x z) = (Rplus y z)) = (x = y).
Axiom thm_REAL_MUL_RNEG : forall x : R, forall y : R, (Rmult x (Ropp y)) = (Ropp (Rmult x y)).
Axiom thm_REAL_MUL_LNEG : forall x : R, forall y : R, (Rmult (Ropp x) y) = (Ropp (Rmult x y)).
Axiom thm_REAL_ADD_RID : forall x : R, (Rplus x (R_of_N N0)) = x.
Axiom thm_REAL_LE_LNEG : forall x : R, forall y : R, (Rle (Ropp x) y) = (Rle (R_of_N N0) (Rplus x y)).
Axiom thm_REAL_LE_RNEG : forall x : R, forall y : R, (Rle x (Ropp y)) = (Rle (Rplus x y) (R_of_N N0)).
Axiom thm_REAL_OF_NUM_POW : forall x : N, forall n : N, (Rpow (R_of_N x) n) = (R_of_N (N.pow x n)).
Axiom thm_REAL_POW_NEG : forall x : R, forall n : N, (Rpow (Ropp x) n) = (@COND R (N.Even n) (Rpow x n) (Ropp (Rpow x n))).
Axiom thm_REAL_ABS_NUM : forall n : N, (Rabs (R_of_N n)) = (R_of_N n).
Axiom thm_REAL_ABS_NEG : forall x : R, (Rabs (Ropp x)) = (Rabs x).
Axiom thm_REAL_LTE_TOTAL : forall x : R, forall y : R, (Rlt x y) \/ (Rle y x).
Axiom thm_REAL_LET_TOTAL : forall x : R, forall y : R, (Rle x y) \/ (Rlt y x).
Axiom thm_REAL_LET_TRANS : forall x : R, forall y : R, forall z : R, ((Rle x y) /\ (Rlt y z)) -> Rlt x z.
Axiom thm_REAL_LT_TRANS : forall x : R, forall y : R, forall z : R, ((Rlt x y) /\ (Rlt y z)) -> Rlt x z.
Axiom thm_REAL_LE_ADD : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rle (R_of_N N0) y)) -> Rle (R_of_N N0) (Rplus x y).
Axiom thm_REAL_LTE_ANTISYM : forall x : R, forall y : R, ~ ((Rlt x y) /\ (Rle y x)).
Axiom thm_REAL_LT_REFL : forall x : R, ~ (Rlt x x).
Axiom thm_REAL_LET_ADD : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rlt (R_of_N N0) y)) -> Rlt (R_of_N N0) (Rplus x y).
Axiom thm_REAL_ENTIRE : forall x : R, forall y : R, ((Rmult x y) = (R_of_N N0)) = ((x = (R_of_N N0)) \/ (y = (R_of_N N0))).
Axiom thm_REAL_POW_2 : forall x : R, (Rpow x ((BIT0 (BIT1 N0)))) = (Rmult x x).
Axiom thm_REAL_POLY_CLAUSES : (forall x : R, forall y : R, forall z : R, (Rplus x (Rplus y z)) = (Rplus (Rplus x y) z)) /\ ((forall x : R, forall y : R, (Rplus x y) = (Rplus y x)) /\ ((forall x : R, (Rplus (R_of_N N0) x) = x) /\ ((forall x : R, forall y : R, forall z : R, (Rmult x (Rmult y z)) = (Rmult (Rmult x y) z)) /\ ((forall x : R, forall y : R, (Rmult x y) = (Rmult y x)) /\ ((forall x : R, (Rmult (R_of_N ((BIT1 N0))) x) = x) /\ ((forall x : R, (Rmult (R_of_N N0) x) = (R_of_N N0)) /\ ((forall x : R, forall y : R, forall z : R, (Rmult x (Rplus y z)) = (Rplus (Rmult x y) (Rmult x z))) /\ ((forall x : R, (Rpow x N0) = (R_of_N ((BIT1 N0)))) /\ (forall x : R, forall n : N, (Rpow x (N.succ n)) = (Rmult x (Rpow x n))))))))))).
Axiom thm_REAL_POLY_NEG_CLAUSES : (forall x : R, (Ropp x) = (Rmult (Ropp (R_of_N ((BIT1 N0)))) x)) /\ (forall x : R, forall y : R, (Rminus x y) = (Rplus x (Rmult (Ropp (R_of_N ((BIT1 N0)))) y))).
Axiom thm_REAL_POS_LT : forall n : N, Rlt (R_of_N N0) (R_of_N (N.succ n)).
Axiom thm_REAL_OF_NUM_LT : forall m : N, forall n : N, (Rlt (R_of_N m) (R_of_N n)) = (N.lt m n).
Axiom thm_REAL_OF_NUM_GE : forall m : N, forall n : N, (Rge (R_of_N m) (R_of_N n)) = (N.ge m n).
Axiom thm_REAL_OF_NUM_GT : forall m : N, forall n : N, (Rgt (R_of_N m) (R_of_N n)) = (N.gt m n).
Axiom thm_REAL_OF_NUM_MAX : forall m : N, forall n : N, (Rmax (R_of_N m) (R_of_N n)) = (R_of_N (N.max m n)).
Axiom thm_REAL_OF_NUM_MIN : forall m : N, forall n : N, (Rmin (R_of_N m) (R_of_N n)) = (R_of_N (N.min m n)).
Axiom thm_REAL_OF_NUM_SUC : forall n : N, (Rplus (R_of_N n) (R_of_N ((BIT1 N0)))) = (R_of_N (N.succ n)).
Axiom thm_REAL_OF_NUM_SUB : forall m : N, forall n : N, (N.le m n) -> (Rminus (R_of_N n) (R_of_N m)) = (R_of_N (N.sub n m)).
Axiom thm_REAL_OF_NUM_SUB_CASES : forall m : N, forall n : N, (Rminus (R_of_N m) (R_of_N n)) = (@COND R (N.le n m) (R_of_N (N.sub m n)) (Ropp (R_of_N (N.sub n m)))).
Axiom thm_REAL_OF_NUM_CLAUSES : (forall m : N, forall n : N, ((R_of_N m) = (R_of_N n)) = (m = n)) /\ ((forall m : N, forall n : N, (Rge (R_of_N m) (R_of_N n)) = (N.ge m n)) /\ ((forall m : N, forall n : N, (Rgt (R_of_N m) (R_of_N n)) = (N.gt m n)) /\ ((forall m : N, forall n : N, (Rle (R_of_N m) (R_of_N n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (Rlt (R_of_N m) (R_of_N n)) = (N.lt m n)) /\ ((forall m : N, forall n : N, (Rmax (R_of_N m) (R_of_N n)) = (R_of_N (N.max m n))) /\ ((forall m : N, forall n : N, (Rmin (R_of_N m) (R_of_N n)) = (R_of_N (N.min m n))) /\ ((forall m : N, forall n : N, (Rplus (R_of_N m) (R_of_N n)) = (R_of_N (N.add m n))) /\ ((forall m : N, forall n : N, (Rmult (R_of_N m) (R_of_N n)) = (R_of_N (N.mul m n))) /\ (forall x : N, forall n : N, (Rpow (R_of_N x) n) = (R_of_N (N.pow x n))))))))))).
Axiom thm_REAL_MUL_AC : forall (n : R) (m : R) (p : R), ((Rmult m n) = (Rmult n m)) /\ (((Rmult (Rmult m n) p) = (Rmult m (Rmult n p))) /\ ((Rmult m (Rmult n p)) = (Rmult n (Rmult m p)))).
Axiom thm_REAL_ADD_RDISTRIB : forall x : R, forall y : R, forall z : R, (Rmult (Rplus x y) z) = (Rplus (Rmult x z) (Rmult y z)).
Axiom thm_REAL_LT_LADD_IMP : forall x : R, forall y : R, forall z : R, (Rlt y z) -> Rlt (Rplus x y) (Rplus x z).
Axiom thm_REAL_LT_MUL : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rlt (R_of_N N0) y)) -> Rlt (R_of_N N0) (Rmult x y).
Axiom thm_REAL_EQ_ADD_LCANCEL_0 : forall x : R, forall y : R, ((Rplus x y) = x) = (y = (R_of_N N0)).
Axiom thm_REAL_EQ_ADD_RCANCEL_0 : forall x : R, forall y : R, ((Rplus x y) = y) = (x = (R_of_N N0)).
Axiom thm_REAL_NOT_EQ : forall x : R, forall y : R, (~ (x = y)) = ((Rlt x y) \/ (Rlt y x)).
Axiom thm_REAL_LET_ANTISYM : forall x : R, forall y : R, ~ ((Rle x y) /\ (Rlt y x)).
Axiom thm_REAL_LT_TOTAL : forall x : R, forall y : R, (x = y) \/ ((Rlt x y) \/ (Rlt y x)).
Axiom thm_REAL_LE_01 : Rle (R_of_N N0) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_LE_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((Rle w x) /\ (Rle y z)) -> Rle (Rplus w y) (Rplus x z).
Axiom thm_REAL_LT_LNEG : forall x : R, forall y : R, (Rlt (Ropp x) y) = (Rlt (R_of_N N0) (Rplus x y)).
Axiom thm_REAL_LT_RNEG : forall x : R, forall y : R, (Rlt x (Ropp y)) = (Rlt (Rplus x y) (R_of_N N0)).
Axiom thm_REAL_NEG_EQ_0 : forall x : R, ((Ropp x) = (R_of_N N0)) = (x = (R_of_N N0)).
Axiom thm_REAL_ADD_SUB : forall x : R, forall y : R, (Rminus (Rplus x y) x) = y.
Axiom thm_REAL_LE_ADDR : forall x : R, forall y : R, (Rle x (Rplus x y)) = (Rle (R_of_N N0) y).
Axiom thm_REAL_LE_ADDL : forall x : R, forall y : R, (Rle y (Rplus x y)) = (Rle (R_of_N N0) x).
Axiom thm_REAL_LT_ADDR : forall x : R, forall y : R, (Rlt x (Rplus x y)) = (Rlt (R_of_N N0) y).
Axiom thm_REAL_LT_ADDL : forall x : R, forall y : R, (Rlt y (Rplus x y)) = (Rlt (R_of_N N0) x).
Axiom thm_REAL_ADD2_SUB2 : forall a : R, forall b : R, forall c : R, forall d : R, (Rminus (Rplus a b) (Rplus c d)) = (Rplus (Rminus a c) (Rminus b d)).
Axiom thm_REAL_LET_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((Rle w x) /\ (Rlt y z)) -> Rlt (Rplus w y) (Rplus x z).
Axiom thm_REAL_EQ_SUB_LADD : forall x : R, forall y : R, forall z : R, (x = (Rminus y z)) = ((Rplus x z) = y).
Axiom thm_REAL_EQ_SUB_RADD : forall x : R, forall y : R, forall z : R, ((Rminus x y) = z) = (x = (Rplus z y)).
Axiom thm_REAL_ADD_SUB2 : forall x : R, forall y : R, (Rminus x (Rplus x y)) = (Ropp y).
Axiom thm_REAL_EQ_IMP_LE : forall x : R, forall y : R, (x = y) -> Rle x y.
Axiom thm_REAL_DIFFSQ : forall x : R, forall y : R, (Rmult (Rplus x y) (Rminus x y)) = (Rminus (Rmult x x) (Rmult y y)).
Axiom thm_REAL_EQ_NEG2 : forall x : R, forall y : R, ((Ropp x) = (Ropp y)) = (x = y).
Axiom thm_REAL_ABS_ZERO : forall x : R, ((Rabs x) = (R_of_N N0)) = (x = (R_of_N N0)).
Axiom thm_REAL_ABS_0 : (Rabs (R_of_N N0)) = (R_of_N N0).
Axiom thm_REAL_ABS_1 : (Rabs (R_of_N ((BIT1 N0)))) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_ABS_TRIANGLE : forall x : R, forall y : R, Rle (Rabs (Rplus x y)) (Rplus (Rabs x) (Rabs y)).
Axiom thm_REAL_ABS_TRIANGLE_LE : forall x : R, forall y : R, forall z : R, (Rle (Rplus (Rabs x) (Rabs (Rminus y x))) z) -> Rle (Rabs y) z.
Axiom thm_REAL_ABS_TRIANGLE_LT : forall x : R, forall y : R, forall z : R, (Rlt (Rplus (Rabs x) (Rabs (Rminus y x))) z) -> Rlt (Rabs y) z.
Axiom thm_REAL_ABS_POS : forall x : R, Rle (R_of_N N0) (Rabs x).
Axiom thm_REAL_ABS_SUB : forall x : R, forall y : R, (Rabs (Rminus x y)) = (Rabs (Rminus y x)).
Axiom thm_REAL_ABS_NZ : forall x : R, (~ (x = (R_of_N N0))) = (Rlt (R_of_N N0) (Rabs x)).
Axiom thm_REAL_ABS_ABS : forall x : R, (Rabs (Rabs x)) = (Rabs x).
Axiom thm_REAL_ABS_LE : forall x : R, Rle x (Rabs x).
Axiom thm_REAL_ABS_REFL : forall x : R, ((Rabs x) = x) = (Rle (R_of_N N0) x).
Axiom thm_REAL_ABS_BETWEEN : forall x : R, forall y : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((Rlt (Rminus x d) y) /\ (Rlt y (Rplus x d)))) = (Rlt (Rabs (Rminus y x)) d).
Axiom thm_REAL_ABS_BOUND : forall x : R, forall y : R, forall d : R, (Rlt (Rabs (Rminus x y)) d) -> Rlt y (Rplus x d).
Axiom thm_REAL_ABS_STILLNZ : forall x : R, forall y : R, (Rlt (Rabs (Rminus x y)) (Rabs y)) -> ~ (x = (R_of_N N0)).
Axiom thm_REAL_ABS_CASES : forall x : R, (x = (R_of_N N0)) \/ (Rlt (R_of_N N0) (Rabs x)).
Axiom thm_REAL_ABS_BETWEEN1 : forall x : R, forall y : R, forall z : R, ((Rlt x z) /\ (Rlt (Rabs (Rminus y x)) (Rminus z x))) -> Rlt y z.
Axiom thm_REAL_ABS_SIGN : forall x : R, forall y : R, (Rlt (Rabs (Rminus x y)) y) -> Rlt (R_of_N N0) x.
Axiom thm_REAL_ABS_SIGN2 : forall x : R, forall y : R, (Rlt (Rabs (Rminus x y)) (Ropp y)) -> Rlt x (R_of_N N0).
Axiom thm_REAL_ABS_CIRCLE : forall x : R, forall y : R, forall h : R, (Rlt (Rabs h) (Rminus (Rabs y) (Rabs x))) -> Rlt (Rabs (Rplus x h)) (Rabs y).
Axiom thm_REAL_ABS_SUB_ABS : forall x : R, forall y : R, Rle (Rabs (Rminus (Rabs x) (Rabs y))) (Rabs (Rminus x y)).
Axiom thm_REAL_ABS_BETWEEN2 : forall x0 : R, forall x : R, forall y0 : R, forall y : R, ((Rlt x0 y0) /\ ((Rlt (Rmult (R_of_N ((BIT0 (BIT1 N0)))) (Rabs (Rminus x x0))) (Rminus y0 x0)) /\ (Rlt (Rmult (R_of_N ((BIT0 (BIT1 N0)))) (Rabs (Rminus y y0))) (Rminus y0 x0)))) -> Rlt x y.
Axiom thm_REAL_ABS_BOUNDS : forall x : R, forall k : R, (Rle (Rabs x) k) = ((Rle (Ropp k) x) /\ (Rle x k)).
Axiom thm_REAL_BOUNDS_LE : forall x : R, forall k : R, ((Rle (Ropp k) x) /\ (Rle x k)) = (Rle (Rabs x) k).
Axiom thm_REAL_BOUNDS_LT : forall x : R, forall k : R, ((Rlt (Ropp k) x) /\ (Rlt x k)) = (Rlt (Rabs x) k).
Axiom thm_REAL_MIN_MAX : forall x : R, forall y : R, (Rmin x y) = (Ropp (Rmax (Ropp x) (Ropp y))).
Axiom thm_REAL_MAX_MIN : forall x : R, forall y : R, (Rmax x y) = (Ropp (Rmin (Ropp x) (Ropp y))).
Axiom thm_REAL_MAX_MAX : forall x : R, forall y : R, (Rle x (Rmax x y)) /\ (Rle y (Rmax x y)).
Axiom thm_REAL_MIN_MIN : forall x : R, forall y : R, (Rle (Rmin x y) x) /\ (Rle (Rmin x y) y).
Axiom thm_REAL_MAX_SYM : forall x : R, forall y : R, (Rmax x y) = (Rmax y x).
Axiom thm_REAL_MIN_SYM : forall x : R, forall y : R, (Rmin x y) = (Rmin y x).
Axiom thm_REAL_LE_MAX : forall x : R, forall y : R, forall z : R, (Rle z (Rmax x y)) = ((Rle z x) \/ (Rle z y)).
Axiom thm_REAL_LE_MIN : forall x : R, forall y : R, forall z : R, (Rle z (Rmin x y)) = ((Rle z x) /\ (Rle z y)).
Axiom thm_REAL_LT_MAX : forall x : R, forall y : R, forall z : R, (Rlt z (Rmax x y)) = ((Rlt z x) \/ (Rlt z y)).
Axiom thm_REAL_LT_MIN : forall x : R, forall y : R, forall z : R, (Rlt z (Rmin x y)) = ((Rlt z x) /\ (Rlt z y)).
Axiom thm_REAL_MAX_LE : forall x : R, forall y : R, forall z : R, (Rle (Rmax x y) z) = ((Rle x z) /\ (Rle y z)).
Axiom thm_REAL_MIN_LE : forall x : R, forall y : R, forall z : R, (Rle (Rmin x y) z) = ((Rle x z) \/ (Rle y z)).
Axiom thm_REAL_MAX_LT : forall x : R, forall y : R, forall z : R, (Rlt (Rmax x y) z) = ((Rlt x z) /\ (Rlt y z)).
Axiom thm_REAL_MIN_LT : forall x : R, forall y : R, forall z : R, (Rlt (Rmin x y) z) = ((Rlt x z) \/ (Rlt y z)).
Axiom thm_REAL_MAX_ASSOC : forall x : R, forall y : R, forall z : R, (Rmax x (Rmax y z)) = (Rmax (Rmax x y) z).
Axiom thm_REAL_MIN_ASSOC : forall x : R, forall y : R, forall z : R, (Rmin x (Rmin y z)) = (Rmin (Rmin x y) z).
Axiom thm_REAL_MAX_ACI : forall (z : R) (x : R) (y : R), ((Rmax x y) = (Rmax y x)) /\ (((Rmax (Rmax x y) z) = (Rmax x (Rmax y z))) /\ (((Rmax x (Rmax y z)) = (Rmax y (Rmax x z))) /\ (((Rmax x x) = x) /\ ((Rmax x (Rmax x y)) = (Rmax x y))))).
Axiom thm_REAL_MIN_ACI : forall (z : R) (x : R) (y : R), ((Rmin x y) = (Rmin y x)) /\ (((Rmin (Rmin x y) z) = (Rmin x (Rmin y z))) /\ (((Rmin x (Rmin y z)) = (Rmin y (Rmin x z))) /\ (((Rmin x x) = x) /\ ((Rmin x (Rmin x y)) = (Rmin x y))))).
Axiom thm_REAL_ABS_MUL : forall x : R, forall y : R, (Rabs (Rmult x y)) = (Rmult (Rabs x) (Rabs y)).
Axiom thm_REAL_POW_LE : forall x : R, forall n : N, (Rle (R_of_N N0) x) -> Rle (R_of_N N0) (Rpow x n).
Axiom thm_REAL_POW_LT : forall x : R, forall n : N, (Rlt (R_of_N N0) x) -> Rlt (R_of_N N0) (Rpow x n).
Axiom thm_REAL_ABS_POW : forall x : R, forall n : N, (Rabs (Rpow x n)) = (Rpow (Rabs x) n).
Axiom thm_REAL_LE_LMUL : forall x : R, forall y : R, forall z : R, ((Rle (R_of_N N0) x) /\ (Rle y z)) -> Rle (Rmult x y) (Rmult x z).
Axiom thm_REAL_LE_RMUL : forall x : R, forall y : R, forall z : R, ((Rle x y) /\ (Rle (R_of_N N0) z)) -> Rle (Rmult x z) (Rmult y z).
Axiom thm_REAL_LT_LMUL : forall x : R, forall y : R, forall z : R, ((Rlt (R_of_N N0) x) /\ (Rlt y z)) -> Rlt (Rmult x y) (Rmult x z).
Axiom thm_REAL_LT_RMUL : forall x : R, forall y : R, forall z : R, ((Rlt x y) /\ (Rlt (R_of_N N0) z)) -> Rlt (Rmult x z) (Rmult y z).
Axiom thm_REAL_EQ_MUL_LCANCEL : forall x : R, forall y : R, forall z : R, ((Rmult x y) = (Rmult x z)) = ((x = (R_of_N N0)) \/ (y = z)).
Axiom thm_REAL_EQ_MUL_RCANCEL : forall x : R, forall y : R, forall z : R, ((Rmult x z) = (Rmult y z)) = ((x = y) \/ (z = (R_of_N N0))).
Axiom thm_REAL_MUL_LINV_UNIQ : forall x : R, forall y : R, ((Rmult x y) = (R_of_N ((BIT1 N0)))) -> (Rinv y) = x.
Axiom thm_REAL_MUL_RINV_UNIQ : forall x : R, forall y : R, ((Rmult x y) = (R_of_N ((BIT1 N0)))) -> (Rinv x) = y.
Axiom thm_REAL_INV_INV : forall x : R, (Rinv (Rinv x)) = x.
Axiom thm_REAL_EQ_INV2 : forall x : R, forall y : R, ((Rinv x) = (Rinv y)) = (x = y).
Axiom thm_REAL_INV_EQ_0 : forall x : R, ((Rinv x) = (R_of_N N0)) = (x = (R_of_N N0)).
Axiom thm_REAL_LT_INV : forall x : R, (Rlt (R_of_N N0) x) -> Rlt (R_of_N N0) (Rinv x).
Axiom thm_REAL_LT_INV_EQ : forall x : R, (Rlt (R_of_N N0) (Rinv x)) = (Rlt (R_of_N N0) x).
Axiom thm_REAL_INV_NEG : forall x : R, (Rinv (Ropp x)) = (Ropp (Rinv x)).
Axiom thm_REAL_LE_INV_EQ : forall x : R, (Rle (R_of_N N0) (Rinv x)) = (Rle (R_of_N N0) x).
Axiom thm_REAL_LE_INV : forall x : R, (Rle (R_of_N N0) x) -> Rle (R_of_N N0) (Rinv x).
Axiom thm_REAL_INV_1 : (Rinv (R_of_N ((BIT1 N0)))) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_INV_EQ_1 : forall x : R, ((Rinv x) = (R_of_N ((BIT1 N0)))) = (x = (R_of_N ((BIT1 N0)))).
Axiom thm_REAL_DIV_1 : forall x : R, (Rdiv x (R_of_N ((BIT1 N0)))) = x.
Axiom thm_REAL_DIV_REFL : forall x : R, (~ (x = (R_of_N N0))) -> (Rdiv x x) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_DIV_RMUL : forall x : R, forall y : R, (~ (y = (R_of_N N0))) -> (Rmult (Rdiv x y) y) = x.
Axiom thm_REAL_DIV_LMUL : forall x : R, forall y : R, (~ (y = (R_of_N N0))) -> (Rmult y (Rdiv x y)) = x.
Axiom thm_REAL_DIV_EQ_1 : forall x : R, forall y : R, ((Rdiv x y) = (R_of_N ((BIT1 N0)))) = ((x = y) /\ ((~ (x = (R_of_N N0))) /\ (~ (y = (R_of_N N0))))).
Axiom thm_REAL_ABS_INV : forall x : R, (Rabs (Rinv x)) = (Rinv (Rabs x)).
Axiom thm_REAL_ABS_DIV : forall x : R, forall y : R, (Rabs (Rdiv x y)) = (Rdiv (Rabs x) (Rabs y)).
Axiom thm_REAL_INV_MUL : forall x : R, forall y : R, (Rinv (Rmult x y)) = (Rmult (Rinv x) (Rinv y)).
Axiom thm_REAL_INV_DIV : forall x : R, forall y : R, (Rinv (Rdiv x y)) = (Rdiv y x).
Axiom thm_REAL_POW_MUL : forall x : R, forall y : R, forall n : N, (Rpow (Rmult x y) n) = (Rmult (Rpow x n) (Rpow y n)).
Axiom thm_REAL_POW_INV : forall x : R, forall n : N, (Rpow (Rinv x) n) = (Rinv (Rpow x n)).
Axiom thm_REAL_INV_POW : forall x : R, forall n : N, (Rinv (Rpow x n)) = (Rpow (Rinv x) n).
Axiom thm_REAL_POW_DIV : forall x : R, forall y : R, forall n : N, (Rpow (Rdiv x y) n) = (Rdiv (Rpow x n) (Rpow y n)).
Axiom thm_REAL_DIV_EQ_0 : forall x : R, forall y : R, ((Rdiv x y) = (R_of_N N0)) = ((x = (R_of_N N0)) \/ (y = (R_of_N N0))).
Axiom thm_REAL_POW_ADD : forall x : R, forall m : N, forall n : N, (Rpow x (N.add m n)) = (Rmult (Rpow x m) (Rpow x n)).
Axiom thm_REAL_POW_NZ : forall x : R, forall n : N, (~ (x = (R_of_N N0))) -> ~ ((Rpow x n) = (R_of_N N0)).
Axiom thm_REAL_POW_SUB : forall x : R, forall m : N, forall n : N, ((~ (x = (R_of_N N0))) /\ (N.le m n)) -> (Rpow x (N.sub n m)) = (Rdiv (Rpow x n) (Rpow x m)).
Axiom thm_REAL_LT_LCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((Rlt (R_of_N N0) x) /\ (Rlt (Rmult x y) (Rmult x z))) -> Rlt y z.
Axiom thm_REAL_LT_RCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((Rlt (R_of_N N0) z) /\ (Rlt (Rmult x z) (Rmult y z))) -> Rlt x y.
Axiom thm_REAL_LE_LCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((Rlt (R_of_N N0) x) /\ (Rle (Rmult x y) (Rmult x z))) -> Rle y z.
Axiom thm_REAL_LE_RCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((Rlt (R_of_N N0) z) /\ (Rle (Rmult x z) (Rmult y z))) -> Rle x y.
Axiom thm_REAL_LE_LMUL_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rle (Rmult z x) (Rmult z y)) = (Rle x y).
Axiom thm_REAL_LE_MUL_EQ : (forall x : R, forall y : R, (Rlt (R_of_N N0) x) -> (Rle (R_of_N N0) (Rmult x y)) = (Rle (R_of_N N0) y)) /\ (forall x : R, forall y : R, (Rlt (R_of_N N0) y) -> (Rle (R_of_N N0) (Rmult x y)) = (Rle (R_of_N N0) x)).
Axiom thm_REAL_LT_MUL_EQ : (forall x : R, forall y : R, (Rlt (R_of_N N0) x) -> (Rlt (R_of_N N0) (Rmult x y)) = (Rlt (R_of_N N0) y)) /\ (forall x : R, forall y : R, (Rlt (R_of_N N0) y) -> (Rlt (R_of_N N0) (Rmult x y)) = (Rlt (R_of_N N0) x)).
Axiom thm_REAL_MUL_POS_LT : forall x : R, forall y : R, (Rlt (R_of_N N0) (Rmult x y)) = (((Rlt (R_of_N N0) x) /\ (Rlt (R_of_N N0) y)) \/ ((Rlt x (R_of_N N0)) /\ (Rlt y (R_of_N N0)))).
Axiom thm_REAL_MUL_POS_LE : forall x : R, forall y : R, (Rle (R_of_N N0) (Rmult x y)) = ((x = (R_of_N N0)) \/ ((y = (R_of_N N0)) \/ (((Rlt (R_of_N N0) x) /\ (Rlt (R_of_N N0) y)) \/ ((Rlt x (R_of_N N0)) /\ (Rlt y (R_of_N N0)))))).
Axiom thm_REAL_LE_RDIV_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rle x (Rdiv y z)) = (Rle (Rmult x z) y).
Axiom thm_REAL_LE_LDIV_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rle (Rdiv x z) y) = (Rle x (Rmult y z)).
Axiom thm_REAL_LT_RDIV_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rlt x (Rdiv y z)) = (Rlt (Rmult x z) y).
Axiom thm_REAL_LT_LDIV_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rlt (Rdiv x z) y) = (Rlt x (Rmult y z)).
Axiom thm_REAL_EQ_RDIV_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (x = (Rdiv y z)) = ((Rmult x z) = y).
Axiom thm_REAL_EQ_LDIV_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> ((Rdiv x z) = y) = (x = (Rmult y z)).
Axiom thm_REAL_LT_DIV2_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rlt (Rdiv x z) (Rdiv y z)) = (Rlt x y).
Axiom thm_REAL_LE_DIV2_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rle (Rdiv x z) (Rdiv y z)) = (Rle x y).
Axiom thm_REAL_MUL_2 : forall x : R, (Rmult (R_of_N ((BIT0 (BIT1 N0)))) x) = (Rplus x x).
Axiom thm_REAL_POW_EQ_0 : forall x : R, forall n : N, ((Rpow x n) = (R_of_N N0)) = ((x = (R_of_N N0)) /\ (~ (n = N0))).
Axiom thm_REAL_LE_MUL2 : forall w : R, forall x : R, forall y : R, forall z : R, ((Rle (R_of_N N0) w) /\ ((Rle w x) /\ ((Rle (R_of_N N0) y) /\ (Rle y z)))) -> Rle (Rmult w y) (Rmult x z).
Axiom thm_REAL_LT_MUL2 : forall w : R, forall x : R, forall y : R, forall z : R, ((Rle (R_of_N N0) w) /\ ((Rlt w x) /\ ((Rle (R_of_N N0) y) /\ (Rlt y z)))) -> Rlt (Rmult w y) (Rmult x z).
Axiom thm_REAL_LT_SQUARE : forall x : R, (Rlt (R_of_N N0) (Rmult x x)) = (~ (x = (R_of_N N0))).
Axiom thm_REAL_POW_1 : forall x : R, (Rpow x ((BIT1 N0))) = x.
Axiom thm_REAL_POW_ONE : forall n : N, (Rpow (R_of_N ((BIT1 N0))) n) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_LT_INV2 : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rlt x y)) -> Rlt (Rinv y) (Rinv x).
Axiom thm_REAL_LE_INV2 : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rle x y)) -> Rle (Rinv y) (Rinv x).
Axiom thm_REAL_LT_LINV : forall x : R, forall y : R, ((Rlt (R_of_N N0) y) /\ (Rlt (Rinv y) x)) -> Rlt (Rinv x) y.
Axiom thm_REAL_LT_RINV : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rlt x (Rinv y))) -> Rlt y (Rinv x).
Axiom thm_REAL_LE_LINV : forall x : R, forall y : R, ((Rlt (R_of_N N0) y) /\ (Rle (Rinv y) x)) -> Rle (Rinv x) y.
Axiom thm_REAL_LE_RINV : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rle x (Rinv y))) -> Rle y (Rinv x).
Axiom thm_REAL_INV_LE_1 : forall x : R, (Rle (R_of_N ((BIT1 N0))) x) -> Rle (Rinv x) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_INV_1_LE : forall x : R, ((Rlt (R_of_N N0) x) /\ (Rle x (R_of_N ((BIT1 N0))))) -> Rle (R_of_N ((BIT1 N0))) (Rinv x).
Axiom thm_REAL_INV_LT_1 : forall x : R, (Rlt (R_of_N ((BIT1 N0))) x) -> Rlt (Rinv x) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_INV_1_LT : forall x : R, ((Rlt (R_of_N N0) x) /\ (Rlt x (R_of_N ((BIT1 N0))))) -> Rlt (R_of_N ((BIT1 N0))) (Rinv x).
Axiom thm_REAL_SUB_INV : forall x : R, forall y : R, ((~ (x = (R_of_N N0))) /\ (~ (y = (R_of_N N0)))) -> (Rminus (Rinv x) (Rinv y)) = (Rdiv (Rminus y x) (Rmult x y)).
Axiom thm_REAL_DOWN : forall d : R, (Rlt (R_of_N N0) d) -> exists e : R, (Rlt (R_of_N N0) e) /\ (Rlt e d).
Axiom thm_REAL_DOWN2 : forall d1 : R, forall d2 : R, ((Rlt (R_of_N N0) d1) /\ (Rlt (R_of_N N0) d2)) -> exists e : R, (Rlt (R_of_N N0) e) /\ ((Rlt e d1) /\ (Rlt e d2)).
Axiom thm_REAL_POW_LE2 : forall n : N, forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rle x y)) -> Rle (Rpow x n) (Rpow y n).
Axiom thm_REAL_POW_LE_1 : forall n : N, forall x : R, (Rle (R_of_N ((BIT1 N0))) x) -> Rle (R_of_N ((BIT1 N0))) (Rpow x n).
Axiom thm_REAL_POW_1_LE : forall n : N, forall x : R, ((Rle (R_of_N N0) x) /\ (Rle x (R_of_N ((BIT1 N0))))) -> Rle (Rpow x n) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_POW_MONO : forall m : N, forall n : N, forall x : R, ((Rle (R_of_N ((BIT1 N0))) x) /\ (N.le m n)) -> Rle (Rpow x m) (Rpow x n).
Axiom thm_REAL_POW_LT2 : forall n : N, forall x : R, forall y : R, ((~ (n = N0)) /\ ((Rle (R_of_N N0) x) /\ (Rlt x y))) -> Rlt (Rpow x n) (Rpow y n).
Axiom thm_REAL_POW_LT_1 : forall n : N, forall x : R, ((~ (n = N0)) /\ (Rlt (R_of_N ((BIT1 N0))) x)) -> Rlt (R_of_N ((BIT1 N0))) (Rpow x n).
Axiom thm_REAL_POW_1_LT : forall n : N, forall x : R, ((~ (n = N0)) /\ ((Rle (R_of_N N0) x) /\ (Rlt x (R_of_N ((BIT1 N0)))))) -> Rlt (Rpow x n) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_POW_MONO_LT : forall m : N, forall n : N, forall x : R, ((Rlt (R_of_N ((BIT1 N0))) x) /\ (N.lt m n)) -> Rlt (Rpow x m) (Rpow x n).
Axiom thm_REAL_POW_POW : forall x : R, forall m : N, forall n : N, (Rpow (Rpow x m) n) = (Rpow x (N.mul m n)).
Axiom thm_REAL_EQ_RCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((~ (z = (R_of_N N0))) /\ ((Rmult x z) = (Rmult y z))) -> x = y.
Axiom thm_REAL_EQ_LCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((~ (z = (R_of_N N0))) /\ ((Rmult z x) = (Rmult z y))) -> x = y.
Axiom thm_REAL_LT_DIV : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rlt (R_of_N N0) y)) -> Rlt (R_of_N N0) (Rdiv x y).
Axiom thm_REAL_LE_DIV : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rle (R_of_N N0) y)) -> Rle (R_of_N N0) (Rdiv x y).
Axiom thm_REAL_DIV_POW2 : forall x : R, forall m : N, forall n : N, (~ (x = (R_of_N N0))) -> (Rdiv (Rpow x m) (Rpow x n)) = (@COND R (N.le n m) (Rpow x (N.sub m n)) (Rinv (Rpow x (N.sub n m)))).
Axiom thm_REAL_DIV_POW2_ALT : forall x : R, forall m : N, forall n : N, (~ (x = (R_of_N N0))) -> (Rdiv (Rpow x m) (Rpow x n)) = (@COND R (N.lt n m) (Rpow x (N.sub m n)) (Rinv (Rpow x (N.sub n m)))).
Axiom thm_REAL_LT_POW2 : forall n : N, Rlt (R_of_N N0) (Rpow (R_of_N ((BIT0 (BIT1 N0)))) n).
Axiom thm_REAL_LE_POW2 : forall n : N, Rle (R_of_N ((BIT1 N0))) (Rpow (R_of_N ((BIT0 (BIT1 N0)))) n).
Axiom thm_REAL_POW2_ABS : forall x : R, (Rpow (Rabs x) ((BIT0 (BIT1 N0)))) = (Rpow x ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_LE_SQUARE_ABS : forall x : R, forall y : R, (Rle (Rabs x) (Rabs y)) = (Rle (Rpow x ((BIT0 (BIT1 N0)))) (Rpow y ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_LT_SQUARE_ABS : forall x : R, forall y : R, (Rlt (Rabs x) (Rabs y)) = (Rlt (Rpow x ((BIT0 (BIT1 N0)))) (Rpow y ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_EQ_SQUARE_ABS : forall x : R, forall y : R, ((Rabs x) = (Rabs y)) = ((Rpow x ((BIT0 (BIT1 N0)))) = (Rpow y ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_LE_POW_2 : forall x : R, Rle (R_of_N N0) (Rpow x ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_LT_POW_2 : forall x : R, (Rlt (R_of_N N0) (Rpow x ((BIT0 (BIT1 N0))))) = (~ (x = (R_of_N N0))).
Axiom thm_REAL_SOS_EQ_0 : forall x : R, forall y : R, ((Rplus (Rpow x ((BIT0 (BIT1 N0)))) (Rpow y ((BIT0 (BIT1 N0))))) = (R_of_N N0)) = ((x = (R_of_N N0)) /\ (y = (R_of_N N0))).
Axiom thm_REAL_POW_ZERO : forall n : N, (Rpow (R_of_N N0) n) = (@COND R (n = N0) (R_of_N ((BIT1 N0))) (R_of_N N0)).
Axiom thm_REAL_POW_MONO_INV : forall m : N, forall n : N, forall x : R, ((Rle (R_of_N N0) x) /\ ((Rle x (R_of_N ((BIT1 N0)))) /\ (N.le n m))) -> Rle (Rpow x m) (Rpow x n).
Axiom thm_REAL_POW_LE2_REV : forall n : N, forall x : R, forall y : R, ((~ (n = N0)) /\ ((Rle (R_of_N N0) y) /\ (Rle (Rpow x n) (Rpow y n)))) -> Rle x y.
Axiom thm_REAL_POW_LT2_REV : forall n : N, forall x : R, forall y : R, ((Rle (R_of_N N0) y) /\ (Rlt (Rpow x n) (Rpow y n))) -> Rlt x y.
Axiom thm_REAL_POW_EQ : forall n : N, forall x : R, forall y : R, ((~ (n = N0)) /\ ((Rle (R_of_N N0) x) /\ ((Rle (R_of_N N0) y) /\ ((Rpow x n) = (Rpow y n))))) -> x = y.
Axiom thm_REAL_POW_EQ_ABS : forall n : N, forall x : R, forall y : R, ((~ (n = N0)) /\ ((Rpow x n) = (Rpow y n))) -> (Rabs x) = (Rabs y).
Axiom thm_REAL_POW_EQ_1_IMP : forall x : R, forall n : N, ((~ (n = N0)) /\ ((Rpow x n) = (R_of_N ((BIT1 N0))))) -> (Rabs x) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_POW_EQ_1 : forall x : R, forall n : N, ((Rpow x n) = (R_of_N ((BIT1 N0)))) = ((((Rabs x) = (R_of_N ((BIT1 N0)))) /\ ((Rlt x (R_of_N N0)) -> N.Even n)) \/ (n = N0)).
Axiom thm_REAL_POW_LT2_ODD : forall n : N, forall x : R, forall y : R, ((Rlt x y) /\ (N.Odd n)) -> Rlt (Rpow x n) (Rpow y n).
Axiom thm_REAL_POW_LE2_ODD : forall n : N, forall x : R, forall y : R, ((Rle x y) /\ (N.Odd n)) -> Rle (Rpow x n) (Rpow y n).
Axiom thm_REAL_POW_LT2_ODD_EQ : forall n : N, forall x : R, forall y : R, (N.Odd n) -> (Rlt (Rpow x n) (Rpow y n)) = (Rlt x y).
Axiom thm_REAL_POW_LE2_ODD_EQ : forall n : N, forall x : R, forall y : R, (N.Odd n) -> (Rle (Rpow x n) (Rpow y n)) = (Rle x y).
Axiom thm_REAL_POW_EQ_ODD_EQ : forall n : N, forall x : R, forall y : R, (N.Odd n) -> ((Rpow x n) = (Rpow y n)) = (x = y).
Axiom thm_REAL_POW_EQ_ODD : forall n : N, forall x : R, forall y : R, ((N.Odd n) /\ ((Rpow x n) = (Rpow y n))) -> x = y.
Axiom thm_REAL_POW_EQ_EQ : forall n : N, forall x : R, forall y : R, ((Rpow x n) = (Rpow y n)) = (@COND Prop (N.Even n) ((n = N0) \/ ((Rabs x) = (Rabs y))) (x = y)).
Axiom thm_REAL_EVENPOW_ABS : forall x : R, forall n : N, (N.Even n) -> (Rpow (Rabs x) n) = (Rpow x n).
Axiom thm_REAL_OF_NUM_MOD : forall m : N, forall n : N, (R_of_N (N.modulo m n)) = (Rminus (R_of_N m) (Rmult (R_of_N (N.div m n)) (R_of_N n))).
Axiom thm_REAL_OF_NUM_DIV : forall m : N, forall n : N, (R_of_N (N.div m n)) = (Rminus (Rdiv (R_of_N m) (R_of_N n)) (Rdiv (R_of_N (N.modulo m n)) (R_of_N n))).
Axiom thm_REAL_CONVEX_BOUND2_LT : forall (b : R), forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((Rlt x a) /\ ((Rlt y b) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))) -> Rlt (Rplus (Rmult u x) (Rmult v y)) (Rplus (Rmult u a) (Rmult v b)).
Axiom thm_REAL_CONVEX_BOUND2_LE : forall (b : R), forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((Rle x a) /\ ((Rle y b) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))) -> Rle (Rplus (Rmult u x) (Rmult v y)) (Rplus (Rmult u a) (Rmult v b)).
Axiom thm_REAL_CONVEX_BOUND_LT : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((Rlt x a) /\ ((Rlt y a) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))) -> Rlt (Rplus (Rmult u x) (Rmult v y)) a.
Axiom thm_REAL_CONVEX_BOUND_LE : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((Rle x a) /\ ((Rle y a) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))) -> Rle (Rplus (Rmult u x) (Rmult v y)) a.
Axiom thm_REAL_CONVEX_BOUND_GT : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((Rlt a x) /\ ((Rlt a y) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))) -> Rlt a (Rplus (Rmult u x) (Rmult v y)).
Axiom thm_REAL_CONVEX_BOUND_GE : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((Rle a x) /\ ((Rle a y) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))) -> Rle a (Rplus (Rmult u x) (Rmult v y)).
Axiom thm_REAL_CONVEX_BOUNDS_LE : forall x : R, forall y : R, forall a : R, forall b : R, forall u : R, forall v : R, ((Rle a x) /\ ((Rle x b) /\ ((Rle a y) /\ ((Rle y b) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))))) -> (Rle a (Rplus (Rmult u x) (Rmult v y))) /\ (Rle (Rplus (Rmult u x) (Rmult v y)) b).
Axiom thm_REAL_CONVEX_BOUNDS_LT : forall x : R, forall y : R, forall a : R, forall b : R, forall u : R, forall v : R, ((Rlt a x) /\ ((Rlt x b) /\ ((Rlt a y) /\ ((Rlt y b) /\ ((Rle (R_of_N N0) u) /\ ((Rle (R_of_N N0) v) /\ ((Rplus u v) = (R_of_N ((BIT1 N0)))))))))) -> (Rlt a (Rplus (Rmult u x) (Rmult v y))) /\ (Rlt (Rplus (Rmult u x) (Rmult v y)) b).
Axiom thm_REAL_ARCH_LT : forall x : R, exists n : N, Rlt x (R_of_N n).
Axiom thm_REAL_ARCH_INV : forall e : R, (Rlt (R_of_N N0) e) = (exists n : N, (~ (n = N0)) /\ ((Rlt (R_of_N N0) (Rinv (R_of_N n))) /\ (Rlt (Rinv (R_of_N n)) e))).
Axiom thm_REAL_ARCH_POW_INV : forall x : R, forall y : R, ((Rlt (R_of_N N0) y) /\ (Rlt x (R_of_N ((BIT1 N0))))) -> exists n : N, Rlt (Rpow x n) y.
Axiom thm_real_sgn : forall x : R, (Rsgn x) = (@COND R (Rlt (R_of_N N0) x) (R_of_N ((BIT1 N0))) (@COND R (Rlt x (R_of_N N0)) (Ropp (R_of_N ((BIT1 N0)))) (R_of_N N0))).
Axiom thm_REAL_SGN_0 : (Rsgn (R_of_N N0)) = (R_of_N N0).
Axiom thm_REAL_SGN_NEG : forall x : R, (Rsgn (Ropp x)) = (Ropp (Rsgn x)).
Axiom thm_REAL_SGN_ABS : forall x : R, (Rmult (Rsgn x) (Rabs x)) = x.
Axiom thm_REAL_SGN_ABS_ALT : forall x : R, (Rmult (Rsgn x) x) = (Rabs x).
Axiom thm_REAL_EQ_SGN_ABS : forall x : R, forall y : R, (x = y) = (((Rsgn x) = (Rsgn y)) /\ ((Rabs x) = (Rabs y))).
Axiom thm_REAL_ABS_SGN : forall x : R, (Rabs (Rsgn x)) = (Rsgn (Rabs x)).
Axiom thm_REAL_SGN : forall x : R, (Rsgn x) = (Rdiv x (Rabs x)).
Axiom thm_REAL_SGN_MUL : forall x : R, forall y : R, (Rsgn (Rmult x y)) = (Rmult (Rsgn x) (Rsgn y)).
Axiom thm_REAL_SGN_INV : forall x : R, (Rsgn (Rinv x)) = (Rsgn x).
Axiom thm_REAL_SGN_DIV : forall x : R, forall y : R, (Rsgn (Rdiv x y)) = (Rdiv (Rsgn x) (Rsgn y)).
Axiom thm_REAL_SGN_EQ : (forall x : R, ((Rsgn x) = (R_of_N N0)) = (x = (R_of_N N0))) /\ ((forall x : R, ((Rsgn x) = (R_of_N ((BIT1 N0)))) = (Rgt x (R_of_N N0))) /\ (forall x : R, ((Rsgn x) = (Ropp (R_of_N ((BIT1 N0))))) = (Rlt x (R_of_N N0)))).
Axiom thm_REAL_SGN_CASES : forall x : R, ((Rsgn x) = (R_of_N N0)) \/ (((Rsgn x) = (R_of_N ((BIT1 N0)))) \/ ((Rsgn x) = (Ropp (R_of_N ((BIT1 N0)))))).
Axiom thm_REAL_SGN_INEQS : (forall x : R, (Rle (R_of_N N0) (Rsgn x)) = (Rle (R_of_N N0) x)) /\ ((forall x : R, (Rlt (R_of_N N0) (Rsgn x)) = (Rlt (R_of_N N0) x)) /\ ((forall x : R, (Rge (R_of_N N0) (Rsgn x)) = (Rge (R_of_N N0) x)) /\ ((forall x : R, (Rgt (R_of_N N0) (Rsgn x)) = (Rgt (R_of_N N0) x)) /\ ((forall x : R, ((R_of_N N0) = (Rsgn x)) = ((R_of_N N0) = x)) /\ ((forall x : R, (Rle (Rsgn x) (R_of_N N0)) = (Rle x (R_of_N N0))) /\ ((forall x : R, (Rlt (Rsgn x) (R_of_N N0)) = (Rlt x (R_of_N N0))) /\ ((forall x : R, (Rge (Rsgn x) (R_of_N N0)) = (Rge x (R_of_N N0))) /\ ((forall x : R, (Rgt (Rsgn x) (R_of_N N0)) = (Rgt x (R_of_N N0))) /\ (forall x : R, ((Rsgn x) = (R_of_N N0)) = (x = (R_of_N N0))))))))))).
Axiom thm_REAL_SGN_POW : forall x : R, forall n : N, (Rsgn (Rpow x n)) = (Rpow (Rsgn x) n).
Axiom thm_REAL_SGN_POW_2 : forall x : R, (Rsgn (Rpow x ((BIT0 (BIT1 N0))))) = (Rsgn (Rabs x)).
Axiom thm_REAL_SGN_REAL_SGN : forall x : R, (Rsgn (Rsgn x)) = (Rsgn x).
Axiom thm_REAL_INV_SGN : forall x : R, (Rinv (Rsgn x)) = (Rsgn x).
Axiom thm_REAL_SGN_EQ_INEQ : forall x : R, forall y : R, ((Rsgn x) = (Rsgn y)) = ((x = y) \/ (Rlt (Rabs (Rminus x y)) (Rmax (Rabs x) (Rabs y)))).
Axiom thm_REAL_SGNS_EQ : forall x : R, forall y : R, ((Rsgn x) = (Rsgn y)) = (((x = (R_of_N N0)) = (y = (R_of_N N0))) /\ (((Rgt x (R_of_N N0)) = (Rgt y (R_of_N N0))) /\ ((Rlt x (R_of_N N0)) = (Rlt y (R_of_N N0))))).
Axiom thm_REAL_SGNS_EQ_ALT : forall x : R, forall y : R, ((Rsgn x) = (Rsgn y)) = (((x = (R_of_N N0)) -> y = (R_of_N N0)) /\ (((Rgt x (R_of_N N0)) -> Rgt y (R_of_N N0)) /\ ((Rlt x (R_of_N N0)) -> Rlt y (R_of_N N0)))).
Axiom thm_REAL_WLOG_LE : forall (P : R -> R -> Prop), ((forall x : R, forall y : R, (P x y) = (P y x)) /\ (forall x : R, forall y : R, (Rle x y) -> P x y)) -> forall x : R, forall y : R, P x y.
Axiom thm_REAL_WLOG_LT : forall (P : R -> R -> Prop), ((forall x : R, P x x) /\ ((forall x : R, forall y : R, (P x y) = (P y x)) /\ (forall x : R, forall y : R, (Rlt x y) -> P x y))) -> forall x : R, forall y : R, P x y.
Axiom thm_REAL_WLOG_LE_3 : forall P : R -> R -> R -> Prop, ((forall x : R, forall y : R, forall z : R, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : R, forall y : R, forall z : R, ((Rle x y) /\ (Rle y z)) -> P x y z)) -> forall x : R, forall y : R, forall z : R, P x y z.
Axiom thm_sqrt : forall x : R, (sqrt x) = (@ε R (fun y : R => ((Rsgn y) = (Rsgn x)) /\ ((Rpow y ((BIT0 (BIT1 N0)))) = (Rabs x)))).
Axiom thm_SQRT_UNIQUE : forall x : R, forall y : R, ((Rle (R_of_N N0) y) /\ ((Rpow y ((BIT0 (BIT1 N0)))) = x)) -> (sqrt x) = y.
Axiom thm_POW_2_SQRT : forall x : R, (Rle (R_of_N N0) x) -> (sqrt (Rpow x ((BIT0 (BIT1 N0))))) = x.
Axiom thm_SQRT_0 : (sqrt (R_of_N N0)) = (R_of_N N0).
Axiom thm_SQRT_1 : (sqrt (R_of_N ((BIT1 N0)))) = (R_of_N ((BIT1 N0))).
Axiom thm_POW_2_SQRT_ABS : forall x : R, (sqrt (Rpow x ((BIT0 (BIT1 N0))))) = (Rabs x).
Axiom thm_SQRT_WORKS_GEN : forall x : R, ((Rsgn (sqrt x)) = (Rsgn x)) /\ ((Rpow (sqrt x) ((BIT0 (BIT1 N0)))) = (Rabs x)).
Axiom thm_SQRT_UNIQUE_GEN : forall x : R, forall y : R, (((Rsgn y) = (Rsgn x)) /\ ((Rpow y ((BIT0 (BIT1 N0)))) = (Rabs x))) -> (sqrt x) = y.
Axiom thm_SQRT_NEG : forall x : R, (sqrt (Ropp x)) = (Ropp (sqrt x)).
Axiom thm_REAL_SGN_SQRT : forall x : R, (Rsgn (sqrt x)) = (Rsgn x).
Axiom thm_SQRT_WORKS : forall x : R, (Rle (R_of_N N0) x) -> (Rle (R_of_N N0) (sqrt x)) /\ ((Rpow (sqrt x) ((BIT0 (BIT1 N0)))) = x).
Axiom thm_REAL_POS_EQ_SQUARE : forall x : R, (Rle (R_of_N N0) x) = (exists y : R, (Rpow y ((BIT0 (BIT1 N0)))) = x).
Axiom thm_SQRT_POS_LE : forall x : R, (Rle (R_of_N N0) x) -> Rle (R_of_N N0) (sqrt x).
Axiom thm_SQRT_POW_2 : forall x : R, (Rle (R_of_N N0) x) -> (Rpow (sqrt x) ((BIT0 (BIT1 N0)))) = x.
Axiom thm_SQRT_POW2 : forall x : R, ((Rpow (sqrt x) ((BIT0 (BIT1 N0)))) = x) = (Rle (R_of_N N0) x).
Axiom thm_SQRT_MUL : forall x : R, forall y : R, (sqrt (Rmult x y)) = (Rmult (sqrt x) (sqrt y)).
Axiom thm_SQRT_INV : forall x : R, (sqrt (Rinv x)) = (Rinv (sqrt x)).
Axiom thm_SQRT_DIV : forall x : R, forall y : R, (sqrt (Rdiv x y)) = (Rdiv (sqrt x) (sqrt y)).
Axiom thm_SQRT_LT_0 : forall x : R, (Rlt (R_of_N N0) (sqrt x)) = (Rlt (R_of_N N0) x).
Axiom thm_SQRT_EQ_0 : forall x : R, ((sqrt x) = (R_of_N N0)) = (x = (R_of_N N0)).
Axiom thm_SQRT_LE_0 : forall x : R, (Rle (R_of_N N0) (sqrt x)) = (Rle (R_of_N N0) x).
Axiom thm_REAL_ABS_SQRT : forall x : R, (Rabs (sqrt x)) = (sqrt (Rabs x)).
Axiom thm_SQRT_MONO_LT : forall x : R, forall y : R, (Rlt x y) -> Rlt (sqrt x) (sqrt y).
Axiom thm_SQRT_MONO_LE : forall x : R, forall y : R, (Rle x y) -> Rle (sqrt x) (sqrt y).
Axiom thm_SQRT_MONO_LT_EQ : forall x : R, forall y : R, (Rlt (sqrt x) (sqrt y)) = (Rlt x y).
Axiom thm_SQRT_MONO_LE_EQ : forall x : R, forall y : R, (Rle (sqrt x) (sqrt y)) = (Rle x y).
Axiom thm_SQRT_INJ : forall x : R, forall y : R, ((sqrt x) = (sqrt y)) = (x = y).
Axiom thm_SQRT_EQ_1 : forall x : R, ((sqrt x) = (R_of_N ((BIT1 N0)))) = (x = (R_of_N ((BIT1 N0)))).
Axiom thm_SQRT_POS_LT : forall x : R, (Rlt (R_of_N N0) x) -> Rlt (R_of_N N0) (sqrt x).
Axiom thm_REAL_LE_LSQRT : forall x : R, forall y : R, ((Rle (R_of_N N0) y) /\ (Rle x (Rpow y ((BIT0 (BIT1 N0)))))) -> Rle (sqrt x) y.
Axiom thm_REAL_LE_RSQRT : forall x : R, forall y : R, (Rle (Rpow x ((BIT0 (BIT1 N0)))) y) -> Rle x (sqrt y).
Axiom thm_REAL_LT_LSQRT : forall x : R, forall y : R, ((Rle (R_of_N N0) y) /\ (Rlt x (Rpow y ((BIT0 (BIT1 N0)))))) -> Rlt (sqrt x) y.
Axiom thm_REAL_LT_RSQRT : forall x : R, forall y : R, (Rlt (Rpow x ((BIT0 (BIT1 N0)))) y) -> Rlt x (sqrt y).
Axiom thm_SQRT_EVEN_POW2 : forall n : N, (N.Even n) -> (sqrt (Rpow (R_of_N ((BIT0 (BIT1 N0)))) n)) = (Rpow (R_of_N ((BIT0 (BIT1 N0)))) (N.div n ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_DIV_SQRT : forall x : R, (Rle (R_of_N N0) x) -> (Rdiv x (sqrt x)) = (sqrt x).
Axiom thm_REAL_RSQRT_LE : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ ((Rle (R_of_N N0) y) /\ (Rle x (sqrt y)))) -> Rle (Rpow x ((BIT0 (BIT1 N0)))) y.
Axiom thm_REAL_LSQRT_LE : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rle (sqrt x) y)) -> Rle x (Rpow y ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_SQRT_POW_2 : forall x : R, (Rpow (sqrt x) ((BIT0 (BIT1 N0)))) = (Rabs x).
Axiom thm_REAL_ABS_LE_SQRT_POS : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rle (R_of_N N0) y)) -> Rle (Rabs (Rminus (sqrt x) (sqrt y))) (sqrt (Rabs (Rminus x y))).
Axiom thm_REAL_ABS_LE_SQRT : forall x : R, forall y : R, Rle (Rabs (Rminus (sqrt x) (sqrt y))) (sqrt (Rmult (R_of_N ((BIT0 (BIT1 N0)))) (Rabs (Rminus x y)))).
Axiom thm_DECIMAL : forall x : N, forall y : N, (DECIMAL x y) = (Rdiv (R_of_N x) (R_of_N y)).
Axiom thm_RAT_LEMMA1 : forall (x1 : R) (x2 : R) (y1 : R) (y2 : R), ((~ (y1 = (R_of_N N0))) /\ (~ (y2 = (R_of_N N0)))) -> (Rplus (Rdiv x1 y1) (Rdiv x2 y2)) = (Rmult (Rplus (Rmult x1 y2) (Rmult x2 y1)) (Rmult (Rinv y1) (Rinv y2))).
Axiom thm_RAT_LEMMA2 : forall (x1 : R) (x2 : R) (y1 : R) (y2 : R), ((Rlt (R_of_N N0) y1) /\ (Rlt (R_of_N N0) y2)) -> (Rplus (Rdiv x1 y1) (Rdiv x2 y2)) = (Rmult (Rplus (Rmult x1 y2) (Rmult x2 y1)) (Rmult (Rinv y1) (Rinv y2))).
Axiom thm_RAT_LEMMA3 : forall (x1 : R) (x2 : R) (y1 : R) (y2 : R), ((Rlt (R_of_N N0) y1) /\ (Rlt (R_of_N N0) y2)) -> (Rminus (Rdiv x1 y1) (Rdiv x2 y2)) = (Rmult (Rminus (Rmult x1 y2) (Rmult x2 y1)) (Rmult (Rinv y1) (Rinv y2))).
Axiom thm_RAT_LEMMA4 : forall (x1 : R) (y2 : R) (x2 : R) (y1 : R), ((Rlt (R_of_N N0) y1) /\ (Rlt (R_of_N N0) y2)) -> (Rle (Rdiv x1 y1) (Rdiv x2 y2)) = (Rle (Rmult x1 y2) (Rmult x2 y1)).
Axiom thm_RAT_LEMMA5 : forall (x1 : R) (y2 : R) (x2 : R) (y1 : R), ((Rlt (R_of_N N0) y1) /\ (Rlt (R_of_N N0) y2)) -> ((Rdiv x1 y1) = (Rdiv x2 y2)) = ((Rmult x1 y2) = (Rmult x2 y1)).
Axiom thm_REAL_LE_TRANS_LE : forall x : R, forall y : R, (Rle x y) = (forall z : R, (Rle y z) -> Rle x z).
Axiom thm_REAL_LE_TRANS_LTE : forall x : R, forall y : R, (Rle x y) = (forall z : R, (Rlt y z) -> Rle x z).
Axiom thm_REAL_LE_TRANS_LT : forall x : R, forall y : R, (Rle x y) = (forall z : R, (Rlt y z) -> Rlt x z).
Axiom thm_REAL_SHRINK_RANGE : forall x : R, Rlt (Rabs (Rdiv x (Rplus (R_of_N ((BIT1 N0))) (Rabs x)))) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_SHRINK_LT : forall x : R, forall y : R, (Rlt (Rdiv x (Rplus (R_of_N ((BIT1 N0))) (Rabs x))) (Rdiv y (Rplus (R_of_N ((BIT1 N0))) (Rabs y)))) = (Rlt x y).
Axiom thm_REAL_SHRINK_LE : forall x : R, forall y : R, (Rle (Rdiv x (Rplus (R_of_N ((BIT1 N0))) (Rabs x))) (Rdiv y (Rplus (R_of_N ((BIT1 N0))) (Rabs y)))) = (Rle x y).
Axiom thm_REAL_SHRINK_EQ : forall x : R, forall y : R, ((Rdiv x (Rplus (R_of_N ((BIT1 N0))) (Rabs x))) = (Rdiv y (Rplus (R_of_N ((BIT1 N0))) (Rabs y)))) = (x = y).
Axiom thm_REAL_SHRINK_GALOIS : forall x : R, forall y : R, ((Rdiv x (Rplus (R_of_N ((BIT1 N0))) (Rabs x))) = y) = ((Rlt (Rabs y) (R_of_N ((BIT1 N0)))) /\ ((Rdiv y (Rminus (R_of_N ((BIT1 N0))) (Rabs y))) = x)).
Axiom thm_REAL_GROW_SHRINK : forall x : R, (Rdiv (Rdiv x (Rplus (R_of_N ((BIT1 N0))) (Rabs x))) (Rminus (R_of_N ((BIT1 N0))) (Rabs (Rdiv x (Rplus (R_of_N ((BIT1 N0))) (Rabs x)))))) = x.
Axiom thm_REAL_SHRINK_GROW_EQ : forall x : R, ((Rdiv (Rdiv x (Rminus (R_of_N ((BIT1 N0))) (Rabs x))) (Rplus (R_of_N ((BIT1 N0))) (Rabs (Rdiv x (Rminus (R_of_N ((BIT1 N0))) (Rabs x)))))) = x) = (Rlt (Rabs x) (R_of_N ((BIT1 N0)))).
Axiom thm_REAL_SHRINK_GROW : forall x : R, (Rlt (Rabs x) (R_of_N ((BIT1 N0)))) -> (Rdiv (Rdiv x (Rminus (R_of_N ((BIT1 N0))) (Rabs x))) (Rplus (R_of_N ((BIT1 N0))) (Rabs (Rdiv x (Rminus (R_of_N ((BIT1 N0))) (Rabs x)))))) = x.
Axiom thm_integer : forall x : R, (integer x) = (exists n : N, (Rabs x) = (R_of_N n)).
Axiom thm_is_int : forall (x : R), (integer x) = (exists n : N, (x = (R_of_N n)) \/ (x = (Ropp (R_of_N n)))).
Axiom thm_dest_int_rep : forall i : Z, exists n : N, ((IZR i) = (R_of_N n)) \/ ((IZR i) = (Ropp (R_of_N n))).
Axiom thm_INTEGER_REAL_OF_INT : forall x : Z, integer (IZR x).
Axiom thm_int_eq : forall x : Z, forall y : Z, (x = y) = ((IZR x) = (IZR y)).
Axiom thm_int_le : forall x : Z, forall y : Z, (Z.le x y) = (Rle (IZR x) (IZR y)).
Axiom thm_int_lt : forall x : Z, forall y : Z, (Z.lt x y) = (Rlt (IZR x) (IZR y)).
Axiom thm_int_ge : forall x : Z, forall y : Z, (Z.ge x y) = (Rge (IZR x) (IZR y)).
Axiom thm_int_gt : forall x : Z, forall y : Z, (Z.gt x y) = (Rgt (IZR x) (IZR y)).
Axiom thm_int_of_num : forall n : N, (Z_of_N n) = (int_of_real (R_of_N n)).
Axiom thm_int_of_num_th : forall n : N, (IZR (Z_of_N n)) = (R_of_N n).
Axiom thm_int_neg : forall i : Z, (Z.opp i) = (int_of_real (Ropp (IZR i))).
Axiom thm_int_neg_th : forall x : Z, (IZR (Z.opp x)) = (Ropp (IZR x)).
Axiom thm_int_add : forall x : Z, forall y : Z, (Z.add x y) = (int_of_real (Rplus (IZR x) (IZR y))).
Axiom thm_int_add_th : forall x : Z, forall y : Z, (IZR (Z.add x y)) = (Rplus (IZR x) (IZR y)).
Axiom thm_int_sub : forall x : Z, forall y : Z, (Z.sub x y) = (int_of_real (Rminus (IZR x) (IZR y))).
Axiom thm_int_sub_th : forall x : Z, forall y : Z, (IZR (Z.sub x y)) = (Rminus (IZR x) (IZR y)).
Axiom thm_int_mul : forall x : Z, forall y : Z, (Z.mul x y) = (int_of_real (Rmult (IZR x) (IZR y))).
Axiom thm_int_mul_th : forall x : Z, forall y : Z, (IZR (Z.mul x y)) = (Rmult (IZR x) (IZR y)).
Axiom thm_int_abs : forall x : Z, (Z.abs x) = (int_of_real (Rabs (IZR x))).
Axiom thm_int_abs_th : forall x : Z, (IZR (Z.abs x)) = (Rabs (IZR x)).
Axiom thm_int_sgn : forall x : Z, (Z.sgn x) = (int_of_real (Rsgn (IZR x))).
Axiom thm_int_sgn_th : forall x : Z, (IZR (Z.sgn x)) = (Rsgn (IZR x)).
Axiom thm_int_max : forall x : Z, forall y : Z, (Z.max x y) = (int_of_real (Rmax (IZR x) (IZR y))).
Axiom thm_int_max_th : forall x : Z, forall y : Z, (IZR (Z.max x y)) = (Rmax (IZR x) (IZR y)).
Axiom thm_int_min : forall x : Z, forall y : Z, (Z.min x y) = (int_of_real (Rmin (IZR x) (IZR y))).
Axiom thm_int_min_th : forall x : Z, forall y : Z, (IZR (Z.min x y)) = (Rmin (IZR x) (IZR y)).
Axiom thm_int_pow : forall x : Z, forall n : N, (Zpow x n) = (int_of_real (Rpow (IZR x) n)).
Axiom thm_int_pow_th : forall x : Z, forall n : N, (IZR (Zpow x n)) = (Rpow (IZR x) n).
Axiom thm_REAL_OF_INT_CLAUSES : (forall x : Z, forall y : Z, ((IZR x) = (IZR y)) = (x = y)) /\ ((forall x : Z, forall y : Z, (Rge (IZR x) (IZR y)) = (Z.ge x y)) /\ ((forall x : Z, forall y : Z, (Rgt (IZR x) (IZR y)) = (Z.gt x y)) /\ ((forall x : Z, forall y : Z, (Rle (IZR x) (IZR y)) = (Z.le x y)) /\ ((forall x : Z, forall y : Z, (Rlt (IZR x) (IZR y)) = (Z.lt x y)) /\ ((forall x : Z, forall y : Z, (Rmax (IZR x) (IZR y)) = (IZR (Z.max x y))) /\ ((forall x : Z, forall y : Z, (Rmin (IZR x) (IZR y)) = (IZR (Z.min x y))) /\ ((forall n : N, (R_of_N n) = (IZR (Z_of_N n))) /\ ((forall x : Z, (Ropp (IZR x)) = (IZR (Z.opp x))) /\ ((forall x : Z, (Rabs (IZR x)) = (IZR (Z.abs x))) /\ ((forall x : Z, forall y : Z, (Rmax (IZR x) (IZR y)) = (IZR (Z.max x y))) /\ ((forall x : Z, forall y : Z, (Rmin (IZR x) (IZR y)) = (IZR (Z.min x y))) /\ ((forall x : Z, (Rsgn (IZR x)) = (IZR (Z.sgn x))) /\ ((forall x : Z, forall y : Z, (Rplus (IZR x) (IZR y)) = (IZR (Z.add x y))) /\ ((forall x : Z, forall y : Z, (Rminus (IZR x) (IZR y)) = (IZR (Z.sub x y))) /\ ((forall x : Z, forall y : Z, (Rmult (IZR x) (IZR y)) = (IZR (Z.mul x y))) /\ (forall x : Z, forall n : N, (Rpow (IZR x) n) = (IZR (Zpow x n)))))))))))))))))).
Axiom thm_INT_IMAGE : forall x : Z, (exists n : N, x = (Z_of_N n)) \/ (exists n : N, x = (Z.opp (Z_of_N n))).
Axiom thm_FORALL_INT_CASES : forall P : Z -> Prop, (forall x : Z, P x) = ((forall n : N, P (Z_of_N n)) /\ (forall n : N, P (Z.opp (Z_of_N n)))).
Axiom thm_EXISTS_INT_CASES : forall P : Z -> Prop, (exists x : Z, P x) = ((exists n : N, P (Z_of_N n)) \/ (exists n : N, P (Z.opp (Z_of_N n)))).
Axiom thm_INT_LT_DISCRETE : forall x : Z, forall y : Z, (Z.lt x y) = (Z.le (Z.add x (Z_of_N ((BIT1 N0)))) y).
Axiom thm_INT_GT_DISCRETE : forall x : Z, forall y : Z, (Z.gt x y) = (Z.ge x (Z.add y (Z_of_N ((BIT1 N0))))).
Axiom thm_INT_ABS_0 : (Z.abs (Z_of_N N0)) = (Z_of_N N0).
Axiom thm_INT_ABS_1 : (Z.abs (Z_of_N ((BIT1 N0)))) = (Z_of_N ((BIT1 N0))).
Axiom thm_INT_ABS_ABS : forall x : Z, (Z.abs (Z.abs x)) = (Z.abs x).
Axiom thm_INT_ABS_BETWEEN : forall x : Z, forall y : Z, forall d : Z, ((Z.lt (Z_of_N N0) d) /\ ((Z.lt (Z.sub x d) y) /\ (Z.lt y (Z.add x d)))) = (Z.lt (Z.abs (Z.sub y x)) d).
Axiom thm_INT_ABS_BETWEEN1 : forall x : Z, forall y : Z, forall z : Z, ((Z.lt x z) /\ (Z.lt (Z.abs (Z.sub y x)) (Z.sub z x))) -> Z.lt y z.
Axiom thm_INT_ABS_BETWEEN2 : forall x0 : Z, forall x : Z, forall y0 : Z, forall y : Z, ((Z.lt x0 y0) /\ ((Z.lt (Z.mul (Z_of_N ((BIT0 (BIT1 N0)))) (Z.abs (Z.sub x x0))) (Z.sub y0 x0)) /\ (Z.lt (Z.mul (Z_of_N ((BIT0 (BIT1 N0)))) (Z.abs (Z.sub y y0))) (Z.sub y0 x0)))) -> Z.lt x y.
Axiom thm_INT_ABS_BOUND : forall x : Z, forall y : Z, forall d : Z, (Z.lt (Z.abs (Z.sub x y)) d) -> Z.lt y (Z.add x d).
Axiom thm_INT_ABS_BOUNDS : forall x : Z, forall k : Z, (Z.le (Z.abs x) k) = ((Z.le (Z.opp k) x) /\ (Z.le x k)).
Axiom thm_INT_ABS_CASES : forall x : Z, (x = (Z_of_N N0)) \/ (Z.lt (Z_of_N N0) (Z.abs x)).
Axiom thm_INT_ABS_CIRCLE : forall x : Z, forall y : Z, forall h : Z, (Z.lt (Z.abs h) (Z.sub (Z.abs y) (Z.abs x))) -> Z.lt (Z.abs (Z.add x h)) (Z.abs y).
Axiom thm_INT_ABS_LE : forall x : Z, Z.le x (Z.abs x).
Axiom thm_INT_ABS_MUL : forall x : Z, forall y : Z, (Z.abs (Z.mul x y)) = (Z.mul (Z.abs x) (Z.abs y)).
Axiom thm_INT_ABS_NEG : forall x : Z, (Z.abs (Z.opp x)) = (Z.abs x).
Axiom thm_INT_ABS_NUM : forall n : N, (Z.abs (Z_of_N n)) = (Z_of_N n).
Axiom thm_INT_ABS_NZ : forall x : Z, (~ (x = (Z_of_N N0))) = (Z.lt (Z_of_N N0) (Z.abs x)).
Axiom thm_INT_ABS_POS : forall x : Z, Z.le (Z_of_N N0) (Z.abs x).
Axiom thm_INT_ABS_POW : forall x : Z, forall n : N, (Z.abs (Zpow x n)) = (Zpow (Z.abs x) n).
Axiom thm_INT_ABS_REFL : forall x : Z, ((Z.abs x) = x) = (Z.le (Z_of_N N0) x).
Axiom thm_INT_ABS_SGN : forall x : Z, (Z.abs (Z.sgn x)) = (Z.sgn (Z.abs x)).
Axiom thm_INT_ABS_SIGN : forall x : Z, forall y : Z, (Z.lt (Z.abs (Z.sub x y)) y) -> Z.lt (Z_of_N N0) x.
Axiom thm_INT_ABS_SIGN2 : forall x : Z, forall y : Z, (Z.lt (Z.abs (Z.sub x y)) (Z.opp y)) -> Z.lt x (Z_of_N N0).
Axiom thm_INT_ABS_STILLNZ : forall x : Z, forall y : Z, (Z.lt (Z.abs (Z.sub x y)) (Z.abs y)) -> ~ (x = (Z_of_N N0)).
Axiom thm_INT_ABS_SUB : forall x : Z, forall y : Z, (Z.abs (Z.sub x y)) = (Z.abs (Z.sub y x)).
Axiom thm_INT_ABS_SUB_ABS : forall x : Z, forall y : Z, Z.le (Z.abs (Z.sub (Z.abs x) (Z.abs y))) (Z.abs (Z.sub x y)).
Axiom thm_INT_ABS_TRIANGLE : forall x : Z, forall y : Z, Z.le (Z.abs (Z.add x y)) (Z.add (Z.abs x) (Z.abs y)).
Axiom thm_INT_ABS_ZERO : forall x : Z, ((Z.abs x) = (Z_of_N N0)) = (x = (Z_of_N N0)).
Axiom thm_INT_ADD2_SUB2 : forall a : Z, forall b : Z, forall c : Z, forall d : Z, (Z.sub (Z.add a b) (Z.add c d)) = (Z.add (Z.sub a c) (Z.sub b d)).
Axiom thm_INT_ADD_AC : forall (n : Z) (m : Z) (p : Z), ((Z.add m n) = (Z.add n m)) /\ (((Z.add (Z.add m n) p) = (Z.add m (Z.add n p))) /\ ((Z.add m (Z.add n p)) = (Z.add n (Z.add m p)))).
Axiom thm_INT_ADD_ASSOC : forall x : Z, forall y : Z, forall z : Z, (Z.add x (Z.add y z)) = (Z.add (Z.add x y) z).
Axiom thm_INT_ADD_LDISTRIB : forall x : Z, forall y : Z, forall z : Z, (Z.mul x (Z.add y z)) = (Z.add (Z.mul x y) (Z.mul x z)).
Axiom thm_INT_ADD_LID : forall x : Z, (Z.add (Z_of_N N0) x) = x.
Axiom thm_INT_ADD_LINV : forall x : Z, (Z.add (Z.opp x) x) = (Z_of_N N0).
Axiom thm_INT_ADD_RDISTRIB : forall x : Z, forall y : Z, forall z : Z, (Z.mul (Z.add x y) z) = (Z.add (Z.mul x z) (Z.mul y z)).
Axiom thm_INT_ADD_RID : forall x : Z, (Z.add x (Z_of_N N0)) = x.
Axiom thm_INT_ADD_RINV : forall x : Z, (Z.add x (Z.opp x)) = (Z_of_N N0).
Axiom thm_INT_ADD_SUB : forall x : Z, forall y : Z, (Z.sub (Z.add x y) x) = y.
Axiom thm_INT_ADD_SUB2 : forall x : Z, forall y : Z, (Z.sub x (Z.add x y)) = (Z.opp y).
Axiom thm_INT_ADD_SYM : forall x : Z, forall y : Z, (Z.add x y) = (Z.add y x).
Axiom thm_INT_BOUNDS_LE : forall x : Z, forall k : Z, ((Z.le (Z.opp k) x) /\ (Z.le x k)) = (Z.le (Z.abs x) k).
Axiom thm_INT_BOUNDS_LT : forall x : Z, forall k : Z, ((Z.lt (Z.opp k) x) /\ (Z.lt x k)) = (Z.lt (Z.abs x) k).
Axiom thm_INT_DIFFSQ : forall x : Z, forall y : Z, (Z.mul (Z.add x y) (Z.sub x y)) = (Z.sub (Z.mul x x) (Z.mul y y)).
Axiom thm_INT_ENTIRE : forall x : Z, forall y : Z, ((Z.mul x y) = (Z_of_N N0)) = ((x = (Z_of_N N0)) \/ (y = (Z_of_N N0))).
Axiom thm_INT_EQ_ADD_LCANCEL : forall x : Z, forall y : Z, forall z : Z, ((Z.add x y) = (Z.add x z)) = (y = z).
Axiom thm_INT_EQ_ADD_LCANCEL_0 : forall x : Z, forall y : Z, ((Z.add x y) = x) = (y = (Z_of_N N0)).
Axiom thm_INT_EQ_ADD_RCANCEL : forall x : Z, forall y : Z, forall z : Z, ((Z.add x z) = (Z.add y z)) = (x = y).
Axiom thm_INT_EQ_ADD_RCANCEL_0 : forall x : Z, forall y : Z, ((Z.add x y) = y) = (x = (Z_of_N N0)).
Axiom thm_INT_EQ_IMP_LE : forall x : Z, forall y : Z, (x = y) -> Z.le x y.
Axiom thm_INT_EQ_LCANCEL_IMP : forall x : Z, forall y : Z, forall z : Z, ((~ (z = (Z_of_N N0))) /\ ((Z.mul z x) = (Z.mul z y))) -> x = y.
Axiom thm_INT_EQ_MUL_LCANCEL : forall x : Z, forall y : Z, forall z : Z, ((Z.mul x y) = (Z.mul x z)) = ((x = (Z_of_N N0)) \/ (y = z)).
Axiom thm_INT_EQ_MUL_RCANCEL : forall x : Z, forall y : Z, forall z : Z, ((Z.mul x z) = (Z.mul y z)) = ((x = y) \/ (z = (Z_of_N N0))).
Axiom thm_INT_EQ_NEG2 : forall x : Z, forall y : Z, ((Z.opp x) = (Z.opp y)) = (x = y).
Axiom thm_INT_EQ_RCANCEL_IMP : forall x : Z, forall y : Z, forall z : Z, ((~ (z = (Z_of_N N0))) /\ ((Z.mul x z) = (Z.mul y z))) -> x = y.
Axiom thm_INT_EQ_SGN_ABS : forall x : Z, forall y : Z, (x = y) = (((Z.sgn x) = (Z.sgn y)) /\ ((Z.abs x) = (Z.abs y))).
Axiom thm_INT_EQ_SQUARE_ABS : forall x : Z, forall y : Z, ((Z.abs x) = (Z.abs y)) = ((Zpow x ((BIT0 (BIT1 N0)))) = (Zpow y ((BIT0 (BIT1 N0))))).
Axiom thm_INT_EQ_SUB_LADD : forall x : Z, forall y : Z, forall z : Z, (x = (Z.sub y z)) = ((Z.add x z) = y).
Axiom thm_INT_EQ_SUB_RADD : forall x : Z, forall y : Z, forall z : Z, ((Z.sub x y) = z) = (x = (Z.add z y)).
Axiom thm_INT_EVENPOW_ABS : forall x : Z, forall n : N, (N.Even n) -> (Zpow (Z.abs x) n) = (Zpow x n).
Axiom thm_INT_LET_ADD : forall x : Z, forall y : Z, ((Z.le (Z_of_N N0) x) /\ (Z.lt (Z_of_N N0) y)) -> Z.lt (Z_of_N N0) (Z.add x y).
Axiom thm_INT_LET_ADD2 : forall w : Z, forall x : Z, forall y : Z, forall z : Z, ((Z.le w x) /\ (Z.lt y z)) -> Z.lt (Z.add w y) (Z.add x z).
Axiom thm_INT_LET_ANTISYM : forall x : Z, forall y : Z, ~ ((Z.le x y) /\ (Z.lt y x)).
Axiom thm_INT_LET_TOTAL : forall x : Z, forall y : Z, (Z.le x y) \/ (Z.lt y x).
Axiom thm_INT_LET_TRANS : forall x : Z, forall y : Z, forall z : Z, ((Z.le x y) /\ (Z.lt y z)) -> Z.lt x z.
Axiom thm_INT_LE_01 : Z.le (Z_of_N N0) (Z_of_N ((BIT1 N0))).
Axiom thm_INT_LE_ADD : forall x : Z, forall y : Z, ((Z.le (Z_of_N N0) x) /\ (Z.le (Z_of_N N0) y)) -> Z.le (Z_of_N N0) (Z.add x y).
Axiom thm_INT_LE_ADD2 : forall w : Z, forall x : Z, forall y : Z, forall z : Z, ((Z.le w x) /\ (Z.le y z)) -> Z.le (Z.add w y) (Z.add x z).
Axiom thm_INT_LE_ADDL : forall x : Z, forall y : Z, (Z.le y (Z.add x y)) = (Z.le (Z_of_N N0) x).
Axiom thm_INT_LE_ADDR : forall x : Z, forall y : Z, (Z.le x (Z.add x y)) = (Z.le (Z_of_N N0) y).
Axiom thm_INT_LE_ANTISYM : forall x : Z, forall y : Z, ((Z.le x y) /\ (Z.le y x)) = (x = y).
Axiom thm_INT_LE_DOUBLE : forall x : Z, (Z.le (Z_of_N N0) (Z.add x x)) = (Z.le (Z_of_N N0) x).
Axiom thm_INT_LE_LADD : forall x : Z, forall y : Z, forall z : Z, (Z.le (Z.add x y) (Z.add x z)) = (Z.le y z).
Axiom thm_INT_LE_LADD_IMP : forall x : Z, forall y : Z, forall z : Z, (Z.le y z) -> Z.le (Z.add x y) (Z.add x z).
Axiom thm_INT_LE_LCANCEL_IMP : forall x : Z, forall y : Z, forall z : Z, ((Z.lt (Z_of_N N0) x) /\ (Z.le (Z.mul x y) (Z.mul x z))) -> Z.le y z.
Axiom thm_INT_LE_LMUL : forall x : Z, forall y : Z, forall z : Z, ((Z.le (Z_of_N N0) x) /\ (Z.le y z)) -> Z.le (Z.mul x y) (Z.mul x z).
Axiom thm_INT_LE_LMUL_EQ : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z_of_N N0) z) -> (Z.le (Z.mul z x) (Z.mul z y)) = (Z.le x y).
Axiom thm_INT_LE_LNEG : forall x : Z, forall y : Z, (Z.le (Z.opp x) y) = (Z.le (Z_of_N N0) (Z.add x y)).
Axiom thm_INT_LE_LT : forall x : Z, forall y : Z, (Z.le x y) = ((Z.lt x y) \/ (x = y)).
Axiom thm_INT_LE_MAX : forall x : Z, forall y : Z, forall z : Z, (Z.le z (Z.max x y)) = ((Z.le z x) \/ (Z.le z y)).
Axiom thm_INT_LE_MIN : forall x : Z, forall y : Z, forall z : Z, (Z.le z (Z.min x y)) = ((Z.le z x) /\ (Z.le z y)).
Axiom thm_INT_LE_MUL : forall x : Z, forall y : Z, ((Z.le (Z_of_N N0) x) /\ (Z.le (Z_of_N N0) y)) -> Z.le (Z_of_N N0) (Z.mul x y).
Axiom thm_INT_LE_MUL2 : forall w : Z, forall x : Z, forall y : Z, forall z : Z, ((Z.le (Z_of_N N0) w) /\ ((Z.le w x) /\ ((Z.le (Z_of_N N0) y) /\ (Z.le y z)))) -> Z.le (Z.mul w y) (Z.mul x z).
Axiom thm_INT_LE_MUL_EQ : (forall x : Z, forall y : Z, (Z.lt (Z_of_N N0) x) -> (Z.le (Z_of_N N0) (Z.mul x y)) = (Z.le (Z_of_N N0) y)) /\ (forall x : Z, forall y : Z, (Z.lt (Z_of_N N0) y) -> (Z.le (Z_of_N N0) (Z.mul x y)) = (Z.le (Z_of_N N0) x)).
Axiom thm_INT_LE_NEG2 : forall x : Z, forall y : Z, (Z.le (Z.opp x) (Z.opp y)) = (Z.le y x).
Axiom thm_INT_LE_NEGL : forall x : Z, (Z.le (Z.opp x) x) = (Z.le (Z_of_N N0) x).
Axiom thm_INT_LE_NEGR : forall x : Z, (Z.le x (Z.opp x)) = (Z.le x (Z_of_N N0)).
Axiom thm_INT_LE_NEGTOTAL : forall x : Z, (Z.le (Z_of_N N0) x) \/ (Z.le (Z_of_N N0) (Z.opp x)).
Axiom thm_INT_LE_POW2 : forall n : N, Z.le (Z_of_N ((BIT1 N0))) (Zpow (Z_of_N ((BIT0 (BIT1 N0)))) n).
Axiom thm_INT_LE_POW_2 : forall x : Z, Z.le (Z_of_N N0) (Zpow x ((BIT0 (BIT1 N0)))).
Axiom thm_INT_LE_RADD : forall x : Z, forall y : Z, forall z : Z, (Z.le (Z.add x z) (Z.add y z)) = (Z.le x y).
Axiom thm_INT_LE_RCANCEL_IMP : forall x : Z, forall y : Z, forall z : Z, ((Z.lt (Z_of_N N0) z) /\ (Z.le (Z.mul x z) (Z.mul y z))) -> Z.le x y.
Axiom thm_INT_LE_REFL : forall x : Z, Z.le x x.
Axiom thm_INT_LE_RMUL : forall x : Z, forall y : Z, forall z : Z, ((Z.le x y) /\ (Z.le (Z_of_N N0) z)) -> Z.le (Z.mul x z) (Z.mul y z).
Axiom thm_INT_LE_RMUL_EQ : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z_of_N N0) z) -> (Z.le (Z.mul x z) (Z.mul y z)) = (Z.le x y).
Axiom thm_INT_LE_RNEG : forall x : Z, forall y : Z, (Z.le x (Z.opp y)) = (Z.le (Z.add x y) (Z_of_N N0)).
Axiom thm_INT_LE_SQUARE : forall x : Z, Z.le (Z_of_N N0) (Z.mul x x).
Axiom thm_INT_LE_SQUARE_ABS : forall x : Z, forall y : Z, (Z.le (Z.abs x) (Z.abs y)) = (Z.le (Zpow x ((BIT0 (BIT1 N0)))) (Zpow y ((BIT0 (BIT1 N0))))).
Axiom thm_INT_LE_SUB_LADD : forall x : Z, forall y : Z, forall z : Z, (Z.le x (Z.sub y z)) = (Z.le (Z.add x z) y).
Axiom thm_INT_LE_SUB_RADD : forall x : Z, forall y : Z, forall z : Z, (Z.le (Z.sub x y) z) = (Z.le x (Z.add z y)).
Axiom thm_INT_LE_TOTAL : forall x : Z, forall y : Z, (Z.le x y) \/ (Z.le y x).
Axiom thm_INT_LE_TRANS : forall x : Z, forall y : Z, forall z : Z, ((Z.le x y) /\ (Z.le y z)) -> Z.le x z.
Axiom thm_INT_LNEG_UNIQ : forall x : Z, forall y : Z, ((Z.add x y) = (Z_of_N N0)) = (x = (Z.opp y)).
Axiom thm_INT_LTE_ADD : forall x : Z, forall y : Z, ((Z.lt (Z_of_N N0) x) /\ (Z.le (Z_of_N N0) y)) -> Z.lt (Z_of_N N0) (Z.add x y).
Axiom thm_INT_LTE_ADD2 : forall w : Z, forall x : Z, forall y : Z, forall z : Z, ((Z.lt w x) /\ (Z.le y z)) -> Z.lt (Z.add w y) (Z.add x z).
Axiom thm_INT_LTE_ANTISYM : forall x : Z, forall y : Z, ~ ((Z.lt x y) /\ (Z.le y x)).
Axiom thm_INT_LTE_TOTAL : forall x : Z, forall y : Z, (Z.lt x y) \/ (Z.le y x).
Axiom thm_INT_LTE_TRANS : forall x : Z, forall y : Z, forall z : Z, ((Z.lt x y) /\ (Z.le y z)) -> Z.lt x z.
Axiom thm_INT_LT_01 : Z.lt (Z_of_N N0) (Z_of_N ((BIT1 N0))).
Axiom thm_INT_LT_ADD : forall x : Z, forall y : Z, ((Z.lt (Z_of_N N0) x) /\ (Z.lt (Z_of_N N0) y)) -> Z.lt (Z_of_N N0) (Z.add x y).
Axiom thm_INT_LT_ADD1 : forall x : Z, forall y : Z, (Z.le x y) -> Z.lt x (Z.add y (Z_of_N ((BIT1 N0)))).
Axiom thm_INT_LT_ADD2 : forall w : Z, forall x : Z, forall y : Z, forall z : Z, ((Z.lt w x) /\ (Z.lt y z)) -> Z.lt (Z.add w y) (Z.add x z).
Axiom thm_INT_LT_ADDL : forall x : Z, forall y : Z, (Z.lt y (Z.add x y)) = (Z.lt (Z_of_N N0) x).
Axiom thm_INT_LT_ADDNEG : forall x : Z, forall y : Z, forall z : Z, (Z.lt y (Z.add x (Z.opp z))) = (Z.lt (Z.add y z) x).
Axiom thm_INT_LT_ADDNEG2 : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z.add x (Z.opp y)) z) = (Z.lt x (Z.add z y)).
Axiom thm_INT_LT_ADDR : forall x : Z, forall y : Z, (Z.lt x (Z.add x y)) = (Z.lt (Z_of_N N0) y).
Axiom thm_INT_LT_ADD_SUB : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z.add x y) z) = (Z.lt x (Z.sub z y)).
Axiom thm_INT_LT_ANTISYM : forall x : Z, forall y : Z, ~ ((Z.lt x y) /\ (Z.lt y x)).
Axiom thm_INT_LT_GT : forall x : Z, forall y : Z, (Z.lt x y) -> ~ (Z.lt y x).
Axiom thm_INT_LT_IMP_LE : forall x : Z, forall y : Z, (Z.lt x y) -> Z.le x y.
Axiom thm_INT_LT_IMP_NE : forall x : Z, forall y : Z, (Z.lt x y) -> ~ (x = y).
Axiom thm_INT_LT_LADD : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z.add x y) (Z.add x z)) = (Z.lt y z).
Axiom thm_INT_LT_LADD_IMP : forall x : Z, forall y : Z, forall z : Z, (Z.lt y z) -> Z.lt (Z.add x y) (Z.add x z).
Axiom thm_INT_LT_LCANCEL_IMP : forall x : Z, forall y : Z, forall z : Z, ((Z.lt (Z_of_N N0) x) /\ (Z.lt (Z.mul x y) (Z.mul x z))) -> Z.lt y z.
Axiom thm_INT_LT_LE : forall x : Z, forall y : Z, (Z.lt x y) = ((Z.le x y) /\ (~ (x = y))).
Axiom thm_INT_LT_LMUL : forall x : Z, forall y : Z, forall z : Z, ((Z.lt (Z_of_N N0) x) /\ (Z.lt y z)) -> Z.lt (Z.mul x y) (Z.mul x z).
Axiom thm_INT_LT_LMUL_EQ : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z_of_N N0) z) -> (Z.lt (Z.mul z x) (Z.mul z y)) = (Z.lt x y).
Axiom thm_INT_LT_LNEG : forall x : Z, forall y : Z, (Z.lt (Z.opp x) y) = (Z.lt (Z_of_N N0) (Z.add x y)).
Axiom thm_INT_LT_MAX : forall x : Z, forall y : Z, forall z : Z, (Z.lt z (Z.max x y)) = ((Z.lt z x) \/ (Z.lt z y)).
Axiom thm_INT_LT_MIN : forall x : Z, forall y : Z, forall z : Z, (Z.lt z (Z.min x y)) = ((Z.lt z x) /\ (Z.lt z y)).
Axiom thm_INT_LT_MUL : forall x : Z, forall y : Z, ((Z.lt (Z_of_N N0) x) /\ (Z.lt (Z_of_N N0) y)) -> Z.lt (Z_of_N N0) (Z.mul x y).
Axiom thm_INT_LT_MUL2 : forall w : Z, forall x : Z, forall y : Z, forall z : Z, ((Z.le (Z_of_N N0) w) /\ ((Z.lt w x) /\ ((Z.le (Z_of_N N0) y) /\ (Z.lt y z)))) -> Z.lt (Z.mul w y) (Z.mul x z).
Axiom thm_INT_LT_MUL_EQ : (forall x : Z, forall y : Z, (Z.lt (Z_of_N N0) x) -> (Z.lt (Z_of_N N0) (Z.mul x y)) = (Z.lt (Z_of_N N0) y)) /\ (forall x : Z, forall y : Z, (Z.lt (Z_of_N N0) y) -> (Z.lt (Z_of_N N0) (Z.mul x y)) = (Z.lt (Z_of_N N0) x)).
Axiom thm_INT_LT_NEG2 : forall x : Z, forall y : Z, (Z.lt (Z.opp x) (Z.opp y)) = (Z.lt y x).
Axiom thm_INT_LT_NEGTOTAL : forall x : Z, (x = (Z_of_N N0)) \/ ((Z.lt (Z_of_N N0) x) \/ (Z.lt (Z_of_N N0) (Z.opp x))).
Axiom thm_INT_LT_POW2 : forall n : N, Z.lt (Z_of_N N0) (Zpow (Z_of_N ((BIT0 (BIT1 N0)))) n).
Axiom thm_INT_LT_POW_2 : forall x : Z, (Z.lt (Z_of_N N0) (Zpow x ((BIT0 (BIT1 N0))))) = (~ (x = (Z_of_N N0))).
Axiom thm_INT_LT_RADD : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z.add x z) (Z.add y z)) = (Z.lt x y).
Axiom thm_INT_LT_RCANCEL_IMP : forall x : Z, forall y : Z, forall z : Z, ((Z.lt (Z_of_N N0) z) /\ (Z.lt (Z.mul x z) (Z.mul y z))) -> Z.lt x y.
Axiom thm_INT_LT_REFL : forall x : Z, ~ (Z.lt x x).
Axiom thm_INT_LT_RMUL : forall x : Z, forall y : Z, forall z : Z, ((Z.lt x y) /\ (Z.lt (Z_of_N N0) z)) -> Z.lt (Z.mul x z) (Z.mul y z).
Axiom thm_INT_LT_RMUL_EQ : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z_of_N N0) z) -> (Z.lt (Z.mul x z) (Z.mul y z)) = (Z.lt x y).
Axiom thm_INT_LT_RNEG : forall x : Z, forall y : Z, (Z.lt x (Z.opp y)) = (Z.lt (Z.add x y) (Z_of_N N0)).
Axiom thm_INT_LT_SQUARE : forall x : Z, (Z.lt (Z_of_N N0) (Z.mul x x)) = (~ (x = (Z_of_N N0))).
Axiom thm_INT_LT_SQUARE_ABS : forall x : Z, forall y : Z, (Z.lt (Z.abs x) (Z.abs y)) = (Z.lt (Zpow x ((BIT0 (BIT1 N0)))) (Zpow y ((BIT0 (BIT1 N0))))).
Axiom thm_INT_LT_SUB_LADD : forall x : Z, forall y : Z, forall z : Z, (Z.lt x (Z.sub y z)) = (Z.lt (Z.add x z) y).
Axiom thm_INT_LT_SUB_RADD : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z.sub x y) z) = (Z.lt x (Z.add z y)).
Axiom thm_INT_LT_TOTAL : forall x : Z, forall y : Z, (x = y) \/ ((Z.lt x y) \/ (Z.lt y x)).
Axiom thm_INT_LT_TRANS : forall x : Z, forall y : Z, forall z : Z, ((Z.lt x y) /\ (Z.lt y z)) -> Z.lt x z.
Axiom thm_INT_MAX_ACI : forall (z : Z) (x : Z) (y : Z), ((Z.max x y) = (Z.max y x)) /\ (((Z.max (Z.max x y) z) = (Z.max x (Z.max y z))) /\ (((Z.max x (Z.max y z)) = (Z.max y (Z.max x z))) /\ (((Z.max x x) = x) /\ ((Z.max x (Z.max x y)) = (Z.max x y))))).
Axiom thm_INT_MAX_ASSOC : forall x : Z, forall y : Z, forall z : Z, (Z.max x (Z.max y z)) = (Z.max (Z.max x y) z).
Axiom thm_INT_MAX_LE : forall x : Z, forall y : Z, forall z : Z, (Z.le (Z.max x y) z) = ((Z.le x z) /\ (Z.le y z)).
Axiom thm_INT_MAX_LT : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z.max x y) z) = ((Z.lt x z) /\ (Z.lt y z)).
Axiom thm_INT_MAX_MAX : forall x : Z, forall y : Z, (Z.le x (Z.max x y)) /\ (Z.le y (Z.max x y)).
Axiom thm_INT_MAX_MIN : forall x : Z, forall y : Z, (Z.max x y) = (Z.opp (Z.min (Z.opp x) (Z.opp y))).
Axiom thm_INT_MAX_SYM : forall x : Z, forall y : Z, (Z.max x y) = (Z.max y x).
Axiom thm_INT_MIN_ACI : forall (z : Z) (x : Z) (y : Z), ((Z.min x y) = (Z.min y x)) /\ (((Z.min (Z.min x y) z) = (Z.min x (Z.min y z))) /\ (((Z.min x (Z.min y z)) = (Z.min y (Z.min x z))) /\ (((Z.min x x) = x) /\ ((Z.min x (Z.min x y)) = (Z.min x y))))).
Axiom thm_INT_MIN_ASSOC : forall x : Z, forall y : Z, forall z : Z, (Z.min x (Z.min y z)) = (Z.min (Z.min x y) z).
Axiom thm_INT_MIN_LE : forall x : Z, forall y : Z, forall z : Z, (Z.le (Z.min x y) z) = ((Z.le x z) \/ (Z.le y z)).
Axiom thm_INT_MIN_LT : forall x : Z, forall y : Z, forall z : Z, (Z.lt (Z.min x y) z) = ((Z.lt x z) \/ (Z.lt y z)).
Axiom thm_INT_MIN_MAX : forall x : Z, forall y : Z, (Z.min x y) = (Z.opp (Z.max (Z.opp x) (Z.opp y))).
Axiom thm_INT_MIN_MIN : forall x : Z, forall y : Z, (Z.le (Z.min x y) x) /\ (Z.le (Z.min x y) y).
Axiom thm_INT_MIN_SYM : forall x : Z, forall y : Z, (Z.min x y) = (Z.min y x).
Axiom thm_INT_MUL_2 : forall x : Z, (Z.mul (Z_of_N ((BIT0 (BIT1 N0)))) x) = (Z.add x x).
Axiom thm_INT_MUL_AC : forall (n : Z) (m : Z) (p : Z), ((Z.mul m n) = (Z.mul n m)) /\ (((Z.mul (Z.mul m n) p) = (Z.mul m (Z.mul n p))) /\ ((Z.mul m (Z.mul n p)) = (Z.mul n (Z.mul m p)))).
Axiom thm_INT_MUL_ASSOC : forall x : Z, forall y : Z, forall z : Z, (Z.mul x (Z.mul y z)) = (Z.mul (Z.mul x y) z).
Axiom thm_INT_MUL_LID : forall x : Z, (Z.mul (Z_of_N ((BIT1 N0))) x) = x.
Axiom thm_INT_MUL_LNEG : forall x : Z, forall y : Z, (Z.mul (Z.opp x) y) = (Z.opp (Z.mul x y)).
Axiom thm_INT_MUL_LZERO : forall x : Z, (Z.mul (Z_of_N N0) x) = (Z_of_N N0).
Axiom thm_INT_MUL_POS_LE : forall x : Z, forall y : Z, (Z.le (Z_of_N N0) (Z.mul x y)) = ((x = (Z_of_N N0)) \/ ((y = (Z_of_N N0)) \/ (((Z.lt (Z_of_N N0) x) /\ (Z.lt (Z_of_N N0) y)) \/ ((Z.lt x (Z_of_N N0)) /\ (Z.lt y (Z_of_N N0)))))).
Axiom thm_INT_MUL_POS_LT : forall x : Z, forall y : Z, (Z.lt (Z_of_N N0) (Z.mul x y)) = (((Z.lt (Z_of_N N0) x) /\ (Z.lt (Z_of_N N0) y)) \/ ((Z.lt x (Z_of_N N0)) /\ (Z.lt y (Z_of_N N0)))).
Axiom thm_INT_MUL_RID : forall x : Z, (Z.mul x (Z_of_N ((BIT1 N0)))) = x.
Axiom thm_INT_MUL_RNEG : forall x : Z, forall y : Z, (Z.mul x (Z.opp y)) = (Z.opp (Z.mul x y)).
Axiom thm_INT_MUL_RZERO : forall x : Z, (Z.mul x (Z_of_N N0)) = (Z_of_N N0).
Axiom thm_INT_MUL_SYM : forall x : Z, forall y : Z, (Z.mul x y) = (Z.mul y x).
Axiom thm_INT_NEG_0 : (Z.opp (Z_of_N N0)) = (Z_of_N N0).
Axiom thm_INT_NEG_ADD : forall x : Z, forall y : Z, (Z.opp (Z.add x y)) = (Z.add (Z.opp x) (Z.opp y)).
Axiom thm_INT_NEG_EQ : forall x : Z, forall y : Z, ((Z.opp x) = y) = (x = (Z.opp y)).
Axiom thm_INT_NEG_EQ_0 : forall x : Z, ((Z.opp x) = (Z_of_N N0)) = (x = (Z_of_N N0)).
Axiom thm_INT_NEG_GE0 : forall x : Z, (Z.le (Z_of_N N0) (Z.opp x)) = (Z.le x (Z_of_N N0)).
Axiom thm_INT_NEG_GT0 : forall x : Z, (Z.lt (Z_of_N N0) (Z.opp x)) = (Z.lt x (Z_of_N N0)).
Axiom thm_INT_NEG_LE0 : forall x : Z, (Z.le (Z.opp x) (Z_of_N N0)) = (Z.le (Z_of_N N0) x).
Axiom thm_INT_NEG_LMUL : forall x : Z, forall y : Z, (Z.opp (Z.mul x y)) = (Z.mul (Z.opp x) y).
Axiom thm_INT_NEG_LT0 : forall x : Z, (Z.lt (Z.opp x) (Z_of_N N0)) = (Z.lt (Z_of_N N0) x).
Axiom thm_INT_NEG_MINUS1 : forall x : Z, (Z.opp x) = (Z.mul (Z.opp (Z_of_N ((BIT1 N0)))) x).
Axiom thm_INT_NEG_MUL2 : forall x : Z, forall y : Z, (Z.mul (Z.opp x) (Z.opp y)) = (Z.mul x y).
Axiom thm_INT_NEG_NEG : forall x : Z, (Z.opp (Z.opp x)) = x.
Axiom thm_INT_NEG_RMUL : forall x : Z, forall y : Z, (Z.opp (Z.mul x y)) = (Z.mul x (Z.opp y)).
Axiom thm_INT_NEG_SUB : forall x : Z, forall y : Z, (Z.opp (Z.sub x y)) = (Z.sub y x).
Axiom thm_INT_NOT_EQ : forall x : Z, forall y : Z, (~ (x = y)) = ((Z.lt x y) \/ (Z.lt y x)).
Axiom thm_INT_NOT_LE : forall x : Z, forall y : Z, (~ (Z.le x y)) = (Z.lt y x).
Axiom thm_INT_NOT_LT : forall x : Z, forall y : Z, (~ (Z.lt x y)) = (Z.le y x).
Axiom thm_INT_OF_NUM_ADD : forall m : N, forall n : N, (Z.add (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.add m n)).
Axiom thm_INT_OF_NUM_CLAUSES : (forall m : N, forall n : N, ((Z_of_N m) = (Z_of_N n)) = (m = n)) /\ ((forall m : N, forall n : N, (Z.ge (Z_of_N m) (Z_of_N n)) = (N.ge m n)) /\ ((forall m : N, forall n : N, (Z.gt (Z_of_N m) (Z_of_N n)) = (N.gt m n)) /\ ((forall m : N, forall n : N, (Z.le (Z_of_N m) (Z_of_N n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (Z.lt (Z_of_N m) (Z_of_N n)) = (N.lt m n)) /\ ((forall m : N, forall n : N, (Z.max (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.max m n))) /\ ((forall m : N, forall n : N, (Z.min (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.min m n))) /\ ((forall m : N, forall n : N, (Z.add (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.add m n))) /\ ((forall m : N, forall n : N, (Z.mul (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.mul m n))) /\ (forall x : N, forall n : N, (Zpow (Z_of_N x) n) = (Z_of_N (N.pow x n))))))))))).
Axiom thm_INT_OF_NUM_EQ : forall m : N, forall n : N, ((Z_of_N m) = (Z_of_N n)) = (m = n).
Axiom thm_INT_OF_NUM_GE : forall m : N, forall n : N, (Z.ge (Z_of_N m) (Z_of_N n)) = (N.ge m n).
Axiom thm_INT_OF_NUM_GT : forall m : N, forall n : N, (Z.gt (Z_of_N m) (Z_of_N n)) = (N.gt m n).
Axiom thm_INT_OF_NUM_LE : forall m : N, forall n : N, (Z.le (Z_of_N m) (Z_of_N n)) = (N.le m n).
Axiom thm_INT_OF_NUM_LT : forall m : N, forall n : N, (Z.lt (Z_of_N m) (Z_of_N n)) = (N.lt m n).
Axiom thm_INT_OF_NUM_MAX : forall m : N, forall n : N, (Z.max (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.max m n)).
Axiom thm_INT_OF_NUM_MIN : forall m : N, forall n : N, (Z.min (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.min m n)).
Axiom thm_INT_OF_NUM_MOD : forall m : N, forall n : N, (Z_of_N (N.modulo m n)) = (Z.sub (Z_of_N m) (Z.mul (Z_of_N (N.div m n)) (Z_of_N n))).
Axiom thm_INT_OF_NUM_MUL : forall m : N, forall n : N, (Z.mul (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.mul m n)).
Axiom thm_INT_OF_NUM_POW : forall x : N, forall n : N, (Zpow (Z_of_N x) n) = (Z_of_N (N.pow x n)).
Axiom thm_INT_OF_NUM_SUB : forall m : N, forall n : N, (N.le m n) -> (Z.sub (Z_of_N n) (Z_of_N m)) = (Z_of_N (N.sub n m)).
Axiom thm_INT_OF_NUM_SUB_CASES : forall m : N, forall n : N, (Z.sub (Z_of_N m) (Z_of_N n)) = (@COND Z (N.le n m) (Z_of_N (N.sub m n)) (Z.opp (Z_of_N (N.sub n m)))).
Axiom thm_INT_OF_NUM_SUC : forall n : N, (Z.add (Z_of_N n) (Z_of_N ((BIT1 N0)))) = (Z_of_N (N.succ n)).
Axiom thm_INT_POS : forall n : N, Z.le (Z_of_N N0) (Z_of_N n).
Axiom thm_INT_POS_EQ_SQUARE : forall x : Z, (Z.le (Z_of_N N0) x) = (exists y : R, (Rpow y ((BIT0 (BIT1 N0)))) = (IZR x)).
Axiom thm_INT_POS_NZ : forall x : Z, (Z.lt (Z_of_N N0) x) -> ~ (x = (Z_of_N N0)).
Axiom thm_INT_POW2_ABS : forall x : Z, (Zpow (Z.abs x) ((BIT0 (BIT1 N0)))) = (Zpow x ((BIT0 (BIT1 N0)))).
Axiom thm_INT_POW_1 : forall x : Z, (Zpow x ((BIT1 N0))) = x.
Axiom thm_INT_POW_1_LE : forall n : N, forall x : Z, ((Z.le (Z_of_N N0) x) /\ (Z.le x (Z_of_N ((BIT1 N0))))) -> Z.le (Zpow x n) (Z_of_N ((BIT1 N0))).
Axiom thm_INT_POW_1_LT : forall n : N, forall x : Z, ((~ (n = N0)) /\ ((Z.le (Z_of_N N0) x) /\ (Z.lt x (Z_of_N ((BIT1 N0)))))) -> Z.lt (Zpow x n) (Z_of_N ((BIT1 N0))).
Axiom thm_INT_POW_2 : forall x : Z, (Zpow x ((BIT0 (BIT1 N0)))) = (Z.mul x x).
Axiom thm_INT_POW_ADD : forall x : Z, forall m : N, forall n : N, (Zpow x (N.add m n)) = (Z.mul (Zpow x m) (Zpow x n)).
Axiom thm_INT_POW_EQ : forall n : N, forall x : Z, forall y : Z, ((~ (n = N0)) /\ ((Z.le (Z_of_N N0) x) /\ ((Z.le (Z_of_N N0) y) /\ ((Zpow x n) = (Zpow y n))))) -> x = y.
Axiom thm_INT_POW_EQ_0 : forall x : Z, forall n : N, ((Zpow x n) = (Z_of_N N0)) = ((x = (Z_of_N N0)) /\ (~ (n = N0))).
Axiom thm_INT_POW_EQ_1 : forall x : Z, forall n : N, ((Zpow x n) = (Z_of_N ((BIT1 N0)))) = ((((Z.abs x) = (Z_of_N ((BIT1 N0)))) /\ ((Z.lt x (Z_of_N N0)) -> N.Even n)) \/ (n = N0)).
Axiom thm_INT_POW_EQ_1_IMP : forall x : Z, forall n : N, ((~ (n = N0)) /\ ((Zpow x n) = (Z_of_N ((BIT1 N0))))) -> (Z.abs x) = (Z_of_N ((BIT1 N0))).
Axiom thm_INT_POW_EQ_ABS : forall n : N, forall x : Z, forall y : Z, ((~ (n = N0)) /\ ((Zpow x n) = (Zpow y n))) -> (Z.abs x) = (Z.abs y).
Axiom thm_INT_POW_EQ_EQ : forall n : N, forall x : Z, forall y : Z, ((Zpow x n) = (Zpow y n)) = (@COND Prop (N.Even n) ((n = N0) \/ ((Z.abs x) = (Z.abs y))) (x = y)).
Axiom thm_INT_POW_EQ_ODD : forall n : N, forall x : Z, forall y : Z, ((N.Odd n) /\ ((Zpow x n) = (Zpow y n))) -> x = y.
Axiom thm_INT_POW_EQ_ODD_EQ : forall n : N, forall x : Z, forall y : Z, (N.Odd n) -> ((Zpow x n) = (Zpow y n)) = (x = y).
Axiom thm_INT_POW_LBOUND : forall x : Z, forall n : N, (Z.le (Z_of_N N0) x) -> Z.le (Z.add (Z_of_N ((BIT1 N0))) (Z.mul (Z_of_N n) x)) (Zpow (Z.add (Z_of_N ((BIT1 N0))) x) n).
Axiom thm_INT_POW_LE : forall x : Z, forall n : N, (Z.le (Z_of_N N0) x) -> Z.le (Z_of_N N0) (Zpow x n).
Axiom thm_INT_POW_LE2 : forall n : N, forall x : Z, forall y : Z, ((Z.le (Z_of_N N0) x) /\ (Z.le x y)) -> Z.le (Zpow x n) (Zpow y n).
Axiom thm_INT_POW_LE2_ODD : forall n : N, forall x : Z, forall y : Z, ((Z.le x y) /\ (N.Odd n)) -> Z.le (Zpow x n) (Zpow y n).
Axiom thm_INT_POW_LE2_ODD_EQ : forall n : N, forall x : Z, forall y : Z, (N.Odd n) -> (Z.le (Zpow x n) (Zpow y n)) = (Z.le x y).
Axiom thm_INT_POW_LE2_REV : forall n : N, forall x : Z, forall y : Z, ((~ (n = N0)) /\ ((Z.le (Z_of_N N0) y) /\ (Z.le (Zpow x n) (Zpow y n)))) -> Z.le x y.
Axiom thm_INT_POW_LE_1 : forall n : N, forall x : Z, (Z.le (Z_of_N ((BIT1 N0))) x) -> Z.le (Z_of_N ((BIT1 N0))) (Zpow x n).
Axiom thm_INT_POW_LT : forall x : Z, forall n : N, (Z.lt (Z_of_N N0) x) -> Z.lt (Z_of_N N0) (Zpow x n).
Axiom thm_INT_POW_LT2 : forall n : N, forall x : Z, forall y : Z, ((~ (n = N0)) /\ ((Z.le (Z_of_N N0) x) /\ (Z.lt x y))) -> Z.lt (Zpow x n) (Zpow y n).
Axiom thm_INT_POW_LT2_ODD : forall n : N, forall x : Z, forall y : Z, ((Z.lt x y) /\ (N.Odd n)) -> Z.lt (Zpow x n) (Zpow y n).
Axiom thm_INT_POW_LT2_ODD_EQ : forall n : N, forall x : Z, forall y : Z, (N.Odd n) -> (Z.lt (Zpow x n) (Zpow y n)) = (Z.lt x y).
Axiom thm_INT_POW_LT2_REV : forall n : N, forall x : Z, forall y : Z, ((Z.le (Z_of_N N0) y) /\ (Z.lt (Zpow x n) (Zpow y n))) -> Z.lt x y.
Axiom thm_INT_POW_LT_1 : forall n : N, forall x : Z, ((~ (n = N0)) /\ (Z.lt (Z_of_N ((BIT1 N0))) x)) -> Z.lt (Z_of_N ((BIT1 N0))) (Zpow x n).
Axiom thm_INT_POW_MONO : forall m : N, forall n : N, forall x : Z, ((Z.le (Z_of_N ((BIT1 N0))) x) /\ (N.le m n)) -> Z.le (Zpow x m) (Zpow x n).
Axiom thm_INT_POW_MONO_LT : forall m : N, forall n : N, forall x : Z, ((Z.lt (Z_of_N ((BIT1 N0))) x) /\ (N.lt m n)) -> Z.lt (Zpow x m) (Zpow x n).
Axiom thm_INT_POW_MUL : forall x : Z, forall y : Z, forall n : N, (Zpow (Z.mul x y) n) = (Z.mul (Zpow x n) (Zpow y n)).
Axiom thm_INT_POW_NEG : forall x : Z, forall n : N, (Zpow (Z.opp x) n) = (@COND Z (N.Even n) (Zpow x n) (Z.opp (Zpow x n))).
Axiom thm_INT_POW_NZ : forall x : Z, forall n : N, (~ (x = (Z_of_N N0))) -> ~ ((Zpow x n) = (Z_of_N N0)).
Axiom thm_INT_POW_ONE : forall n : N, (Zpow (Z_of_N ((BIT1 N0))) n) = (Z_of_N ((BIT1 N0))).
Axiom thm_INT_POW_POW : forall x : Z, forall m : N, forall n : N, (Zpow (Zpow x m) n) = (Zpow x (N.mul m n)).
Axiom thm_INT_POW_ZERO : forall n : N, (Zpow (Z_of_N N0) n) = (@COND Z (n = N0) (Z_of_N ((BIT1 N0))) (Z_of_N N0)).
Axiom thm_INT_RNEG_UNIQ : forall x : Z, forall y : Z, ((Z.add x y) = (Z_of_N N0)) = (y = (Z.opp x)).
Axiom thm_INT_SGN : forall x : Z, (Z.sgn x) = (@COND Z (Z.lt (Z_of_N N0) x) (Z_of_N ((BIT1 N0))) (@COND Z (Z.lt x (Z_of_N N0)) (Z.opp (Z_of_N ((BIT1 N0)))) (Z_of_N N0))).
Axiom thm_INT_SGNS_EQ : forall x : Z, forall y : Z, ((Z.sgn x) = (Z.sgn y)) = (((x = (Z_of_N N0)) = (y = (Z_of_N N0))) /\ (((Z.gt x (Z_of_N N0)) = (Z.gt y (Z_of_N N0))) /\ ((Z.lt x (Z_of_N N0)) = (Z.lt y (Z_of_N N0))))).
Axiom thm_INT_SGNS_EQ_ALT : forall x : Z, forall y : Z, ((Z.sgn x) = (Z.sgn y)) = (((x = (Z_of_N N0)) -> y = (Z_of_N N0)) /\ (((Z.gt x (Z_of_N N0)) -> Z.gt y (Z_of_N N0)) /\ ((Z.lt x (Z_of_N N0)) -> Z.lt y (Z_of_N N0)))).
Axiom thm_INT_SGN_0 : (Z.sgn (Z_of_N N0)) = (Z_of_N N0).
Axiom thm_INT_SGN_ABS : forall x : Z, (Z.mul (Z.sgn x) (Z.abs x)) = x.
Axiom thm_INT_SGN_ABS_ALT : forall x : Z, (Z.mul (Z.sgn x) x) = (Z.abs x).
Axiom thm_INT_SGN_CASES : forall x : Z, ((Z.sgn x) = (Z_of_N N0)) \/ (((Z.sgn x) = (Z_of_N ((BIT1 N0)))) \/ ((Z.sgn x) = (Z.opp (Z_of_N ((BIT1 N0)))))).
Axiom thm_INT_SGN_EQ : (forall x : Z, ((Z.sgn x) = (Z_of_N N0)) = (x = (Z_of_N N0))) /\ ((forall x : Z, ((Z.sgn x) = (Z_of_N ((BIT1 N0)))) = (Z.gt x (Z_of_N N0))) /\ (forall x : Z, ((Z.sgn x) = (Z.opp (Z_of_N ((BIT1 N0))))) = (Z.lt x (Z_of_N N0)))).
Axiom thm_INT_SGN_EQ_INEQ : forall x : Z, forall y : Z, ((Z.sgn x) = (Z.sgn y)) = ((x = y) \/ (Z.lt (Z.abs (Z.sub x y)) (Z.max (Z.abs x) (Z.abs y)))).
Axiom thm_INT_SGN_INEQS : (forall x : Z, (Z.le (Z_of_N N0) (Z.sgn x)) = (Z.le (Z_of_N N0) x)) /\ ((forall x : Z, (Z.lt (Z_of_N N0) (Z.sgn x)) = (Z.lt (Z_of_N N0) x)) /\ ((forall x : Z, (Z.ge (Z_of_N N0) (Z.sgn x)) = (Z.ge (Z_of_N N0) x)) /\ ((forall x : Z, (Z.gt (Z_of_N N0) (Z.sgn x)) = (Z.gt (Z_of_N N0) x)) /\ ((forall x : Z, ((Z_of_N N0) = (Z.sgn x)) = ((Z_of_N N0) = x)) /\ ((forall x : Z, (Z.le (Z.sgn x) (Z_of_N N0)) = (Z.le x (Z_of_N N0))) /\ ((forall x : Z, (Z.lt (Z.sgn x) (Z_of_N N0)) = (Z.lt x (Z_of_N N0))) /\ ((forall x : Z, (Z.ge (Z.sgn x) (Z_of_N N0)) = (Z.ge x (Z_of_N N0))) /\ ((forall x : Z, (Z.gt (Z.sgn x) (Z_of_N N0)) = (Z.gt x (Z_of_N N0))) /\ (forall x : Z, ((Z.sgn x) = (Z_of_N N0)) = (x = (Z_of_N N0))))))))))).
Axiom thm_INT_SGN_INT_SGN : forall x : Z, (Z.sgn (Z.sgn x)) = (Z.sgn x).
Axiom thm_INT_SGN_MUL : forall x : Z, forall y : Z, (Z.sgn (Z.mul x y)) = (Z.mul (Z.sgn x) (Z.sgn y)).
Axiom thm_INT_SGN_NEG : forall x : Z, (Z.sgn (Z.opp x)) = (Z.opp (Z.sgn x)).
Axiom thm_INT_SGN_POW : forall x : Z, forall n : N, (Z.sgn (Zpow x n)) = (Zpow (Z.sgn x) n).
Axiom thm_INT_SGN_POW_2 : forall x : Z, (Z.sgn (Zpow x ((BIT0 (BIT1 N0))))) = (Z.sgn (Z.abs x)).
Axiom thm_INT_SOS_EQ_0 : forall x : Z, forall y : Z, ((Z.add (Zpow x ((BIT0 (BIT1 N0)))) (Zpow y ((BIT0 (BIT1 N0))))) = (Z_of_N N0)) = ((x = (Z_of_N N0)) /\ (y = (Z_of_N N0))).
Axiom thm_INT_SUB_0 : forall x : Z, forall y : Z, ((Z.sub x y) = (Z_of_N N0)) = (x = y).
Axiom thm_INT_SUB_ABS : forall x : Z, forall y : Z, Z.le (Z.sub (Z.abs x) (Z.abs y)) (Z.abs (Z.sub x y)).
Axiom thm_INT_SUB_ADD : forall x : Z, forall y : Z, (Z.add (Z.sub x y) y) = x.
Axiom thm_INT_SUB_ADD2 : forall x : Z, forall y : Z, (Z.add y (Z.sub x y)) = x.
Axiom thm_INT_SUB_LDISTRIB : forall x : Z, forall y : Z, forall z : Z, (Z.mul x (Z.sub y z)) = (Z.sub (Z.mul x y) (Z.mul x z)).
Axiom thm_INT_SUB_LE : forall x : Z, forall y : Z, (Z.le (Z_of_N N0) (Z.sub x y)) = (Z.le y x).
Axiom thm_INT_SUB_LNEG : forall x : Z, forall y : Z, (Z.sub (Z.opp x) y) = (Z.opp (Z.add x y)).
Axiom thm_INT_SUB_LT : forall x : Z, forall y : Z, (Z.lt (Z_of_N N0) (Z.sub x y)) = (Z.lt y x).
Axiom thm_INT_SUB_LZERO : forall x : Z, (Z.sub (Z_of_N N0) x) = (Z.opp x).
Axiom thm_INT_SUB_NEG2 : forall x : Z, forall y : Z, (Z.sub (Z.opp x) (Z.opp y)) = (Z.sub y x).
Axiom thm_INT_SUB_RDISTRIB : forall x : Z, forall y : Z, forall z : Z, (Z.mul (Z.sub x y) z) = (Z.sub (Z.mul x z) (Z.mul y z)).
Axiom thm_INT_SUB_REFL : forall x : Z, (Z.sub x x) = (Z_of_N N0).
Axiom thm_INT_SUB_RNEG : forall x : Z, forall y : Z, (Z.sub x (Z.opp y)) = (Z.add x y).
Axiom thm_INT_SUB_RZERO : forall x : Z, (Z.sub x (Z_of_N N0)) = x.
Axiom thm_INT_SUB_SUB : forall x : Z, forall y : Z, (Z.sub (Z.sub x y) x) = (Z.opp y).
Axiom thm_INT_SUB_SUB2 : forall x : Z, forall y : Z, (Z.sub x (Z.sub x y)) = y.
Axiom thm_INT_SUB_TRIANGLE : forall a : Z, forall b : Z, forall c : Z, (Z.add (Z.sub a b) (Z.sub b c)) = (Z.sub a c).
Axiom thm_INT_WLOG_LE : forall (P : Z -> Z -> Prop), ((forall x : Z, forall y : Z, (P x y) = (P y x)) /\ (forall x : Z, forall y : Z, (Z.le x y) -> P x y)) -> forall x : Z, forall y : Z, P x y.
Axiom thm_INT_WLOG_LT : forall (P : Z -> Z -> Prop), ((forall x : Z, P x x) /\ ((forall x : Z, forall y : Z, (P x y) = (P y x)) /\ (forall x : Z, forall y : Z, (Z.lt x y) -> P x y))) -> forall x : Z, forall y : Z, P x y.
Axiom thm_INT_WLOG_LE_3 : forall P : Z -> Z -> Z -> Prop, ((forall x : Z, forall y : Z, forall z : Z, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : Z, forall y : Z, forall z : Z, ((Z.le x y) /\ (Z.le y z)) -> P x y z)) -> forall x : Z, forall y : Z, forall z : Z, P x y z.
Axiom thm_INT_FORALL_POS : forall P : Z -> Prop, (forall n : N, P (Z_of_N n)) = (forall i : Z, (Z.le (Z_of_N N0) i) -> P i).
Axiom thm_INT_EXISTS_POS : forall P : Z -> Prop, (exists n : N, P (Z_of_N n)) = (exists i : Z, (Z.le (Z_of_N N0) i) /\ (P i)).
Axiom thm_INT_FORALL_ABS : forall P : Z -> Prop, (forall n : N, P (Z_of_N n)) = (forall x : Z, P (Z.abs x)).
Axiom thm_INT_EXISTS_ABS : forall P : Z -> Prop, (exists n : N, P (Z_of_N n)) = (exists x : Z, P (Z.abs x)).
Axiom thm_INT_POW : forall (x : Z), ((Zpow x N0) = (Z_of_N ((BIT1 N0)))) /\ (forall n : N, (Zpow x (N.succ n)) = (Z.mul x (Zpow x n))).
Axiom thm_INT_ABS : forall x : Z, (Z.abs x) = (@COND Z (Z.le (Z_of_N N0) x) x (Z.opp x)).
Axiom thm_INT_GE : forall x : Z, forall y : Z, (Z.ge x y) = (Z.le y x).
Axiom thm_INT_GT : forall x : Z, forall y : Z, (Z.gt x y) = (Z.lt y x).
Axiom thm_INT_LT : forall x : Z, forall y : Z, (Z.lt x y) = (~ (Z.le y x)).
Axiom thm_INT_SUB : forall x : Z, forall y : Z, (Z.sub x y) = (Z.add x (Z.opp y)).
Axiom thm_INT_MAX : forall x : Z, forall y : Z, (Z.max x y) = (@COND Z (Z.le x y) y x).
Axiom thm_INT_MIN : forall x : Z, forall y : Z, (Z.min x y) = (@COND Z (Z.le x y) x y).
Axiom thm_INT_OF_NUM_EXISTS : forall x : Z, (exists n : N, x = (Z_of_N n)) = (Z.le (Z_of_N N0) x).
Axiom thm_INT_LE_DISCRETE : forall x : Z, forall y : Z, (Z.le x y) = (Z.lt x (Z.add y (Z_of_N ((BIT1 N0))))).
Axiom thm_INT_LE_TRANS_LE : forall x : Z, forall y : Z, (Z.le x y) = (forall z : Z, (Z.le y z) -> Z.le x z).
Axiom thm_INT_LE_TRANS_LT : forall x : Z, forall y : Z, (Z.le x y) = (forall z : Z, (Z.lt y z) -> Z.lt x z).
Axiom thm_INT_MUL_EQ_1 : forall x : Z, forall y : Z, ((Z.mul x y) = (Z_of_N ((BIT1 N0)))) = (((x = (Z_of_N ((BIT1 N0)))) /\ (y = (Z_of_N ((BIT1 N0))))) \/ ((x = (Z.opp (Z_of_N ((BIT1 N0))))) /\ (y = (Z.opp (Z_of_N ((BIT1 N0))))))).
Axiom thm_INT_ABS_MUL_1 : forall x : Z, forall y : Z, ((Z.abs (Z.mul x y)) = (Z_of_N ((BIT1 N0)))) = (((Z.abs x) = (Z_of_N ((BIT1 N0)))) /\ ((Z.abs y) = (Z_of_N ((BIT1 N0))))).
Axiom thm_INT_WOP : forall (P : Z -> Prop), (exists x : Z, (Z.le (Z_of_N N0) x) /\ (P x)) = (exists x : Z, (Z.le (Z_of_N N0) x) /\ ((P x) /\ (forall y : Z, ((Z.le (Z_of_N N0) y) /\ (P y)) -> Z.le x y))).
Axiom thm_INT_ARCH : forall x : Z, forall d : Z, (~ (d = (Z_of_N N0))) -> exists c : Z, Z.lt x (Z.mul c d).
Axiom thm_INT_DIVMOD_EXIST_0 : forall m : Z, forall n : Z, exists q : Z, exists r : Z, @COND Prop (n = (Z_of_N N0)) ((q = (Z_of_N N0)) /\ (r = m)) ((Z.le (Z_of_N N0) r) /\ ((Z.lt r (Z.abs n)) /\ (m = (Z.add (Z.mul q n) r)))).
Axiom thm_INT_DIVISION : forall m : Z, forall n : Z, (~ (n = (Z_of_N N0))) -> (m = (Z.add (Z.mul (Zdiv m n) n) (Zrem m n))) /\ ((Z.le (Z_of_N N0) (Zrem m n)) /\ (Z.lt (Zrem m n) (Z.abs n))).
Axiom thm_INT_DIVISION_SIMP : forall m : Z, forall n : Z, (Z.add (Z.mul (Zdiv m n) n) (Zrem m n)) = m.
Axiom thm_INT_REM_POS : forall a : Z, forall b : Z, (~ (b = (Z_of_N N0))) -> Z.le (Z_of_N N0) (Zrem a b).
Axiom thm_INT_DIV_0 : forall m : Z, (Zdiv m (Z_of_N N0)) = (Z_of_N N0).
Axiom thm_INT_REM_0 : forall m : Z, (Zrem m (Z_of_N N0)) = m.
Axiom thm_INT_REM_POS_EQ : forall m : Z, forall n : Z, (Z.le (Z_of_N N0) (Zrem m n)) = ((n = (Z_of_N N0)) -> Z.le (Z_of_N N0) m).
Axiom thm_INT_REM_DIV : forall m : Z, forall n : Z, (Zrem m n) = (Z.sub m (Z.mul (Zdiv m n) n)).
Axiom thm_INT_LT_REM : forall x : Z, forall n : Z, (Z.lt (Z_of_N N0) n) -> Z.lt (Zrem x n) n.
Axiom thm_INT_LT_REM_EQ : forall m : Z, forall n : Z, (Z.lt (Zrem m n) n) = ((Z.lt (Z_of_N N0) n) \/ ((n = (Z_of_N N0)) /\ (Z.lt m (Z_of_N N0)))).
Axiom thm_cong : forall {A : Type'}, forall rel : A -> A -> Prop, forall x : A, forall y : A, (@eq2 A x y rel) = (rel x y).
Axiom thm_real_mod : forall x : R, forall y : R, forall n : R, (Rmod_eq n x y) = (exists q : R, (integer q) /\ ((Rminus x y) = (Rmult q n))).
Axiom thm_int_divides : forall b : Z, forall a : Z, (Z.divide a b) = (exists x : Z, b = (Z.mul a x)).
Axiom thm_INT_DIVIDES_LE : forall x : Z, forall y : Z, (Z.divide x y) -> (Z.le (Z.abs x) (Z.abs y)) \/ (y = (Z_of_N N0)).
Axiom thm_int_mod : forall n : Z, forall x : Z, forall y : Z, (int_mod n x y) = (Z.divide n (Z.sub x y)).
Axiom thm_int_congruent : forall x : Z, forall y : Z, forall n : Z, (@eq2 Z x y (int_mod n)) = (exists d : Z, (Z.sub x y) = (Z.mul n d)).
Axiom thm_INT_CONG_IMP_EQ : forall x : Z, forall y : Z, forall n : Z, ((Z.lt (Z.abs (Z.sub x y)) n) /\ (@eq2 Z x y (int_mod n))) -> x = y.
Axiom thm_int_coprime : forall a : Z, forall b : Z, (int_coprime (@pair Z Z a b)) = (exists x : Z, exists y : Z, (Z.add (Z.mul a x) (Z.mul b y)) = (Z_of_N ((BIT1 N0)))).
Axiom thm_INT_DIVMOD_UNIQ : forall m : Z, forall n : Z, forall q : Z, forall r : Z, ((m = (Z.add (Z.mul q n) r)) /\ ((Z.le (Z_of_N N0) r) /\ (Z.lt r (Z.abs n)))) -> ((Zdiv m n) = q) /\ ((Zrem m n) = r).
Axiom thm_INT_DIV_UNIQ : forall m : Z, forall n : Z, forall q : Z, forall r : Z, ((m = (Z.add (Z.mul q n) r)) /\ ((Z.le (Z_of_N N0) r) /\ (Z.lt r (Z.abs n)))) -> (Zdiv m n) = q.
Axiom thm_INT_REM_UNIQ : forall m : Z, forall n : Z, forall q : Z, forall r : Z, ((m = (Z.add (Z.mul q n) r)) /\ ((Z.le (Z_of_N N0) r) /\ (Z.lt r (Z.abs n)))) -> (Zrem m n) = r.
Axiom thm_INT_REM_LT : forall m : Z, forall n : Z, (((~ (n = (Z_of_N N0))) -> Z.le (Z_of_N N0) m) /\ (Z.lt m n)) -> (Zrem m n) = m.
Axiom thm_INT_DIV_LT : forall m : Z, forall n : Z, (((~ (n = (Z_of_N N0))) -> Z.le (Z_of_N N0) m) /\ (Z.lt m n)) -> (Zdiv m n) = (Z_of_N N0).
Axiom thm_INT_REM_RNEG : forall m : Z, forall n : Z, (Zrem m (Z.opp n)) = (Zrem m n).
Axiom thm_INT_DIV_RNEG : forall m : Z, forall n : Z, (Zdiv m (Z.opp n)) = (Z.opp (Zdiv m n)).
Axiom thm_INT_REM_RABS : forall x : Z, forall y : Z, (Zrem x (Z.abs y)) = (Zrem x y).
Axiom thm_INT_REM_REM : forall m : Z, forall n : Z, (Zrem (Zrem m n) n) = (Zrem m n).
Axiom thm_INT_REM_EQ : forall m : Z, forall n : Z, forall p : Z, ((Zrem m p) = (Zrem n p)) = (@eq2 Z m n (int_mod p)).
Axiom thm_INT_REM_ZERO : forall n : Z, (Zrem (Z_of_N N0) n) = (Z_of_N N0).
Axiom thm_INT_DIV_ZERO : forall n : Z, (Zdiv (Z_of_N N0) n) = (Z_of_N N0).
Axiom thm_INT_REM_EQ_0 : forall m : Z, forall n : Z, ((Zrem m n) = (Z_of_N N0)) = (Z.divide n m).
Axiom thm_INT_MUL_DIV_EQ : (forall m : Z, forall n : Z, ((Z.mul n (Zdiv m n)) = m) = (Z.divide n m)) /\ (forall m : Z, forall n : Z, ((Z.mul (Zdiv m n) n) = m) = (Z.divide n m)).
Axiom thm_INT_CONG_LREM : forall x : Z, forall y : Z, forall n : Z, (@eq2 Z (Zrem x n) y (int_mod n)) = (@eq2 Z x y (int_mod n)).
Axiom thm_INT_CONG_RREM : forall x : Z, forall y : Z, forall n : Z, (@eq2 Z x (Zrem y n) (int_mod n)) = (@eq2 Z x y (int_mod n)).
Axiom thm_INT_REM_MOD_SELF : forall m : Z, forall n : Z, @eq2 Z (Zrem m n) m (int_mod n).
Axiom thm_INT_REM_REM_MUL : (forall m : Z, forall n : Z, forall p : Z, (Zrem (Zrem m (Z.mul n p)) n) = (Zrem m n)) /\ (forall m : Z, forall n : Z, forall p : Z, (Zrem (Zrem m (Z.mul n p)) p) = (Zrem m p)).
Axiom thm_INT_CONG_SOLVE_BOUNDS : forall a : Z, forall n : Z, (~ (n = (Z_of_N N0))) -> exists x : Z, (Z.le (Z_of_N N0) x) /\ ((Z.lt x (Z.abs n)) /\ (@eq2 Z x a (int_mod n))).
Axiom thm_INT_NEG_REM : forall n : Z, forall p : Z, (Zrem (Z.opp (Zrem n p)) p) = (Zrem (Z.opp n) p).
Axiom thm_INT_ADD_REM : forall m : Z, forall n : Z, forall p : Z, (Zrem (Z.add (Zrem m p) (Zrem n p)) p) = (Zrem (Z.add m n) p).
Axiom thm_INT_SUB_REM : forall m : Z, forall n : Z, forall p : Z, (Zrem (Z.sub (Zrem m p) (Zrem n p)) p) = (Zrem (Z.sub m n) p).
Axiom thm_INT_MUL_REM : forall m : Z, forall n : Z, forall p : Z, (Zrem (Z.mul (Zrem m p) (Zrem n p)) p) = (Zrem (Z.mul m n) p).
Axiom thm_INT_POW_REM : forall m : Z, forall n : N, forall p : Z, (Zrem (Zpow (Zrem m p) n) p) = (Zrem (Zpow m n) p).
Axiom thm_INT_OF_NUM_REM : forall m : N, forall n : N, (Zrem (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.modulo m n)).
Axiom thm_INT_OF_NUM_DIV : forall m : N, forall n : N, (Zdiv (Z_of_N m) (Z_of_N n)) = (Z_of_N (N.div m n)).
Axiom thm_INT_REM_REFL : forall n : Z, (Zrem n n) = (Z_of_N N0).
Axiom thm_INT_DIV_REFL : forall n : Z, (Zdiv n n) = (@COND Z (n = (Z_of_N N0)) (Z_of_N N0) (Z_of_N ((BIT1 N0)))).
Axiom thm_INT_REM_LNEG : forall m : Z, forall n : Z, (Zrem (Z.opp m) n) = (@COND Z ((Zrem m n) = (Z_of_N N0)) (Z_of_N N0) (Z.sub (Z.abs n) (Zrem m n))).
Axiom thm_INT_DIV_LNEG : forall m : Z, forall n : Z, (Zdiv (Z.opp m) n) = (@COND Z ((Zrem m n) = (Z_of_N N0)) (Z.opp (Zdiv m n)) (Z.sub (Z.opp (Zdiv m n)) (Z.sgn n))).
Axiom thm_INT_DIV_NEG2 : forall m : Z, forall n : Z, (Zdiv (Z.opp m) (Z.opp n)) = (@COND Z ((Zrem m n) = (Z_of_N N0)) (Zdiv m n) (Z.add (Zdiv m n) (Z.sgn n))).
Axiom thm_INT_REM_NEG2 : forall m : Z, forall n : Z, (Zrem (Z.opp m) (Z.opp n)) = (@COND Z ((Zrem m n) = (Z_of_N N0)) (Z_of_N N0) (Z.sub (Z.abs n) (Zrem m n))).
Axiom thm_INT_REM_1 : forall n : Z, (Zrem n (Z_of_N ((BIT1 N0)))) = (Z_of_N N0).
Axiom thm_INT_DIV_1 : forall n : Z, (Zdiv n (Z_of_N ((BIT1 N0)))) = n.
Axiom thm_INT_REM_MUL : (forall m : Z, forall n : Z, (Zrem (Z.mul m n) n) = (Z_of_N N0)) /\ (forall m : Z, forall n : Z, (Zrem (Z.mul m n) m) = (Z_of_N N0)).
Axiom thm_INT_DIV_MUL : (forall m : Z, forall n : Z, (~ (n = (Z_of_N N0))) -> (Zdiv (Z.mul m n) n) = m) /\ (forall m : Z, forall n : Z, (~ (m = (Z_of_N N0))) -> (Zdiv (Z.mul m n) m) = n).
Axiom thm_INT_DIV_LT_EQ : forall a : Z, forall b : Z, forall c : Z, (Z.lt (Z_of_N N0) a) -> (Z.lt (Zdiv b a) c) = (Z.lt b (Z.mul a c)).
Axiom thm_INT_LE_DIV_EQ : forall a : Z, forall b : Z, forall c : Z, (Z.lt (Z_of_N N0) a) -> (Z.le c (Zdiv b a)) = (Z.le (Z.mul a c) b).
Axiom thm_INT_DIV_LE_EQ : forall a : Z, forall b : Z, forall c : Z, (Z.lt (Z_of_N N0) a) -> (Z.le (Zdiv b a) c) = (Z.lt b (Z.mul a (Z.add c (Z_of_N ((BIT1 N0)))))).
Axiom thm_INT_LT_DIV_EQ : forall a : Z, forall b : Z, forall c : Z, (Z.lt (Z_of_N N0) a) -> (Z.lt c (Zdiv b a)) = (Z.le (Z.mul a (Z.add c (Z_of_N ((BIT1 N0))))) b).
Axiom thm_INT_DIV_LE : forall m : Z, forall n : Z, Z.le (Z.abs (Zdiv m n)) (Z.abs m).
Axiom thm_INT_REM_MUL_REM : forall m : Z, forall n : Z, forall p : Z, (Z.le (Z_of_N N0) n) -> (Zrem m (Z.mul n p)) = (Z.add (Z.mul n (Zrem (Zdiv m n) p)) (Zrem m n)).
Axiom thm_INT_DIV_DIV : forall m : Z, forall n : Z, forall p : Z, (Z.le (Z_of_N N0) n) -> (Zdiv (Zdiv m n) p) = (Zdiv m (Z.mul n p)).
Axiom thm_INT_DIV_EQ_0 : forall m : Z, forall n : Z, ((Zdiv m n) = (Z_of_N N0)) = ((n = (Z_of_N N0)) \/ ((Z.le (Z_of_N N0) m) /\ (Z.lt m (Z.abs n)))).
Axiom thm_INT_REM_EQ_SELF : forall m : Z, forall n : Z, ((Zrem m n) = m) = ((n = (Z_of_N N0)) \/ ((Z.le (Z_of_N N0) m) /\ (Z.lt m (Z.abs n)))).
Axiom thm_INT_REM_UNIQUE : forall m : Z, forall n : Z, forall p : Z, ((Zrem m n) = p) = ((((n = (Z_of_N N0)) /\ (m = p)) \/ ((Z.le (Z_of_N N0) p) /\ (Z.lt p (Z.abs n)))) /\ (@eq2 Z m p (int_mod n))).
Axiom thm_INT_DIV_REM : forall m : Z, forall n : Z, forall p : Z, (Z.le (Z_of_N N0) n) -> (Zrem (Zdiv m n) p) = (Zdiv (Zrem m (Z.mul n p)) n).
Axiom thm_INT_REM_REM_LE : forall m : Z, forall n : Z, forall p : Z, ((~ (n = (Z_of_N N0))) /\ (Z.le (Z.abs n) (Z.abs p))) -> (Zrem (Zrem m n) p) = (Zrem m n).
Axiom thm_INT_LE_DIV : forall m : Z, forall n : Z, ((Z.le (Z_of_N N0) m) /\ (Z.le (Z_of_N N0) n)) -> Z.le (Z_of_N N0) (Zdiv m n).
Axiom thm_INT_LT_DIV : forall m : Z, forall n : Z, ((Z.lt (Z_of_N N0) n) /\ (Z.le n m)) -> Z.lt (Z_of_N N0) (Zdiv m n).
Axiom thm_INT_REM_LE_EQ : forall m : Z, forall n : Z, (Z.le (Zrem m n) m) = ((n = (Z_of_N N0)) \/ (Z.le (Z_of_N N0) m)).
Axiom thm_INT_REM_LE : forall m : Z, forall n : Z, forall p : Z, (((n = (Z_of_N N0)) \/ (Z.le (Z_of_N N0) m)) /\ (Z.le m p)) -> Z.le (Zrem m n) p.
Axiom thm_INT_REM_MUL_ADD : (forall m : Z, forall n : Z, forall p : Z, (Zrem (Z.add (Z.mul m n) p) n) = (Zrem p n)) /\ ((forall m : Z, forall n : Z, forall p : Z, (Zrem (Z.add (Z.mul n m) p) n) = (Zrem p n)) /\ ((forall m : Z, forall n : Z, forall p : Z, (Zrem (Z.add p (Z.mul m n)) n) = (Zrem p n)) /\ (forall m : Z, forall n : Z, forall p : Z, (Zrem (Z.add p (Z.mul n m)) n) = (Zrem p n)))).
Axiom thm_INT_DIV_MUL_ADD : (forall m : Z, forall n : Z, forall p : Z, (~ (n = (Z_of_N N0))) -> (Zdiv (Z.add (Z.mul m n) p) n) = (Z.add m (Zdiv p n))) /\ ((forall m : Z, forall n : Z, forall p : Z, (~ (n = (Z_of_N N0))) -> (Zdiv (Z.add (Z.mul n m) p) n) = (Z.add m (Zdiv p n))) /\ ((forall m : Z, forall n : Z, forall p : Z, (~ (n = (Z_of_N N0))) -> (Zdiv (Z.add p (Z.mul m n)) n) = (Z.add (Zdiv p n) m)) /\ (forall m : Z, forall n : Z, forall p : Z, (~ (n = (Z_of_N N0))) -> (Zdiv (Z.add p (Z.mul n m)) n) = (Z.add (Zdiv p n) m)))).
Axiom thm_INT_CONG_DIV2 : forall a : Z, forall b : Z, forall m : Z, forall n : Z, (@eq2 Z a b (int_mod (Z.mul m n))) -> @eq2 Z (Zdiv a m) (Zdiv b m) (int_mod n).
Axiom thm_INT_REM_2_CASES : forall n : Z, ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N N0)) \/ ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N ((BIT1 N0)))).
Axiom thm_NOT_INT_REM_2 : (forall n : Z, (~ ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N N0))) = ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N ((BIT1 N0))))) /\ (forall n : Z, (~ ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N ((BIT1 N0))))) = ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N N0))).
Axiom thm_INT_REM_2_DIVIDES : (forall n : Z, ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N N0)) = (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) n)) /\ (forall n : Z, ((Zrem n (Z_of_N ((BIT0 (BIT1 N0))))) = (Z_of_N ((BIT1 N0)))) = (~ (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) n))).
Axiom thm_INT_REM_2_EXPAND : forall x : Z, (Zrem x (Z_of_N ((BIT0 (BIT1 N0))))) = (@COND Z (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) x) (Z_of_N N0) (Z_of_N ((BIT1 N0)))).
Axiom thm_INT_REM_2_NEG : forall x : Z, (Zrem (Z.opp x) (Z_of_N ((BIT0 (BIT1 N0))))) = (Zrem x (Z_of_N ((BIT0 (BIT1 N0))))).
Axiom thm_INT_DIVIDES_DIV_SELF : forall n : Z, forall d : Z, (Z.divide d n) -> Z.divide (Zdiv n d) n.
Axiom thm_INT_DIV_BY_DIV : forall m : Z, forall n : Z, ((~ (n = (Z_of_N N0))) /\ (Z.divide m n)) -> (Zdiv n (Zdiv n m)) = m.
Axiom thm_INT_DIVIDES_DIV_DIVIDES : forall n : Z, forall d : Z, forall e : Z, ((Z.divide d n) /\ ((n = (Z_of_N N0)) -> e = (Z_of_N N0))) -> (Z.divide (Zdiv n d) e) = (Z.divide n (Z.mul d e)).
Axiom thm_INT_DIVIDES_DIVIDES_DIV : forall n : Z, forall d : Z, forall e : Z, (Z.divide d n) -> (Z.divide e (Zdiv n d)) = (Z.divide (Z.mul d e) n).
Axiom thm_INT_DIVIDES_DIVIDES_DIV_EQ : forall n : Z, forall d : Z, forall e : Z, ((Z.divide d n) /\ (Z.divide e (Zdiv n d))) = (Z.divide (Z.mul d e) n).
Axiom thm_INT_2_DIVIDES_ADD : forall m : Z, forall n : Z, (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) (Z.add m n)) = ((Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) m) = (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) n)).
Axiom thm_INT_2_DIVIDES_SUB : forall m : Z, forall n : Z, (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) (Z.sub m n)) = ((Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) m) = (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) n)).
Axiom thm_INT_2_DIVIDES_MUL : forall m : Z, forall n : Z, (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) (Z.mul m n)) = ((Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) m) \/ (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) n)).
Axiom thm_INT_2_DIVIDES_POW : forall n : Z, forall k : N, (Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) (Zpow n k)) = ((Z.divide (Z_of_N ((BIT0 (BIT1 N0)))) n) /\ (~ (k = N0))).
Axiom thm_WF_INT_MEASURE : forall {A : Type'}, forall P : A -> Prop, forall m : A -> Z, ((forall x : A, Z.le (Z_of_N N0) (m x)) /\ (forall x : A, (forall y : A, (Z.lt (m y) (m x)) -> P y) -> P x)) -> forall x : A, P x.
Axiom thm_WF_INT_MEASURE_2 : forall {A B : Type'}, forall P : A -> B -> Prop, forall m : A -> B -> Z, ((forall x : A, forall y : B, Z.le (Z_of_N N0) (m x y)) /\ (forall x : A, forall y : B, (forall x' : A, forall y' : B, (Z.lt (m x' y') (m x y)) -> P x' y') -> P x y)) -> forall x : A, forall y : B, P x y.
Axiom thm_INT_GCD_EXISTS : forall a : Z, forall b : Z, exists d : Z, (Z.divide d a) /\ ((Z.divide d b) /\ (exists x : Z, exists y : Z, d = (Z.add (Z.mul a x) (Z.mul b y)))).
Axiom thm_INT_GCD_EXISTS_POS : forall a : Z, forall b : Z, exists d : Z, (Z.le (Z_of_N N0) d) /\ ((Z.divide d a) /\ ((Z.divide d b) /\ (exists x : Z, exists y : Z, d = (Z.add (Z.mul a x) (Z.mul b y))))).
Axiom thm_int_lcm : forall m : Z, forall n : Z, (int_lcm (@pair Z Z m n)) = (@COND Z ((Z.mul m n) = (Z_of_N N0)) (Z_of_N N0) (Zdiv (Z.abs (Z.mul m n)) (int_gcd (@pair Z Z m n)))).
Axiom thm_INT_DIVIDES_LABS : forall d : Z, forall n : Z, (Z.divide (Z.abs d) n) = (Z.divide d n).
Axiom thm_INT_DIVIDES_RABS : forall d : Z, forall n : Z, (Z.divide d (Z.abs n)) = (Z.divide d n).
Axiom thm_INT_DIVIDES_ABS : (forall d : Z, forall n : Z, (Z.divide (Z.abs d) n) = (Z.divide d n)) /\ (forall d : Z, forall n : Z, (Z.divide d (Z.abs n)) = (Z.divide d n)).
Axiom thm_INT_LCM_POS : forall m : Z, forall n : Z, Z.le (Z_of_N N0) (int_lcm (@pair Z Z m n)).
Axiom thm_INT_MUL_GCD_LCM : forall m : Z, forall n : Z, (Z.mul (int_gcd (@pair Z Z m n)) (int_lcm (@pair Z Z m n))) = (Z.abs (Z.mul m n)).
Axiom thm_INT_MUL_LCM_GCD : forall m : Z, forall n : Z, (Z.mul (int_lcm (@pair Z Z m n)) (int_gcd (@pair Z Z m n))) = (Z.abs (Z.mul m n)).
Axiom thm_INT_DIVIDES_LCM_GCD : forall m : Z, forall n : Z, forall d : Z, (Z.divide d (int_lcm (@pair Z Z m n))) = (Z.divide (Z.mul d (int_gcd (@pair Z Z m n))) (Z.mul m n)).
Axiom thm_INT_LCM_DIVIDES : forall m : Z, forall n : Z, forall d : Z, (Z.divide (int_lcm (@pair Z Z m n)) d) = ((Z.divide m d) /\ (Z.divide n d)).
Axiom thm_INT_LCM : forall m : Z, forall n : Z, (Z.divide m (int_lcm (@pair Z Z m n))) /\ ((Z.divide n (int_lcm (@pair Z Z m n))) /\ (forall d : Z, ((Z.divide m d) /\ (Z.divide n d)) -> Z.divide (int_lcm (@pair Z Z m n)) d)).
Axiom thm_num_of_int : forall x : Z, (num_of_int x) = (@ε N (fun n : N => (Z_of_N n) = x)).
Axiom thm_NUM_OF_INT_OF_NUM : forall n : N, (num_of_int (Z_of_N n)) = n.
Axiom thm_INT_OF_NUM_OF_INT : forall x : Z, (Z.le (Z_of_N N0) x) -> (Z_of_N (num_of_int x)) = x.
Axiom thm_NUM_OF_INT : forall x : Z, (Z.le (Z_of_N N0) x) = ((Z_of_N (num_of_int x)) = x).
Axiom thm_NUM_OF_INT_ADD : forall x : Z, forall y : Z, ((Z.le (Z_of_N N0) x) /\ (Z.le (Z_of_N N0) y)) -> (num_of_int (Z.add x y)) = (N.add (num_of_int x) (num_of_int y)).
Axiom thm_NUM_OF_INT_MUL : forall x : Z, forall y : Z, ((Z.le (Z_of_N N0) x) /\ (Z.le (Z_of_N N0) y)) -> (num_of_int (Z.mul x y)) = (N.mul (num_of_int x) (num_of_int y)).
Axiom thm_NUM_OF_INT_POW : forall x : Z, forall n : N, (Z.le (Z_of_N N0) x) -> (num_of_int (Zpow x n)) = (N.pow (num_of_int x) n).
Axiom thm_num_divides : forall a : N, forall b : N, (num_divides a b) = (Z.divide (Z_of_N a) (Z_of_N b)).
Axiom thm_num_mod : forall n : N, forall x : N, forall y : N, (num_mod n x y) = (int_mod (Z_of_N n) (Z_of_N x) (Z_of_N y)).
Axiom thm_num_congruent : forall x : N, forall y : N, forall n : N, (@eq2 N x y (num_mod n)) = (@eq2 Z (Z_of_N x) (Z_of_N y) (int_mod (Z_of_N n))).
Axiom thm_num_coprime : forall a : N, forall b : N, (num_coprime (@pair N N a b)) = (int_coprime (@pair Z Z (Z_of_N a) (Z_of_N b))).
Axiom thm_num_gcd : forall a : N, forall b : N, (num_gcd (@pair N N a b)) = (num_of_int (int_gcd (@pair Z Z (Z_of_N a) (Z_of_N b)))).
Axiom thm_num_lcm : forall a : N, forall b : N, (num_lcm (@pair N N a b)) = (num_of_int (int_lcm (@pair Z Z (Z_of_N a) (Z_of_N b)))).
Axiom thm_BINARY_INDUCT : forall P : N -> Prop, ((P N0) /\ (forall n : N, (P n) -> (P (N.mul ((BIT0 (BIT1 N0))) n)) /\ (P (N.add (N.mul ((BIT0 (BIT1 N0))) n) ((BIT1 N0)))))) -> forall n : N, P n.
Axiom thm_NUM_CASES_BINARY : forall P : N -> Prop, (forall n : N, P n) = ((forall n : N, P (N.mul ((BIT0 (BIT1 N0))) n)) /\ (forall n : N, P (N.add (N.mul ((BIT0 (BIT1 N0))) n) ((BIT1 N0))))).
Axiom thm_num_WF_DOWN : forall P : N -> Prop, forall m : N, ((forall n : N, (N.le m n) -> P n) /\ (forall n : N, ((N.lt n m) /\ (forall p : N, (N.lt n p) -> P p)) -> P n)) -> forall n : N, P n.
Axiom thm_INT_REM_REM_POW_MIN : forall x : Z, forall p : Z, forall m : N, forall n : N, (Zrem (Zrem x (Zpow p m)) (Zpow p n)) = (Zrem x (Zpow p (N.min m n))).
Axiom thm_NUM_GCD : forall a : N, forall b : N, (Z_of_N (num_gcd (@pair N N a b))) = (int_gcd (@pair Z Z (Z_of_N a) (Z_of_N b))).
Axiom thm_NUM_LCM : forall a : N, forall b : N, (Z_of_N (num_lcm (@pair N N a b))) = (int_lcm (@pair Z Z (Z_of_N a) (Z_of_N b))).
Axiom thm_CONG : forall x : N, forall y : N, forall n : N, (@eq2 N x y (num_mod n)) = ((N.modulo x n) = (N.modulo y n)).
Axiom thm_CONG_LMOD : forall x : N, forall y : N, forall n : N, (@eq2 N (N.modulo x n) y (num_mod n)) = (@eq2 N x y (num_mod n)).
Axiom thm_CONG_RMOD : forall x : N, forall y : N, forall n : N, (@eq2 N x (N.modulo y n) (num_mod n)) = (@eq2 N x y (num_mod n)).
Axiom thm_CONG_DIV2 : forall a : N, forall b : N, forall m : N, forall n : N, (@eq2 N a b (num_mod (N.mul m n))) -> @eq2 N (N.div a m) (N.div b m) (num_mod n).
Axiom thm_divides : forall (b : N) (a : N), (num_divides a b) = (exists x : N, b = (N.mul a x)).
Axiom thm_DIVIDES_LE : forall m : N, forall n : N, (num_divides m n) -> (N.le m n) \/ (n = N0).
Axiom thm_DIVIDES_LE_STRONG : forall m : N, forall n : N, (num_divides m n) -> ((N.le ((BIT1 N0)) m) /\ (N.le m n)) \/ (n = N0).
Axiom thm_DIVIDES_LE_IMP : forall m : N, forall n : N, ((num_divides m n) /\ ((n = N0) -> m = N0)) -> N.le m n.
Axiom thm_PROPERLY_DIVIDES_LE_IMP : forall m : N, forall n : N, ((num_divides m n) /\ ((~ (n = N0)) /\ (~ (m = n)))) -> N.le (N.mul ((BIT0 (BIT1 N0))) m) n.
Axiom thm_DIVIDES_ANTISYM : forall m : N, forall n : N, ((num_divides m n) /\ (num_divides n m)) = (m = n).
Axiom thm_DIVIDES_ONE : forall n : N, (num_divides n ((BIT1 N0))) = (n = ((BIT1 N0))).
Axiom thm_DIV_ADD : forall d : N, forall a : N, forall b : N, ((num_divides d a) \/ (num_divides d b)) -> (N.div (N.add a b) d) = (N.add (N.div a d) (N.div b d)).
Axiom thm_DIVIDES_MOD : forall m : N, forall n : N, (num_divides m n) = ((N.modulo n m) = N0).
Axiom thm_DIVIDES_DIV_MULT : forall m : N, forall n : N, (num_divides m n) = ((N.mul (N.div n m) m) = n).
Axiom thm_DIV_BY_DIV : forall m : N, forall n : N, ((~ (n = N0)) /\ (num_divides m n)) -> (N.div n (N.div n m)) = m.
Axiom thm_DIVIDES_DIV_DIVIDES : forall n : N, forall d : N, forall e : N, ((num_divides d n) /\ ((n = N0) -> e = N0)) -> (num_divides (N.div n d) e) = (num_divides n (N.mul d e)).
Axiom thm_DIVIDES_DIV_SELF : forall n : N, forall d : N, (num_divides d n) -> num_divides (N.div n d) n.
Axiom thm_DIVIDES_DIVIDES_DIV : forall n : N, forall d : N, forall e : N, (num_divides d n) -> (num_divides e (N.div n d)) = (num_divides (N.mul d e) n).
Axiom thm_DIVIDES_DIVIDES_DIV_EQ : forall n : N, forall d : N, forall e : N, ((num_divides d n) /\ (num_divides e (N.div n d))) = (num_divides (N.mul d e) n).
Axiom thm_DIVIDES_DIVIDES_DIV_IMP : forall n : N, forall d : N, forall e : N, (num_divides (N.mul d e) n) -> num_divides e (N.div n d).
Axiom thm_MULT_DIV : (forall m : N, forall n : N, forall p : N, (num_divides p m) -> (N.div (N.mul m n) p) = (N.mul (N.div m p) n)) /\ (forall m : N, forall n : N, forall p : N, (num_divides p n) -> (N.div (N.mul m n) p) = (N.mul m (N.div n p))).
Axiom thm_COPRIME_LMOD : forall a : N, forall n : N, (num_coprime (@pair N N (N.modulo a n) n)) = (num_coprime (@pair N N a n)).
Axiom thm_COPRIME_RMOD : forall a : N, forall n : N, (num_coprime (@pair N N n (N.modulo a n))) = (num_coprime (@pair N N n a)).
Axiom thm_INT_CONG_NUM_EXISTS : forall x : Z, forall y : Z, ((y = (Z_of_N N0)) -> Z.le (Z_of_N N0) x) -> exists n : N, @eq2 Z (Z_of_N n) x (int_mod y).
Axiom thm_GCD : forall a : N, forall b : N, ((num_divides (num_gcd (@pair N N a b)) a) /\ (num_divides (num_gcd (@pair N N a b)) b)) /\ (forall e : N, ((num_divides e a) /\ (num_divides e b)) -> num_divides e (num_gcd (@pair N N a b))).
Axiom thm_coprime : forall (a : N) (b : N), (num_coprime (@pair N N a b)) = (forall d : N, ((num_divides d a) /\ (num_divides d b)) -> d = ((BIT1 N0))).
Axiom thm_prime : forall p : N, (prime p) = ((~ (p = ((BIT1 N0)))) /\ (forall x : N, (num_divides x p) -> (x = ((BIT1 N0))) \/ (x = p))).
Axiom thm_ONE_OR_PRIME : forall p : N, ((p = ((BIT1 N0))) \/ (prime p)) = (forall n : N, (num_divides n p) -> (n = ((BIT1 N0))) \/ (n = p)).
Axiom thm_ONE_OR_PRIME_DIVIDES_OR_COPRIME : forall p : N, ((p = ((BIT1 N0))) \/ (prime p)) = (forall n : N, (num_divides p n) \/ (num_coprime (@pair N N p n))).
Axiom thm_PRIME_COPRIME_EQ_NONDIVISIBLE : forall p : N, (prime p) = (forall n : N, (num_coprime (@pair N N p n)) = (~ (num_divides p n))).
Axiom thm_ZERO_ONE_OR_PRIME_DIVPROD : forall p : N, forall a : N, forall b : N, ((p = N0) \/ ((p = ((BIT1 N0))) \/ (prime p))) -> (num_divides p (N.mul a b)) = ((num_divides p a) \/ (num_divides p b)).
Axiom thm_ZERO_ONE_OR_PRIME : forall p : N, ((p = N0) \/ ((p = ((BIT1 N0))) \/ (prime p))) = (forall a : N, forall b : N, (num_divides p (N.mul a b)) -> (num_divides p a) \/ (num_divides p b)).
Axiom thm_real_zpow : forall z : R, forall i : Z, (real_zpow z i) = (@COND R (Z.le (Z_of_N N0) i) (Rpow z (num_of_int i)) (Rinv (Rpow z (num_of_int (Z.opp i))))).
Axiom thm_REAL_POW_ZPOW : forall x : R, forall n : N, (Rpow x n) = (real_zpow x (Z_of_N n)).
Axiom thm_REAL_ZPOW_NUM : forall x : R, forall n : N, (real_zpow x (Z_of_N n)) = (Rpow x n).
Axiom thm_REAL_ZPOW_0 : forall x : R, (real_zpow x (Z_of_N N0)) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_ZPOW_1 : forall x : R, (real_zpow x (Z_of_N ((BIT1 N0)))) = x.
Axiom thm_REAL_ZPOW_2 : forall x : R, (real_zpow x (Z_of_N ((BIT0 (BIT1 N0))))) = (Rmult x x).
Axiom thm_REAL_ZPOW_ONE : forall n : Z, (real_zpow (R_of_N ((BIT1 N0))) n) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_ZPOW_NEG : forall x : R, forall n : Z, (real_zpow x (Z.opp n)) = (Rinv (real_zpow x n)).
Axiom thm_REAL_ZPOW_MINUS1 : forall x : R, (real_zpow x (Z.opp (Z_of_N ((BIT1 N0))))) = (Rinv x).
Axiom thm_REAL_ZPOW_ZERO : forall n : Z, (real_zpow (R_of_N N0) n) = (@COND R (n = (Z_of_N N0)) (R_of_N ((BIT1 N0))) (R_of_N N0)).
Axiom thm_REAL_ZPOW_POW : (forall x : R, forall n : N, (real_zpow x (Z_of_N n)) = (Rpow x n)) /\ (forall x : R, forall n : N, (real_zpow x (Z.opp (Z_of_N n))) = (Rinv (Rpow x n))).
Axiom thm_REAL_INV_ZPOW : forall x : R, forall n : Z, (Rinv (real_zpow x n)) = (real_zpow (Rinv x) n).
Axiom thm_REAL_ZPOW_INV : forall x : R, forall n : Z, (real_zpow (Rinv x) n) = (Rinv (real_zpow x n)).
Axiom thm_REAL_ZPOW_ZPOW : forall x : R, forall m : Z, forall n : Z, (real_zpow (real_zpow x m) n) = (real_zpow x (Z.mul m n)).
Axiom thm_REAL_ZPOW_MUL : forall x : R, forall y : R, forall n : Z, (real_zpow (Rmult x y) n) = (Rmult (real_zpow x n) (real_zpow y n)).
Axiom thm_REAL_ZPOW_DIV : forall x : R, forall y : R, forall n : Z, (real_zpow (Rdiv x y) n) = (Rdiv (real_zpow x n) (real_zpow y n)).
Axiom thm_REAL_ZPOW_ADD : forall x : R, forall m : Z, forall n : Z, (~ (x = (R_of_N N0))) -> (real_zpow x (Z.add m n)) = (Rmult (real_zpow x m) (real_zpow x n)).
Axiom thm_REAL_ZPOW_SUB : forall x : R, forall m : Z, forall n : Z, (~ (x = (R_of_N N0))) -> (real_zpow x (Z.sub m n)) = (Rdiv (real_zpow x m) (real_zpow x n)).
Axiom thm_REAL_ZPOW_LE : forall x : R, forall n : Z, (Rle (R_of_N N0) x) -> Rle (R_of_N N0) (real_zpow x n).
Axiom thm_REAL_ZPOW_LT : forall x : R, forall n : Z, (Rlt (R_of_N N0) x) -> Rlt (R_of_N N0) (real_zpow x n).
Axiom thm_REAL_ZPOW_EQ_0 : forall x : R, forall n : Z, ((real_zpow x n) = (R_of_N N0)) = ((x = (R_of_N N0)) /\ (~ (n = (Z_of_N N0)))).
Axiom thm_REAL_ABS_ZPOW : forall x : R, forall n : Z, (Rabs (real_zpow x n)) = (real_zpow (Rabs x) n).
Axiom thm_REAL_SGN_ZPOW : forall x : R, forall n : Z, (Rsgn (real_zpow x n)) = (real_zpow (Rsgn x) n).
Axiom thm_IN : forall {A : Type'}, forall P : A -> Prop, forall x : A, (@IN A x P) = (P x).
Axiom thm_EXTENSION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (s = t) = (forall x : A, (@IN A x s) = (@IN A x t)).
Axiom thm_GSPEC : forall {A : Type'}, forall p : A -> Prop, (@GSPEC A p) = p.
Axiom thm_SETSPEC : forall {A : Type'}, forall P : Prop, forall v : A, forall t : A, (@SETSPEC A v P t) = (P /\ (v = t)).
Axiom thm_IN_ELIM_THM : forall {A : Type'}, (forall P : (Prop -> A -> Prop) -> Prop, forall x : A, (@IN A x (@GSPEC A (fun v : A => P (@SETSPEC A v)))) = (P (fun p : Prop => fun t : A => p /\ (x = t)))) /\ ((forall p : A -> Prop, forall x : A, (@IN A x (@GSPEC A (fun v : A => exists y : A, @SETSPEC A v (p y) y))) = (p x)) /\ ((forall P : (Prop -> A -> Prop) -> Prop, forall x : A, (@GSPEC A (fun v : A => P (@SETSPEC A v)) x) = (P (fun p : Prop => fun t : A => p /\ (x = t)))) /\ ((forall p : A -> Prop, forall x : A, (@GSPEC A (fun v : A => exists y : A, @SETSPEC A v (p y) y) x) = (p x)) /\ (forall p : A -> Prop, forall x : A, (@IN A x (fun y : A => p y)) = (p x))))).
Axiom thm_EMPTY : forall {A : Type'}, (@set0 A) = (fun x : A => False).
Axiom thm_INSERT_DEF : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@INSERT A x s) = (fun y : A => (@IN A y s) \/ (y = x)).
Axiom thm_UNIV : forall {A : Type'}, (@setT A) = (fun x : A => True).
Axiom thm_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setU A s t) = (@GSPEC A (fun GEN_PVAR_0 : A => exists x : A, @SETSPEC A GEN_PVAR_0 ((@IN A x s) \/ (@IN A x t)) x)).
Axiom thm_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A s) = (@GSPEC A (fun GEN_PVAR_1 : A => exists x : A, @SETSPEC A GEN_PVAR_1 (exists u : A -> Prop, (@IN (A -> Prop) u s) /\ (@IN A x u)) x)).
Axiom thm_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setI A s t) = (@GSPEC A (fun GEN_PVAR_2 : A => exists x : A, @SETSPEC A GEN_PVAR_2 ((@IN A x s) /\ (@IN A x t)) x)).
Axiom thm_INTERS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@INTERS A s) = (@GSPEC A (fun GEN_PVAR_3 : A => exists x : A, @SETSPEC A GEN_PVAR_3 (forall u : A -> Prop, (@IN (A -> Prop) u s) -> @IN A x u) x)).
Axiom thm_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setD A s t) = (@GSPEC A (fun GEN_PVAR_4 : A => exists x : A, @SETSPEC A GEN_PVAR_4 ((@IN A x s) /\ (~ (@IN A x t))) x)).
Axiom thm_INSERT : forall {A : Type'} (s : A -> Prop) (x : A), (@INSERT A x s) = (@GSPEC A (fun GEN_PVAR_5 : A => exists y : A, @SETSPEC A GEN_PVAR_5 ((@IN A y s) \/ (y = x)) y)).
Axiom thm_DELETE : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@DELETE A s x) = (@GSPEC A (fun GEN_PVAR_6 : A => exists y : A, @SETSPEC A GEN_PVAR_6 ((@IN A y s) /\ (~ (y = x))) y)).
Axiom thm_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) = (forall x : A, (@IN A x s) -> @IN A x t).
Axiom thm_PSUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@proper A s t) = ((@subset A s t) /\ (~ (s = t))).
Axiom thm_DISJOINT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A s t) = ((@setI A s t) = (@set0 A)).
Axiom thm_SING : forall {A : Type'}, forall s : A -> Prop, (@is_set1 A s) = (exists x : A, s = (@INSERT A x (@set0 A))).
Axiom thm_FINITE_RULES : forall {A : Type'}, (@finite_set A (@set0 A)) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> @finite_set A (@INSERT A x s)).
Axiom thm_FINITE_CASES : forall {A : Type'}, forall a : A -> Prop, (@finite_set A a) = ((a = (@set0 A)) \/ (exists x : A, exists s : A -> Prop, (a = (@INSERT A x s)) /\ (@finite_set A s))).
Axiom thm_FINITE_INDUCT : forall {A : Type'}, forall FINITE' : (A -> Prop) -> Prop, ((FINITE' (@set0 A)) /\ (forall x : A, forall s : A -> Prop, (FINITE' s) -> FINITE' (@INSERT A x s))) -> forall a : A -> Prop, (@finite_set A a) -> FINITE' a.
Axiom thm_INFINITE : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) = (~ (@finite_set A s)).
Axiom thm_IMAGE : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@IMAGE A B f s) = (@GSPEC B (fun GEN_PVAR_7 : B => exists y : B, @SETSPEC B GEN_PVAR_7 (exists x : A, (@IN A x s) /\ (y = (f x))) y)).
Axiom thm_INJ : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, forall f : A -> B, (@INJ A B f s t) = ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_SURJ : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, forall f : A -> B, (@SURJ A B f s t) = ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : B, (@IN B x t) -> exists y : A, (@IN A y s) /\ ((f y) = x))).
Axiom thm_BIJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, (@BIJ A B f s t) = ((@INJ A B f s t) /\ (@SURJ A B f s t)).
Axiom thm_CHOICE : forall {A : Type'}, forall s : A -> Prop, (@CHOICE A s) = (@ε A (fun x : A => @IN A x s)).
Axiom thm_REST : forall {A : Type'}, forall s : A -> Prop, (@REST A s) = (@DELETE A s (@CHOICE A s)).
Axiom thm_NOT_IN_EMPTY : forall {A : Type'}, forall x : A, ~ (@IN A x (@set0 A)).
Axiom thm_IN_UNIV : forall {A : Type'}, forall x : A, @IN A x (@setT A).
Axiom thm_IN_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@IN A x (@setU A s t)) = ((@IN A x s) \/ (@IN A x t)).
Axiom thm_IN_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall x : A, (@IN A x (@UNIONS A s)) = (exists t : A -> Prop, (@IN (A -> Prop) t s) /\ (@IN A x t)).
Axiom thm_IN_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@IN A x (@setI A s t)) = ((@IN A x s) /\ (@IN A x t)).
Axiom thm_IN_INTERS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall x : A, (@IN A x (@INTERS A s)) = (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @IN A x t).
Axiom thm_IN_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@IN A x (@setD A s t)) = ((@IN A x s) /\ (~ (@IN A x t))).
Axiom thm_IN_INSERT : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@IN A x (@INSERT A y s)) = ((x = y) \/ (@IN A x s)).
Axiom thm_IN_DELETE : forall {A : Type'}, forall s : A -> Prop, forall x : A, forall y : A, (@IN A x (@DELETE A s y)) = ((@IN A x s) /\ (~ (x = y))).
Axiom thm_IN_SING : forall {A : Type'}, forall x : A, forall y : A, (@IN A x (@INSERT A y (@set0 A))) = (x = y).
Axiom thm_IN_IMAGE : forall {A B : Type'}, forall y : B, forall s : A -> Prop, forall f : A -> B, (@IN B y (@IMAGE A B f s)) = (exists x : A, (y = (f x)) /\ (@IN A x s)).
Axiom thm_IN_REST : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x (@REST A s)) = ((@IN A x s) /\ (~ (x = (@CHOICE A s)))).
Axiom thm_FORALL_IN_INSERT : forall {A : Type'}, forall P : A -> Prop, forall a : A, forall s : A -> Prop, (forall x : A, (@IN A x (@INSERT A a s)) -> P x) = ((P a) /\ (forall x : A, (@IN A x s) -> P x)).
Axiom thm_EXISTS_IN_INSERT : forall {A : Type'}, forall P : A -> Prop, forall a : A, forall s : A -> Prop, (exists x : A, (@IN A x (@INSERT A a s)) /\ (P x)) = ((P a) \/ (exists x : A, (@IN A x s) /\ (P x))).
Axiom thm_FORALL_IN_UNION : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (forall x : A, (@IN A x (@setU A s t)) -> P x) = ((forall x : A, (@IN A x s) -> P x) /\ (forall x : A, (@IN A x t) -> P x)).
Axiom thm_EXISTS_IN_UNION : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (exists x : A, (@IN A x (@setU A s t)) /\ (P x)) = ((exists x : A, (@IN A x s) /\ (P x)) \/ (exists x : A, (@IN A x t) /\ (P x))).
Axiom thm_FORALL_IN_IMAGE : forall {A B : Type'} (P : B -> Prop), forall f : A -> B, forall s : A -> Prop, (forall y : B, (@IN B y (@IMAGE A B f s)) -> P y) = (forall x : A, (@IN A x s) -> P (f x)).
Axiom thm_EXISTS_IN_IMAGE : forall {A B : Type'} (P : B -> Prop), forall f : A -> B, forall s : A -> Prop, (exists y : B, (@IN B y (@IMAGE A B f s)) /\ (P y)) = (exists x : A, (@IN A x s) /\ (P (f x))).
Axiom thm_FORALL_IN_GSPEC : forall {A B C D E : Type'}, (forall P : A -> Prop, forall Q : B -> Prop, forall f : A -> B, (forall z : B, (@IN B z (@GSPEC B (fun GEN_PVAR_8 : B => exists x : A, @SETSPEC B GEN_PVAR_8 (P x) (f x)))) -> Q z) = (forall x : A, (P x) -> Q (f x))) /\ ((forall P : A -> B -> Prop, forall Q : C -> Prop, forall f : A -> B -> C, (forall z : C, (@IN C z (@GSPEC C (fun GEN_PVAR_9 : C => exists x : A, exists y : B, @SETSPEC C GEN_PVAR_9 (P x y) (f x y)))) -> Q z) = (forall x : A, forall y : B, (P x y) -> Q (f x y))) /\ ((forall P : A -> B -> C -> Prop, forall Q : D -> Prop, forall f : A -> B -> C -> D, (forall z : D, (@IN D z (@GSPEC D (fun GEN_PVAR_10 : D => exists w : A, exists x : B, exists y : C, @SETSPEC D GEN_PVAR_10 (P w x y) (f w x y)))) -> Q z) = (forall w : A, forall x : B, forall y : C, (P w x y) -> Q (f w x y))) /\ (forall P : A -> B -> C -> D -> Prop, forall Q : E -> Prop, forall f : A -> B -> C -> D -> E, (forall z : E, (@IN E z (@GSPEC E (fun GEN_PVAR_11 : E => exists v : A, exists w : B, exists x : C, exists y : D, @SETSPEC E GEN_PVAR_11 (P v w x y) (f v w x y)))) -> Q z) = (forall v : A, forall w : B, forall x : C, forall y : D, (P v w x y) -> Q (f v w x y))))).
Axiom thm_EXISTS_IN_GSPEC : forall {A B C D E : Type'}, (forall P : A -> Prop, forall Q : B -> Prop, forall f : A -> B, (exists z : B, (@IN B z (@GSPEC B (fun GEN_PVAR_12 : B => exists x : A, @SETSPEC B GEN_PVAR_12 (P x) (f x)))) /\ (Q z)) = (exists x : A, (P x) /\ (Q (f x)))) /\ ((forall P : A -> B -> Prop, forall Q : C -> Prop, forall f : A -> B -> C, (exists z : C, (@IN C z (@GSPEC C (fun GEN_PVAR_13 : C => exists x : A, exists y : B, @SETSPEC C GEN_PVAR_13 (P x y) (f x y)))) /\ (Q z)) = (exists x : A, exists y : B, (P x y) /\ (Q (f x y)))) /\ ((forall P : A -> B -> C -> Prop, forall Q : D -> Prop, forall f : A -> B -> C -> D, (exists z : D, (@IN D z (@GSPEC D (fun GEN_PVAR_14 : D => exists w : A, exists x : B, exists y : C, @SETSPEC D GEN_PVAR_14 (P w x y) (f w x y)))) /\ (Q z)) = (exists w : A, exists x : B, exists y : C, (P w x y) /\ (Q (f w x y)))) /\ (forall P : A -> B -> C -> D -> Prop, forall Q : E -> Prop, forall f : A -> B -> C -> D -> E, (exists z : E, (@IN E z (@GSPEC E (fun GEN_PVAR_15 : E => exists v : A, exists w : B, exists x : C, exists y : D, @SETSPEC E GEN_PVAR_15 (P v w x y) (f v w x y)))) /\ (Q z)) = (exists v : A, exists w : B, exists x : C, exists y : D, (P v w x y) /\ (Q (f v w x y)))))).
Axiom thm_UNIONS_IMAGE : forall {A B : Type'}, forall f : A -> B -> Prop, forall s : A -> Prop, (@UNIONS B (@IMAGE A (B -> Prop) f s)) = (@GSPEC B (fun GEN_PVAR_16 : B => exists y : B, @SETSPEC B GEN_PVAR_16 (exists x : A, (@IN A x s) /\ (@IN B y (f x))) y)).
Axiom thm_INTERS_IMAGE : forall {A B : Type'}, forall f : A -> B -> Prop, forall s : A -> Prop, (@INTERS B (@IMAGE A (B -> Prop) f s)) = (@GSPEC B (fun GEN_PVAR_17 : B => exists y : B, @SETSPEC B GEN_PVAR_17 (forall x : A, (@IN A x s) -> @IN B y (f x)) y)).
Axiom thm_UNIONS_GSPEC : forall {A B C D : Type'}, (forall P : A -> Prop, forall f : A -> B -> Prop, (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_18 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_18 (P x) (f x)))) = (@GSPEC B (fun GEN_PVAR_19 : B => exists a : B, @SETSPEC B GEN_PVAR_19 (exists x : A, (P x) /\ (@IN B a (f x))) a))) /\ ((forall P : A -> B -> Prop, forall f : A -> B -> C -> Prop, (@UNIONS C (@GSPEC (C -> Prop) (fun GEN_PVAR_20 : C -> Prop => exists x : A, exists y : B, @SETSPEC (C -> Prop) GEN_PVAR_20 (P x y) (f x y)))) = (@GSPEC C (fun GEN_PVAR_21 : C => exists a : C, @SETSPEC C GEN_PVAR_21 (exists x : A, exists y : B, (P x y) /\ (@IN C a (f x y))) a))) /\ (forall P : A -> B -> C -> Prop, forall f : A -> B -> C -> D -> Prop, (@UNIONS D (@GSPEC (D -> Prop) (fun GEN_PVAR_22 : D -> Prop => exists x : A, exists y : B, exists z : C, @SETSPEC (D -> Prop) GEN_PVAR_22 (P x y z) (f x y z)))) = (@GSPEC D (fun GEN_PVAR_23 : D => exists a : D, @SETSPEC D GEN_PVAR_23 (exists x : A, exists y : B, exists z : C, (P x y z) /\ (@IN D a (f x y z))) a)))).
Axiom thm_INTERS_GSPEC : forall {A B C D : Type'}, (forall P : A -> Prop, forall f : A -> B -> Prop, (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_24 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_24 (P x) (f x)))) = (@GSPEC B (fun GEN_PVAR_25 : B => exists a : B, @SETSPEC B GEN_PVAR_25 (forall x : A, (P x) -> @IN B a (f x)) a))) /\ ((forall P : A -> B -> Prop, forall f : A -> B -> C -> Prop, (@INTERS C (@GSPEC (C -> Prop) (fun GEN_PVAR_26 : C -> Prop => exists x : A, exists y : B, @SETSPEC (C -> Prop) GEN_PVAR_26 (P x y) (f x y)))) = (@GSPEC C (fun GEN_PVAR_27 : C => exists a : C, @SETSPEC C GEN_PVAR_27 (forall x : A, forall y : B, (P x y) -> @IN C a (f x y)) a))) /\ (forall P : A -> B -> C -> Prop, forall f : A -> B -> C -> D -> Prop, (@INTERS D (@GSPEC (D -> Prop) (fun GEN_PVAR_28 : D -> Prop => exists x : A, exists y : B, exists z : C, @SETSPEC (D -> Prop) GEN_PVAR_28 (P x y z) (f x y z)))) = (@GSPEC D (fun GEN_PVAR_29 : D => exists a : D, @SETSPEC D GEN_PVAR_29 (forall x : A, forall y : B, forall z : C, (P x y z) -> @IN D a (f x y z)) a)))).
Axiom thm_CHOICE_DEF : forall {A : Type'}, forall s : A -> Prop, (~ (s = (@set0 A))) -> @IN A (@CHOICE A s) s.
Axiom thm_NOT_EQUAL_SETS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (~ (s = t)) = (exists x : A, (@IN A x t) = (~ (@IN A x s))).
Axiom thm_INSERT_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall a : A, (@GSPEC A (fun GEN_PVAR_30 : A => exists x : A, @SETSPEC A GEN_PVAR_30 ((@IN A x (@INSERT A a s)) /\ (P x)) x)) = (@COND (A -> Prop) (P a) (@INSERT A a (@GSPEC A (fun GEN_PVAR_31 : A => exists x : A, @SETSPEC A GEN_PVAR_31 ((@IN A x s) /\ (P x)) x))) (@GSPEC A (fun GEN_PVAR_32 : A => exists x : A, @SETSPEC A GEN_PVAR_32 ((@IN A x s) /\ (P x)) x))).
Axiom thm_UNIV_1 : (@setT unit) = (@INSERT unit tt (@set0 unit)).
Axiom thm_MEMBER_NOT_EMPTY : forall {A : Type'}, forall s : A -> Prop, (exists x : A, @IN A x s) = (~ (s = (@set0 A))).
Axiom thm_UNIV_NOT_EMPTY : forall {A : Type'}, ~ ((@setT A) = (@set0 A)).
Axiom thm_EMPTY_NOT_UNIV : forall {A : Type'}, ~ ((@set0 A) = (@setT A)).
Axiom thm_EQ_UNIV : forall {A : Type'} (s : A -> Prop), (forall x : A, @IN A x s) = (s = (@setT A)).
Axiom thm_SUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@subset A s t) /\ (@subset A t u)) -> @subset A s u.
Axiom thm_SUBSET_REFL : forall {A : Type'}, forall s : A -> Prop, @subset A s s.
Axiom thm_SUBSET_ANTISYM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@subset A s t) /\ (@subset A t s)) -> s = t.
Axiom thm_SUBSET_ANTISYM_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@subset A s t) /\ (@subset A t s)) = (s = t).
Axiom thm_EMPTY_SUBSET : forall {A : Type'}, forall s : A -> Prop, @subset A (@set0 A) s.
Axiom thm_SUBSET_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@subset A s (@set0 A)) = (s = (@set0 A)).
Axiom thm_SUBSET_UNIV : forall {A : Type'}, forall s : A -> Prop, @subset A s (@setT A).
Axiom thm_UNIV_SUBSET : forall {A : Type'}, forall s : A -> Prop, (@subset A (@setT A) s) = (s = (@setT A)).
Axiom thm_SING_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@subset A (@INSERT A x (@set0 A)) s) = (@IN A x s).
Axiom thm_SUBSET_RESTRICT : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, @subset A (@GSPEC A (fun GEN_PVAR_33 : A => exists x : A, @SETSPEC A GEN_PVAR_33 ((@IN A x s) /\ (P x)) x)) s.
Axiom thm_PSUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@proper A s t) /\ (@proper A t u)) -> @proper A s u.
Axiom thm_PSUBSET_SUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@proper A s t) /\ (@subset A t u)) -> @proper A s u.
Axiom thm_SUBSET_PSUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@subset A s t) /\ (@proper A t u)) -> @proper A s u.
Axiom thm_PSUBSET_IRREFL : forall {A : Type'}, forall s : A -> Prop, ~ (@proper A s s).
Axiom thm_NOT_PSUBSET_EMPTY : forall {A : Type'}, forall s : A -> Prop, ~ (@proper A s (@set0 A)).
Axiom thm_NOT_UNIV_PSUBSET : forall {A : Type'}, forall s : A -> Prop, ~ (@proper A (@setT A) s).
Axiom thm_PSUBSET_UNIV : forall {A : Type'}, forall s : A -> Prop, (@proper A s (@setT A)) = (exists x : A, ~ (@IN A x s)).
Axiom thm_PSUBSET_ALT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@proper A s t) = ((@subset A s t) /\ (exists a : A, (@IN A a t) /\ (~ (@IN A a s)))).
Axiom thm_UNION_ASSOC : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setU A (@setU A s t) u) = (@setU A s (@setU A t u)).
Axiom thm_UNION_IDEMPOT : forall {A : Type'}, forall s : A -> Prop, (@setU A s s) = s.
Axiom thm_UNION_COMM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setU A s t) = (@setU A t s).
Axiom thm_SUBSET_UNION : forall {A : Type'}, (forall s : A -> Prop, forall t : A -> Prop, @subset A s (@setU A s t)) /\ (forall s : A -> Prop, forall t : A -> Prop, @subset A s (@setU A t s)).
Axiom thm_SUBSET_UNION_ABSORPTION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) = ((@setU A s t) = t).
Axiom thm_UNION_EMPTY : forall {A : Type'}, (forall s : A -> Prop, (@setU A (@set0 A) s) = s) /\ (forall s : A -> Prop, (@setU A s (@set0 A)) = s).
Axiom thm_UNION_UNIV : forall {A : Type'}, (forall s : A -> Prop, (@setU A (@setT A) s) = (@setT A)) /\ (forall s : A -> Prop, (@setU A s (@setT A)) = (@setT A)).
Axiom thm_EMPTY_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@setU A s t) = (@set0 A)) = ((s = (@set0 A)) /\ (t = (@set0 A))).
Axiom thm_UNION_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@subset A (@setU A s t) u) = ((@subset A s u) /\ (@subset A t u)).
Axiom thm_UNION_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@GSPEC A (fun GEN_PVAR_34 : A => exists x : A, @SETSPEC A GEN_PVAR_34 ((@IN A x (@setU A s t)) /\ (P x)) x)) = (@setU A (@GSPEC A (fun GEN_PVAR_35 : A => exists x : A, @SETSPEC A GEN_PVAR_35 ((@IN A x s) /\ (P x)) x)) (@GSPEC A (fun GEN_PVAR_36 : A => exists x : A, @SETSPEC A GEN_PVAR_36 ((@IN A x t) /\ (P x)) x))).
Axiom thm_FORALL_SUBSET_UNION : forall {A : Type'} (P : (A -> Prop) -> Prop), forall t : A -> Prop, forall u : A -> Prop, (forall s : A -> Prop, (@subset A s (@setU A t u)) -> P s) = (forall t' : A -> Prop, forall u' : A -> Prop, ((@subset A t' t) /\ (@subset A u' u)) -> P (@setU A t' u')).
Axiom thm_EXISTS_SUBSET_UNION : forall {A : Type'} (P : (A -> Prop) -> Prop), forall t : A -> Prop, forall u : A -> Prop, (exists s : A -> Prop, (@subset A s (@setU A t u)) /\ (P s)) = (exists t' : A -> Prop, exists u' : A -> Prop, (@subset A t' t) /\ ((@subset A u' u) /\ (P (@setU A t' u')))).
Axiom thm_FORALL_SUBSET_INSERT : forall {A : Type'} (P : (A -> Prop) -> Prop), forall a : A, forall t : A -> Prop, (forall s : A -> Prop, (@subset A s (@INSERT A a t)) -> P s) = (forall s : A -> Prop, (@subset A s t) -> (P s) /\ (P (@INSERT A a s))).
Axiom thm_EXISTS_SUBSET_INSERT : forall {A : Type'} (P : (A -> Prop) -> Prop), forall a : A, forall t : A -> Prop, (exists s : A -> Prop, (@subset A s (@INSERT A a t)) /\ (P s)) = (exists s : A -> Prop, (@subset A s t) /\ ((P s) \/ (P (@INSERT A a s)))).
Axiom thm_INTER_ASSOC : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setI A (@setI A s t) u) = (@setI A s (@setI A t u)).
Axiom thm_INTER_IDEMPOT : forall {A : Type'}, forall s : A -> Prop, (@setI A s s) = s.
Axiom thm_INTER_COMM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setI A s t) = (@setI A t s).
Axiom thm_INTER_SUBSET : forall {A : Type'}, (forall s : A -> Prop, forall t : A -> Prop, @subset A (@setI A s t) s) /\ (forall s : A -> Prop, forall t : A -> Prop, @subset A (@setI A t s) s).
Axiom thm_SUBSET_INTER_ABSORPTION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) = ((@setI A s t) = s).
Axiom thm_INTER_EMPTY : forall {A : Type'}, (forall s : A -> Prop, (@setI A (@set0 A) s) = (@set0 A)) /\ (forall s : A -> Prop, (@setI A s (@set0 A)) = (@set0 A)).
Axiom thm_INTER_UNIV : forall {A : Type'}, (forall s : A -> Prop, (@setI A (@setT A) s) = s) /\ (forall s : A -> Prop, (@setI A s (@setT A)) = s).
Axiom thm_SUBSET_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@subset A s (@setI A t u)) = ((@subset A s t) /\ (@subset A s u)).
Axiom thm_INTER_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@GSPEC A (fun GEN_PVAR_37 : A => exists x : A, @SETSPEC A GEN_PVAR_37 ((@IN A x (@setI A s t)) /\ (P x)) x)) = (@setI A (@GSPEC A (fun GEN_PVAR_38 : A => exists x : A, @SETSPEC A GEN_PVAR_38 ((@IN A x s) /\ (P x)) x)) (@GSPEC A (fun GEN_PVAR_39 : A => exists x : A, @SETSPEC A GEN_PVAR_39 ((@IN A x t) /\ (P x)) x))).
Axiom thm_UNION_OVER_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setI A s (@setU A t u)) = (@setU A (@setI A s t) (@setI A s u)).
Axiom thm_INTER_OVER_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setU A s (@setI A t u)) = (@setI A (@setU A s t) (@setU A s u)).
Axiom thm_IN_DISJOINT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A s t) = (~ (exists x : A, (@IN A x s) /\ (@IN A x t))).
Axiom thm_DISJOINT_SYM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A s t) = (@DISJOINT A t s).
Axiom thm_DISJOINT_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@DISJOINT A (@set0 A) s) /\ (@DISJOINT A s (@set0 A)).
Axiom thm_DISJOINT_EMPTY_REFL : forall {A : Type'}, forall s : A -> Prop, (s = (@set0 A)) = (@DISJOINT A s s).
Axiom thm_DISJOINT_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@DISJOINT A (@setU A s t) u) = ((@DISJOINT A s u) /\ (@DISJOINT A t u)).
Axiom thm_DISJOINT_SING : forall {A : Type'}, (forall s : A -> Prop, forall a : A, (@DISJOINT A s (@INSERT A a (@set0 A))) = (~ (@IN A a s))) /\ (forall s : A -> Prop, forall a : A, (@DISJOINT A (@INSERT A a (@set0 A)) s) = (~ (@IN A a s))).
Axiom thm_DIFF_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@setD A s (@set0 A)) = s.
Axiom thm_EMPTY_DIFF : forall {A : Type'}, forall s : A -> Prop, (@setD A (@set0 A) s) = (@set0 A).
Axiom thm_DIFF_UNIV : forall {A : Type'}, forall s : A -> Prop, (@setD A s (@setT A)) = (@set0 A).
Axiom thm_DIFF_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setD A (@setD A s t) t) = (@setD A s t).
Axiom thm_DIFF_EQ_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@setD A s s) = (@set0 A).
Axiom thm_SUBSET_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, @subset A (@setD A s t) s.
Axiom thm_COMPL_COMPL : forall {A : Type'}, forall s : A -> Prop, (@setD A (@setT A) (@setD A (@setT A) s)) = s.
Axiom thm_DIFF_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@GSPEC A (fun GEN_PVAR_40 : A => exists x : A, @SETSPEC A GEN_PVAR_40 ((@IN A x (@setD A s t)) /\ (P x)) x)) = (@setD A (@GSPEC A (fun GEN_PVAR_41 : A => exists x : A, @SETSPEC A GEN_PVAR_41 ((@IN A x s) /\ (P x)) x)) (@GSPEC A (fun GEN_PVAR_42 : A => exists x : A, @SETSPEC A GEN_PVAR_42 ((@IN A x t) /\ (P x)) x))).
Axiom thm_COMPONENT : forall {A : Type'}, forall x : A, forall s : A -> Prop, @IN A x (@INSERT A x s).
Axiom thm_DECOMPOSITION : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@IN A x s) = (exists t : A -> Prop, (s = (@INSERT A x t)) /\ (~ (@IN A x t))).
Axiom thm_SET_CASES : forall {A : Type'}, forall s : A -> Prop, (s = (@set0 A)) \/ (exists x : A, exists t : A -> Prop, (s = (@INSERT A x t)) /\ (~ (@IN A x t))).
Axiom thm_ABSORPTION : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x s) = ((@INSERT A x s) = s).
Axiom thm_INSERT_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@INSERT A x (@INSERT A x s)) = (@INSERT A x s).
Axiom thm_INSERT_COMM : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@INSERT A x (@INSERT A y s)) = (@INSERT A y (@INSERT A x s)).
Axiom thm_INSERT_UNIV : forall {A : Type'}, forall x : A, (@INSERT A x (@setT A)) = (@setT A).
Axiom thm_NOT_INSERT_EMPTY : forall {A : Type'}, forall x : A, forall s : A -> Prop, ~ ((@INSERT A x s) = (@set0 A)).
Axiom thm_NOT_EMPTY_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, ~ ((@set0 A) = (@INSERT A x s)).
Axiom thm_INSERT_UNION : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@setU A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@setU A s t) (@INSERT A x (@setU A s t))).
Axiom thm_INSERT_UNION_EQ : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@setU A (@INSERT A x s) t) = (@INSERT A x (@setU A s t)).
Axiom thm_INSERT_INTER : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@setI A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@INSERT A x (@setI A s t)) (@setI A s t)).
Axiom thm_DISJOINT_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A (@INSERT A x s) t) = ((@DISJOINT A s t) /\ (~ (@IN A x t))).
Axiom thm_INSERT_SUBSET : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@subset A (@INSERT A x s) t) = ((@IN A x t) /\ (@subset A s t)).
Axiom thm_SUBSET_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, (~ (@IN A x s)) -> forall t : A -> Prop, (@subset A s (@INSERT A x t)) = (@subset A s t).
Axiom thm_INSERT_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@setD A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@setD A s t) (@INSERT A x (@setD A s t))).
Axiom thm_INSERT_AC : forall {A : Type'} (y : A) (x : A) (s : A -> Prop), ((@INSERT A x (@INSERT A y s)) = (@INSERT A y (@INSERT A x s))) /\ ((@INSERT A x (@INSERT A x s)) = (@INSERT A x s)).
Axiom thm_INTER_ACI : forall {A : Type'} (r : A -> Prop) (p : A -> Prop) (q : A -> Prop), ((@setI A p q) = (@setI A q p)) /\ (((@setI A (@setI A p q) r) = (@setI A p (@setI A q r))) /\ (((@setI A p (@setI A q r)) = (@setI A q (@setI A p r))) /\ (((@setI A p p) = p) /\ ((@setI A p (@setI A p q)) = (@setI A p q))))).
Axiom thm_UNION_ACI : forall {A : Type'} (r : A -> Prop) (p : A -> Prop) (q : A -> Prop), ((@setU A p q) = (@setU A q p)) /\ (((@setU A (@setU A p q) r) = (@setU A p (@setU A q r))) /\ (((@setU A p (@setU A q r)) = (@setU A q (@setU A p r))) /\ (((@setU A p p) = p) /\ ((@setU A p (@setU A p q)) = (@setU A p q))))).
Axiom thm_DELETE_NON_ELEMENT : forall {A : Type'}, forall x : A, forall s : A -> Prop, (~ (@IN A x s)) = ((@DELETE A s x) = s).
Axiom thm_IN_DELETE_EQ : forall {A : Type'}, forall s : A -> Prop, forall x : A, forall x' : A, ((@IN A x s) = (@IN A x' s)) = ((@IN A x (@DELETE A s x')) = (@IN A x' (@DELETE A s x))).
Axiom thm_EMPTY_DELETE : forall {A : Type'}, forall x : A, (@DELETE A (@set0 A) x) = (@set0 A).
Axiom thm_DELETE_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@DELETE A (@DELETE A s x) x) = (@DELETE A s x).
Axiom thm_DELETE_COMM : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@DELETE A (@DELETE A s x) y) = (@DELETE A (@DELETE A s y) x).
Axiom thm_DELETE_SUBSET : forall {A : Type'}, forall x : A, forall s : A -> Prop, @subset A (@DELETE A s x) s.
Axiom thm_SUBSET_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@subset A s (@DELETE A t x)) = ((~ (@IN A x s)) /\ (@subset A s t)).
Axiom thm_SUBSET_INSERT_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@subset A s (@INSERT A x t)) = (@subset A (@DELETE A s x) t).
Axiom thm_DIFF_INSERT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@setD A s (@INSERT A x t)) = (@setD A (@DELETE A s x) t).
Axiom thm_PSUBSET_INSERT_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@proper A s t) = (exists x : A, (~ (@IN A x s)) /\ (@subset A (@INSERT A x s) t)).
Axiom thm_DELETE_INSERT : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@DELETE A (@INSERT A x s) y) = (@COND (A -> Prop) (x = y) (@DELETE A s y) (@INSERT A x (@DELETE A s y))).
Axiom thm_INSERT_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x s) -> (@INSERT A x (@DELETE A s x)) = s.
Axiom thm_DELETE_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@setI A (@DELETE A s x) t) = (@DELETE A (@setI A s t) x).
Axiom thm_DISJOINT_DELETE_SYM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@DISJOINT A (@DELETE A s x) t) = (@DISJOINT A (@DELETE A t x) s).
Axiom thm_UNIONS_0 : forall {A : Type'}, (@UNIONS A (@set0 (A -> Prop))) = (@set0 A).
Axiom thm_UNIONS_1 : forall {A : Type'}, forall s : A -> Prop, (@UNIONS A (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) = s.
Axiom thm_UNIONS_2 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@UNIONS A (@INSERT (A -> Prop) s (@INSERT (A -> Prop) t (@set0 (A -> Prop))))) = (@setU A s t).
Axiom thm_UNIONS_INSERT : forall {A : Type'}, forall s : A -> Prop, forall u : (A -> Prop) -> Prop, (@UNIONS A (@INSERT (A -> Prop) s u)) = (@setU A s (@UNIONS A u)).
Axiom thm_FORALL_IN_UNIONS : forall {A : Type'}, forall P : A -> Prop, forall s : (A -> Prop) -> Prop, (forall x : A, (@IN A x (@UNIONS A s)) -> P x) = (forall t : A -> Prop, forall x : A, ((@IN (A -> Prop) t s) /\ (@IN A x t)) -> P x).
Axiom thm_EXISTS_IN_UNIONS : forall {A : Type'}, forall P : A -> Prop, forall s : (A -> Prop) -> Prop, (exists x : A, (@IN A x (@UNIONS A s)) /\ (P x)) = (exists t : A -> Prop, exists x : A, (@IN (A -> Prop) t s) /\ ((@IN A x t) /\ (P x))).
Axiom thm_EMPTY_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, ((@UNIONS A s) = (@set0 A)) = (forall t : A -> Prop, (@IN (A -> Prop) t s) -> t = (@set0 A)).
Axiom thm_INTER_UNIONS : forall {A : Type'}, (forall s : (A -> Prop) -> Prop, forall t : A -> Prop, (@setI A (@UNIONS A s) t) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_43 : A -> Prop => exists x : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_43 (@IN (A -> Prop) x s) (@setI A x t))))) /\ (forall s : (A -> Prop) -> Prop, forall t : A -> Prop, (@setI A t (@UNIONS A s)) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_44 : A -> Prop => exists x : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_44 (@IN (A -> Prop) x s) (@setI A t x))))).
Axiom thm_UNIONS_SUBSET : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall t : A -> Prop, (@subset A (@UNIONS A f) t) = (forall s : A -> Prop, (@IN (A -> Prop) s f) -> @subset A s t).
Axiom thm_SUBSET_UNIONS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall g : (A -> Prop) -> Prop, (@subset (A -> Prop) f g) -> @subset A (@UNIONS A f) (@UNIONS A g).
Axiom thm_UNIONS_UNION : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (@UNIONS A (@setU (A -> Prop) s t)) = (@setU A (@UNIONS A s) (@UNIONS A t)).
Axiom thm_INTERS_UNION : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (@INTERS A (@setU (A -> Prop) s t)) = (@setI A (@INTERS A s) (@INTERS A t)).
Axiom thm_UNIONS_MONO : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (forall x : A -> Prop, (@IN (A -> Prop) x s) -> exists y : A -> Prop, (@IN (A -> Prop) y t) /\ (@subset A x y)) -> @subset A (@UNIONS A s) (@UNIONS A t).
Axiom thm_UNIONS_MONO_IMAGE : forall {A B : Type'}, forall f : A -> B -> Prop, forall g : A -> B -> Prop, forall s : A -> Prop, (forall x : A, (@IN A x s) -> @subset B (f x) (g x)) -> @subset B (@UNIONS B (@IMAGE A (B -> Prop) f s)) (@UNIONS B (@IMAGE A (B -> Prop) g s)).
Axiom thm_UNIONS_UNIV : forall {A : Type'}, (@UNIONS A (@setT (A -> Prop))) = (@setT A).
Axiom thm_UNIONS_INSERT_EMPTY : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A (@INSERT (A -> Prop) (@set0 A) s)) = (@UNIONS A s).
Axiom thm_UNIONS_DELETE_EMPTY : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A (@DELETE (A -> Prop) s (@set0 A))) = (@UNIONS A s).
Axiom thm_INTERS_0 : forall {A : Type'}, (@INTERS A (@set0 (A -> Prop))) = (@setT A).
Axiom thm_INTERS_1 : forall {A : Type'}, forall s : A -> Prop, (@INTERS A (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) = s.
Axiom thm_INTERS_2 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@INTERS A (@INSERT (A -> Prop) s (@INSERT (A -> Prop) t (@set0 (A -> Prop))))) = (@setI A s t).
Axiom thm_INTERS_INSERT : forall {A : Type'}, forall s : A -> Prop, forall u : (A -> Prop) -> Prop, (@INTERS A (@INSERT (A -> Prop) s u)) = (@setI A s (@INTERS A u)).
Axiom thm_SUBSET_INTERS : forall {A : Type'}, forall s : A -> Prop, forall f : (A -> Prop) -> Prop, (@subset A s (@INTERS A f)) = (forall t : A -> Prop, (@IN (A -> Prop) t f) -> @subset A s t).
Axiom thm_INTERS_SUBSET : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (u = (@set0 (A -> Prop)))) /\ (forall t : A -> Prop, (@IN (A -> Prop) t u) -> @subset A t s)) -> @subset A (@INTERS A u) s.
Axiom thm_INTERS_SUBSET_STRONG : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall s : A -> Prop, (exists t : A -> Prop, (@IN (A -> Prop) t u) /\ (@subset A t s)) -> @subset A (@INTERS A u) s.
Axiom thm_INTERS_ANTIMONO : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall g : (A -> Prop) -> Prop, (@subset (A -> Prop) g f) -> @subset A (@INTERS A f) (@INTERS A g).
Axiom thm_INTERS_EQ_UNIV : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@INTERS A f) = (@setT A)) = (forall s : A -> Prop, (@IN (A -> Prop) s f) -> s = (@setT A)).
Axiom thm_INTERS_ANTIMONO_GEN : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (forall y : A -> Prop, (@IN (A -> Prop) y t) -> exists x : A -> Prop, (@IN (A -> Prop) x s) /\ (@subset A x y)) -> @subset A (@INTERS A s) (@INTERS A t).
Axiom thm_IMAGE_CLAUSES : forall {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop), ((@IMAGE A B f (@set0 A)) = (@set0 B)) /\ ((@IMAGE A B f (@INSERT A x s)) = (@INSERT B (f x) (@IMAGE A B f s))).
Axiom thm_IMAGE_UNION : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (@IMAGE A B f (@setU A s t)) = (@setU B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_ID : forall {A : Type'}, forall s : A -> Prop, (@IMAGE A A (fun x : A => x) s) = s.
Axiom thm_IMAGE_I : forall {A : Type'}, forall s : A -> Prop, (@IMAGE A A (@I A) s) = s.
Axiom thm_IMAGE_o : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, forall s : A -> Prop, (@IMAGE A C (@o A B C f g) s) = (@IMAGE B C f (@IMAGE A B g s)).
Axiom thm_IMAGE_SUBSET : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) -> @subset B (@IMAGE A B f s) (@IMAGE A B f t).
Axiom thm_IMAGE_INTER_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) -> (@IMAGE A B f (@setI A s t)) = (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_DIFF_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y t) /\ ((f x) = (f y)))) -> x = y) -> (@IMAGE A B f (@setD A s t)) = (@setD B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_DIFF_INJ_ALT : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@subset A t s)) -> (@IMAGE A B f (@setD A s t)) = (@setD B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_DELETE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall a : A, (forall x : A, ((@IN A x s) /\ ((f x) = (f a))) -> x = a) -> (@IMAGE A B f (@DELETE A s a)) = (@DELETE B (@IMAGE A B f s) (f a)).
Axiom thm_IMAGE_DELETE_INJ_ALT : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall a : A, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@IN A a s)) -> (@IMAGE A B f (@DELETE A s a)) = (@DELETE B (@IMAGE A B f s) (f a)).
Axiom thm_IMAGE_EQ_EMPTY : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((@IMAGE A B f s) = (@set0 B)) = (s = (@set0 A)).
Axiom thm_FORALL_IN_IMAGE_2 : forall {A B : Type'}, forall f : A -> B, forall P : B -> B -> Prop, forall s : A -> Prop, (forall x : B, forall y : B, ((@IN B x (@IMAGE A B f s)) /\ (@IN B y (@IMAGE A B f s))) -> P x y) = (forall x : A, forall y : A, ((@IN A x s) /\ (@IN A y s)) -> P (f x) (f y)).
Axiom thm_IMAGE_CONST : forall {A B : Type'}, forall s : A -> Prop, forall c : B, (@IMAGE A B (fun x : A => c) s) = (@COND (B -> Prop) (s = (@set0 A)) (@set0 B) (@INSERT B c (@set0 B))).
Axiom thm_SIMPLE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@GSPEC B (fun GEN_PVAR_45 : B => exists x : A, @SETSPEC B GEN_PVAR_45 (@IN A x s) (f x))) = (@IMAGE A B f s).
Axiom thm_SIMPLE_IMAGE_GEN : forall {A B : Type'}, forall f : A -> B, forall P : A -> Prop, (@GSPEC B (fun GEN_PVAR_46 : B => exists x : A, @SETSPEC B GEN_PVAR_46 (P x) (f x))) = (@IMAGE A B f (@GSPEC A (fun GEN_PVAR_47 : A => exists x : A, @SETSPEC A GEN_PVAR_47 (P x) x))).
Axiom thm_IMAGE_UNIONS : forall {A B : Type'}, forall f : A -> B, forall s : (A -> Prop) -> Prop, (@IMAGE A B f (@UNIONS A s)) = (@UNIONS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) s)).
Axiom thm_FUN_IN_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall x : A, (@IN A x s) -> @IN B (f x) (@IMAGE A B f s).
Axiom thm_SURJECTIVE_IMAGE_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((forall y : B, (@IN B y t) -> exists x : A, (f x) = y) /\ (forall x : A, (@IN B (f x) t) = (@IN A x s))) -> (@IMAGE A B f s) = t.
Axiom thm_IMAGE_EQ : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@IMAGE A B f s) = (@IMAGE A B g s).
Axiom thm_EMPTY_GSPEC : forall {A : Type'}, (@GSPEC A (fun GEN_PVAR_48 : A => exists x : A, @SETSPEC A GEN_PVAR_48 False x)) = (@set0 A).
Axiom thm_UNIV_GSPEC : forall {A : Type'}, (@GSPEC A (fun GEN_PVAR_49 : A => exists x : A, @SETSPEC A GEN_PVAR_49 True x)) = (@setT A).
Axiom thm_SING_GSPEC : forall {A : Type'}, (forall a : A, (@GSPEC A (fun GEN_PVAR_50 : A => exists x : A, @SETSPEC A GEN_PVAR_50 (x = a) x)) = (@INSERT A a (@set0 A))) /\ (forall a : A, (@GSPEC A (fun GEN_PVAR_51 : A => exists x : A, @SETSPEC A GEN_PVAR_51 (a = x) x)) = (@INSERT A a (@set0 A))).
Axiom thm_SING_ALT : forall {A : Type'}, forall s : A -> Prop, (exists x : A, s = (@INSERT A x (@set0 A))) = (@ex1 A (fun x : A => @IN A x s)).
Axiom thm_IN_GSPEC : forall {A : Type'}, forall s : A -> Prop, (@GSPEC A (fun GEN_PVAR_52 : A => exists x : A, @SETSPEC A GEN_PVAR_52 (@IN A x s) x)) = s.
Axiom thm_IN_ELIM_PAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, forall a : A, forall b : B, (@IN (prod A B) (@pair A B a b) (@GSPEC (prod A B) (fun GEN_PVAR_53 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_53 (P x y) (@pair A B x y)))) = (P a b).
Axiom thm_IN_ELIM_TRIPLE_THM : forall {A B C : Type'}, (forall P : A -> B -> C -> Prop, forall a : A, forall b : B, forall c : C, (@IN (prod A (prod B C)) (@pair A (prod B C) a (@pair B C b c)) (@GSPEC (prod A (prod B C)) (fun GEN_PVAR_54 : prod A (prod B C) => exists x : A, exists y : B, exists z : C, @SETSPEC (prod A (prod B C)) GEN_PVAR_54 (P x y z) (@pair A (prod B C) x (@pair B C y z))))) = (P a b c)) /\ (forall P : A -> B -> C -> Prop, forall a : A, forall b : B, forall c : C, (@IN (prod (prod A B) C) (@pair (prod A B) C (@pair A B a b) c) (@GSPEC (prod (prod A B) C) (fun GEN_PVAR_55 : prod (prod A B) C => exists x : A, exists y : B, exists z : C, @SETSPEC (prod (prod A B) C) GEN_PVAR_55 (P x y z) (@pair (prod A B) C (@pair A B x y) z)))) = (P a b c)).
Axiom thm_IN_ELIM_QUAD_THM : forall {A B C D : Type'}, (forall P : A -> B -> C -> D -> Prop, forall a : A, forall b : B, forall c : C, forall d : D, (@IN (prod A (prod B (prod C D))) (@pair A (prod B (prod C D)) a (@pair B (prod C D) b (@pair C D c d))) (@GSPEC (prod A (prod B (prod C D))) (fun GEN_PVAR_56 : prod A (prod B (prod C D)) => exists w : A, exists x : B, exists y : C, exists z : D, @SETSPEC (prod A (prod B (prod C D))) GEN_PVAR_56 (P w x y z) (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))))) = (P a b c d)) /\ ((forall P : A -> B -> C -> D -> Prop, forall a : A, forall b : B, forall c : C, forall d : D, (@IN (prod (prod A B) (prod C D)) (@pair (prod A B) (prod C D) (@pair A B a b) (@pair C D c d)) (@GSPEC (prod (prod A B) (prod C D)) (fun GEN_PVAR_57 : prod (prod A B) (prod C D) => exists w : A, exists x : B, exists y : C, exists z : D, @SETSPEC (prod (prod A B) (prod C D)) GEN_PVAR_57 (P w x y z) (@pair (prod A B) (prod C D) (@pair A B w x) (@pair C D y z))))) = (P a b c d)) /\ (forall P : A -> B -> C -> D -> Prop, forall a : A, forall b : B, forall c : C, forall d : D, (@IN (prod (prod (prod A B) C) D) (@pair (prod (prod A B) C) D (@pair (prod A B) C (@pair A B a b) c) d) (@GSPEC (prod (prod (prod A B) C) D) (fun GEN_PVAR_58 : prod (prod (prod A B) C) D => exists w : A, exists x : B, exists y : C, exists z : D, @SETSPEC (prod (prod (prod A B) C) D) GEN_PVAR_58 (P w x y z) (@pair (prod (prod A B) C) D (@pair (prod A B) C (@pair A B w x) y) z)))) = (P a b c d))).
Axiom thm_SET_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (@GSPEC (prod A B) (fun GEN_PVAR_59 : prod A B => exists p : prod A B, @SETSPEC (prod A B) GEN_PVAR_59 (P p) p)) = (@GSPEC (prod A B) (fun GEN_PVAR_60 : prod A B => exists a : A, exists b : B, @SETSPEC (prod A B) GEN_PVAR_60 (P (@pair A B a b)) (@pair A B a b))).
Axiom thm_SET_PROVE_CASES : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@set0 A)) /\ (forall a : A, forall s : A -> Prop, (~ (@IN A a s)) -> P (@INSERT A a s))) -> forall s : A -> Prop, P s.
Axiom thm_UNIONS_SINGS_GEN : forall {A : Type'}, forall P : A -> Prop, (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_61 : A -> Prop => exists x : A, @SETSPEC (A -> Prop) GEN_PVAR_61 (P x) (@INSERT A x (@set0 A))))) = (@GSPEC A (fun GEN_PVAR_62 : A => exists x : A, @SETSPEC A GEN_PVAR_62 (P x) x)).
Axiom thm_UNIONS_SINGS : forall {A : Type'}, forall s : A -> Prop, (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_63 : A -> Prop => exists x : A, @SETSPEC (A -> Prop) GEN_PVAR_63 (@IN A x s) (@INSERT A x (@set0 A))))) = s.
Axiom thm_IMAGE_INTERS : forall {A B : Type'}, forall f : A -> B, forall s : (A -> Prop) -> Prop, ((~ (s = (@set0 (A -> Prop)))) /\ (forall x : A, forall y : A, ((@IN A x (@UNIONS A s)) /\ ((@IN A y (@UNIONS A s)) /\ ((f x) = (f y)))) -> x = y)) -> (@IMAGE A B f (@INTERS A s)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) s)).
Axiom thm_DIFF_INTERS : forall {A : Type'}, forall u : A -> Prop, forall s : (A -> Prop) -> Prop, (@setD A u (@INTERS A s)) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_64 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_64 (@IN (A -> Prop) t s) (@setD A u t)))).
Axiom thm_INTERS_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@INTERS A s) = (@setD A (@setT A) (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_65 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_65 (@IN (A -> Prop) t s) (@setD A (@setT A) t))))).
Axiom thm_UNIONS_INTERS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A s) = (@setD A (@setT A) (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_66 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_66 (@IN (A -> Prop) t s) (@setD A (@setT A) t))))).
Axiom thm_UNIONS_DIFF : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : A -> Prop, (@setD A (@UNIONS A s) t) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_67 : A -> Prop => exists x : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_67 (@IN (A -> Prop) x s) (@setD A x t)))).
Axiom thm_DIFF_UNIONS : forall {A : Type'}, forall u : A -> Prop, forall s : (A -> Prop) -> Prop, (@setD A u (@UNIONS A s)) = (@setI A u (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_68 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_68 (@IN (A -> Prop) t s) (@setD A u t))))).
Axiom thm_DIFF_UNIONS_NONEMPTY : forall {A : Type'}, forall u : A -> Prop, forall s : (A -> Prop) -> Prop, (~ (s = (@set0 (A -> Prop)))) -> (@setD A u (@UNIONS A s)) = (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_69 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_69 (@IN (A -> Prop) t s) (@setD A u t)))).
Axiom thm_INTERS_OVER_UNIONS : forall {A B : Type'}, forall f : A -> (B -> Prop) -> Prop, forall s : A -> Prop, (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_70 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_70 (@IN A x s) (@UNIONS B (f x))))) = (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_74 : B -> Prop => exists g : A -> B -> Prop, @SETSPEC (B -> Prop) GEN_PVAR_74 (forall x : A, (@IN A x s) -> @IN (B -> Prop) (g x) (f x)) (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_73 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_73 (@IN A x s) (g x))))))).
Axiom thm_INTER_INTERS : forall {A : Type'}, (forall f : (A -> Prop) -> Prop, forall s : A -> Prop, (@setI A s (@INTERS A f)) = (@COND (A -> Prop) (f = (@set0 (A -> Prop))) s (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_75 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_75 (@IN (A -> Prop) t f) (@setI A s t)))))) /\ (forall f : (A -> Prop) -> Prop, forall s : A -> Prop, (@setI A (@INTERS A f) s) = (@COND (A -> Prop) (f = (@set0 (A -> Prop))) s (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_76 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_76 (@IN (A -> Prop) t f) (@setI A t s)))))).
Axiom thm_UNIONS_OVER_INTERS : forall {A B : Type'}, forall f : A -> (B -> Prop) -> Prop, forall s : A -> Prop, (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_77 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_77 (@IN A x s) (@INTERS B (f x))))) = (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_81 : B -> Prop => exists g : A -> B -> Prop, @SETSPEC (B -> Prop) GEN_PVAR_81 (forall x : A, (@IN A x s) -> @IN (B -> Prop) (g x) (f x)) (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_80 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_80 (@IN A x s) (g x))))))).
Axiom thm_UNIONS_EQ_INTERS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@UNIONS A f) = (@INTERS A f)) = (exists s : A -> Prop, f = (@INSERT (A -> Prop) s (@set0 (A -> Prop)))).
Axiom thm_EXISTS_UNIQUE_UNIONS_INTERS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@ex1 (A -> Prop) (fun s : A -> Prop => P s)) = ((@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_82 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_82 (P s) s))) = (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_83 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_83 (P s) s)))).
Axiom thm_IMAGE_INTERS_SUBSET : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, @subset B (@IMAGE A B f (@INTERS A g)) (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
Axiom thm_IMAGE_INTER_SUBSET : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, @subset B (@IMAGE A B f (@setI A s t)) (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_INTER_SATURATED_GEN : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (((@subset A (@GSPEC A (fun GEN_PVAR_84 : A => exists x : A, @SETSPEC A GEN_PVAR_84 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f s))) x)) s) /\ (@subset A t u)) \/ ((@subset A (@GSPEC A (fun GEN_PVAR_85 : A => exists x : A, @SETSPEC A GEN_PVAR_85 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f t))) x)) t) /\ (@subset A s u))) -> (@IMAGE A B f (@setI A s t)) = (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_INTERS_SATURATED_GEN : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, forall s : A -> Prop, forall u : A -> Prop, ((~ (g = (@set0 (A -> Prop)))) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t g) -> @subset A t u) /\ (forall t : A -> Prop, (@IN (A -> Prop) t (@DELETE (A -> Prop) g s)) -> @subset A (@GSPEC A (fun GEN_PVAR_87 : A => exists x : A, @SETSPEC A GEN_PVAR_87 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f t))) x)) t))) -> (@IMAGE A B f (@INTERS A g)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
Axiom thm_IMAGE_INTER_SATURATED : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@subset A (@GSPEC A (fun GEN_PVAR_88 : A => exists x : A, @SETSPEC A GEN_PVAR_88 (@IN B (f x) (@IMAGE A B f s)) x)) s) \/ (@subset A (@GSPEC A (fun GEN_PVAR_89 : A => exists x : A, @SETSPEC A GEN_PVAR_89 (@IN B (f x) (@IMAGE A B f t)) x)) t)) -> (@IMAGE A B f (@setI A s t)) = (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_INTERS_SATURATED : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (g = (@set0 (A -> Prop)))) /\ (forall t : A -> Prop, (@IN (A -> Prop) t (@DELETE (A -> Prop) g s)) -> @subset A (@GSPEC A (fun GEN_PVAR_90 : A => exists x : A, @SETSPEC A GEN_PVAR_90 (@IN B (f x) (@IMAGE A B f t)) x)) t)) -> (@IMAGE A B f (@INTERS A g)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
Axiom thm_FINITE_INDUCT_STRONG : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@set0 A)) /\ (forall x : A, forall s : A -> Prop, ((P s) /\ ((~ (@IN A x s)) /\ (@finite_set A s))) -> P (@INSERT A x s))) -> forall s : A -> Prop, (@finite_set A s) -> P s.
Axiom thm_INJECTIVE_ON_ALT : forall {A B : Type'}, forall P : A -> Prop, forall f : A -> B, (forall x : A, forall y : A, ((P x) /\ ((P y) /\ ((f x) = (f y)))) -> x = y) = (forall x : A, forall y : A, ((P x) /\ (P y)) -> ((f x) = (f y)) = (x = y)).
Axiom thm_INJECTIVE_ALT : forall {A B : Type'}, forall f : A -> B, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) = (forall x : A, forall y : A, ((f x) = (f y)) = (x = y)).
Axiom thm_SURJECTIVE_ON_RIGHT_INVERSE : forall {A B : Type'} (s : A -> Prop), forall f : A -> B, forall t : B -> Prop, (forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (exists g : B -> A, forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)).
Axiom thm_INJECTIVE_ON_LEFT_INVERSE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) = (exists g : B -> A, forall x : A, (@IN A x s) -> (g (f x)) = x).
Axiom thm_BIJECTIVE_ON_LEFT_RIGHT_INVERSE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, (forall x : A, (@IN A x s) -> @IN B (f x) t) -> ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y))) = (exists g : B -> A, (forall y : B, (@IN B y t) -> @IN A (g y) s) /\ ((forall y : B, (@IN B y t) -> (f (g y)) = y) /\ (forall x : A, (@IN A x s) -> (g (f x)) = x))).
Axiom thm_SURJECTIVE_RIGHT_INVERSE : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (exists g : B -> A, forall y : B, (f (g y)) = y).
Axiom thm_INJECTIVE_LEFT_INVERSE : forall {A B : Type'}, forall f : A -> B, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) = (exists g : B -> A, forall x : A, (g (f x)) = x).
Axiom thm_BIJECTIVE_LEFT_RIGHT_INVERSE : forall {A B : Type'}, forall f : A -> B, ((forall x : A, forall y : A, ((f x) = (f y)) -> x = y) /\ (forall y : B, exists x : A, (f x) = y)) = (exists g : B -> A, (forall y : B, (f (g y)) = y) /\ (forall x : A, (g (f x)) = x)).
Axiom thm_FUNCTION_FACTORS_LEFT_GEN : forall {A B C : Type'}, forall P : A -> Prop, forall f : A -> B, forall g : A -> C, (forall x : A, forall y : A, ((P x) /\ ((P y) /\ ((g x) = (g y)))) -> (f x) = (f y)) = (exists h : C -> B, forall x : A, (P x) -> (f x) = (h (g x))).
Axiom thm_FUNCTION_FACTORS_LEFT : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, (forall x : A, forall y : A, ((g x) = (g y)) -> (f x) = (f y)) = (exists h : C -> B, f = (@o A C B h g)).
Axiom thm_FUNCTION_FACTORS_RIGHT_GEN : forall {A B C : Type'}, forall P : A -> Prop, forall f : A -> C, forall g : B -> C, (forall x : A, (P x) -> exists y : B, (g y) = (f x)) = (exists h : A -> B, forall x : A, (P x) -> (f x) = (g (h x))).
Axiom thm_FUNCTION_FACTORS_RIGHT : forall {A B C : Type'}, forall f : A -> C, forall g : B -> C, (forall x : A, exists y : B, (g y) = (f x)) = (exists h : A -> B, f = (@o A B C g h)).
Axiom thm_SURJECTIVE_FORALL_THM : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (forall x : A, P (f x)) = (forall y : B, P y)).
Axiom thm_SURJECTIVE_EXISTS_THM : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (exists x : A, P (f x)) = (exists y : B, P y)).
Axiom thm_SURJECTIVE_IMAGE_THM : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (@IMAGE A B f (@GSPEC A (fun GEN_PVAR_91 : A => exists x : A, @SETSPEC A GEN_PVAR_91 (P (f x)) x))) = (@GSPEC B (fun GEN_PVAR_92 : B => exists x : B, @SETSPEC B GEN_PVAR_92 (P x) x))).
Axiom thm_IMAGE_INJECTIVE_IMAGE_OF_SUBSET : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, exists t : A -> Prop, (@subset A t s) /\ (((@IMAGE A B f s) = (@IMAGE A B f t)) /\ (forall x : A, forall y : A, ((@IN A x t) /\ ((@IN A y t) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_FINITE_EMPTY : forall {A : Type'}, @finite_set A (@set0 A).
Axiom thm_FINITE_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ (@subset A s t)) -> @finite_set A s.
Axiom thm_FINITE_RESTRICT : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, (@finite_set A s) -> @finite_set A (@GSPEC A (fun GEN_PVAR_93 : A => exists x : A, @SETSPEC A GEN_PVAR_93 ((@IN A x s) /\ (P x)) x)).
Axiom thm_FINITE_UNION_IMP : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> @finite_set A (@setU A s t).
Axiom thm_FINITE_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@finite_set A (@setU A s t)) = ((@finite_set A s) /\ (@finite_set A t)).
Axiom thm_FINITE_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) \/ (@finite_set A t)) -> @finite_set A (@setI A s t).
Axiom thm_FINITE_INSERT : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@finite_set A (@INSERT A x s)) = (@finite_set A s).
Axiom thm_FINITE_SING : forall {A : Type'}, forall a : A, @finite_set A (@INSERT A a (@set0 A)).
Axiom thm_FINITE_DELETE_IMP : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@finite_set A s) -> @finite_set A (@DELETE A s x).
Axiom thm_FINITE_DELETE : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@finite_set A (@DELETE A s x)) = (@finite_set A s).
Axiom thm_FINITE_FINITE_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@finite_set (A -> Prop) s) -> (@finite_set A (@UNIONS A s)) = (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t).
Axiom thm_FINITE_IMAGE_EXPAND : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> @finite_set B (@GSPEC B (fun GEN_PVAR_96 : B => exists y : B, @SETSPEC B GEN_PVAR_96 (exists x : A, (@IN A x s) /\ (y = (f x))) y)).
Axiom thm_FINITE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> @finite_set B (@IMAGE A B f s).
Axiom thm_FINITE_IMAGE_INJ_GENERAL : forall {A B : Type'}, forall f : A -> B, forall A' : B -> Prop, forall s : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@finite_set B A')) -> @finite_set A (@GSPEC A (fun GEN_PVAR_97 : A => exists x : A, @SETSPEC A GEN_PVAR_97 ((@IN A x s) /\ (@IN B (f x) A')) x)).
Axiom thm_FINITE_FINITE_PREIMAGE_GENERAL : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set B t) /\ (forall y : B, (@IN B y t) -> @finite_set A (@GSPEC A (fun GEN_PVAR_100 : A => exists x : A, @SETSPEC A GEN_PVAR_100 ((@IN A x s) /\ ((f x) = y)) x)))) -> @finite_set A (@GSPEC A (fun GEN_PVAR_101 : A => exists x : A, @SETSPEC A GEN_PVAR_101 ((@IN A x s) /\ (@IN B (f x) t)) x)).
Axiom thm_FINITE_FINITE_PREIMAGE : forall {A B : Type'}, forall f : A -> B, forall t : B -> Prop, ((@finite_set B t) /\ (forall y : B, (@IN B y t) -> @finite_set A (@GSPEC A (fun GEN_PVAR_102 : A => exists x : A, @SETSPEC A GEN_PVAR_102 ((f x) = y) x)))) -> @finite_set A (@GSPEC A (fun GEN_PVAR_103 : A => exists x : A, @SETSPEC A GEN_PVAR_103 (@IN B (f x) t) x)).
Axiom thm_FINITE_IMAGE_INJ_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@finite_set B (@IMAGE A B f s)) = (@finite_set A s).
Axiom thm_FINITE_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall A' : B -> Prop, ((forall x : A, forall y : A, ((f x) = (f y)) -> x = y) /\ (@finite_set B A')) -> @finite_set A (@GSPEC A (fun GEN_PVAR_104 : A => exists x : A, @SETSPEC A GEN_PVAR_104 (@IN B (f x) A') x)).
Axiom thm_FINITE_IMAGE_GEN : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, forall s : A -> Prop, forall t : B -> Prop, ((@subset B (@IMAGE A B f s) t) /\ ((@finite_set B t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> (g x) = (g y)))) -> @finite_set C (@IMAGE A C g s).
Axiom thm_INFINITE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((@INFINITE A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)) -> @INFINITE B (@IMAGE A B f s).
Axiom thm_INFINITE_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) -> forall s : A -> Prop, (@INFINITE A s) -> @INFINITE B (@IMAGE A B f s).
Axiom thm_INFINITE_NONEMPTY : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) -> ~ (s = (@set0 A)).
Axiom thm_INFINITE_DIFF_FINITE : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@INFINITE A s) /\ (@finite_set A t)) -> @INFINITE A (@setD A s t).
Axiom thm_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : B -> Prop, forall t : A -> Prop, (@subset B s (@IMAGE A B f t)) = (exists u : A -> Prop, (@subset A u t) /\ ((forall x : A, forall y : A, ((@IN A x u) /\ (@IN A y u)) -> ((f x) = (f y)) = (x = y)) /\ (s = (@IMAGE A B f u)))).
Axiom thm_SUBSET_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : B -> Prop, forall t : A -> Prop, (@subset B s (@IMAGE A B f t)) = (exists u : A -> Prop, (@subset A u t) /\ (s = (@IMAGE A B f u))).
Axiom thm_EXISTS_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@subset B t (@IMAGE A B f s)) /\ (P t)) = (exists t : A -> Prop, (@subset A t s) /\ (P (@IMAGE A B f t))).
Axiom thm_FORALL_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, (@subset B t (@IMAGE A B f s)) -> P t) = (forall t : A -> Prop, (@subset A t s) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@subset B t (@IMAGE A B f s)) /\ (P t)) = (exists t : A -> Prop, (@subset A t s) /\ ((forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE A B f t)))).
Axiom thm_FORALL_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, (@subset B t (@IMAGE A B f s)) -> P t) = (forall t : A -> Prop, ((@subset A t s) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y))) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_FINITE_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@finite_set B t) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t))) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ ((forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE A B f t))))).
Axiom thm_FORALL_FINITE_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ ((@subset A t s) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)))) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_FINITE_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@finite_set B t) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t))) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (P (@IMAGE A B f t)))).
Axiom thm_FORALL_FINITE_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ (@subset A t s)) -> P (@IMAGE A B f t)).
Axiom thm_FINITE_SUBSET_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) = (exists s' : A -> Prop, (@finite_set A s') /\ ((@subset A s' s) /\ (t = (@IMAGE A B f s')))).
Axiom thm_FINITE_SUBSET_IMAGE_IMP : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) -> exists s' : A -> Prop, (@finite_set A s') /\ ((@subset A s' s) /\ (@subset B t (@IMAGE A B f s'))).
Axiom thm_FINITE_IMAGE_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set B (@IMAGE A B f s)) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ ((@IMAGE A B f s) = (@IMAGE A B f t)))).
Axiom thm_FINITE_IMAGE_EQ_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set B (@IMAGE A B f s)) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (((@IMAGE A B f s) = (@IMAGE A B f t)) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y))))).
Axiom thm_FINITE_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@finite_set A s) -> @finite_set A (@setD A s t).
Axiom thm_INFINITE_SUPERSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@INFINITE A s) /\ (@subset A s t)) -> @INFINITE A t.
Axiom thm_FINITE_TRANSITIVITY_CHAIN : forall {A : Type'}, forall R' : A -> A -> Prop, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, ~ (R' x x)) /\ ((forall x : A, forall y : A, forall z : A, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall x : A, (@IN A x s) -> exists y : A, (@IN A y s) /\ (R' x y))))) -> s = (@set0 A).
Axiom thm_UNIONS_MAXIMAL_SETS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, (@finite_set (A -> Prop) f) -> (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_106 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_106 ((@IN (A -> Prop) t f) /\ (forall u : A -> Prop, (@IN (A -> Prop) u f) -> ~ (@proper A t u))) t))) = (@UNIONS A f).
Axiom thm_FINITE_SUBSET_UNIONS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((@finite_set A s) /\ (@subset A s (@UNIONS A f))) -> exists f' : (A -> Prop) -> Prop, (@finite_set (A -> Prop) f') /\ ((@subset (A -> Prop) f' f) /\ (@subset A s (@UNIONS A f'))).
Axiom thm_UNIONS_IN_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) f) /\ ((~ (f = (@set0 (A -> Prop)))) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s f) /\ (@IN (A -> Prop) t f)) -> (@subset A s t) \/ (@subset A t s)))) -> @IN (A -> Prop) (@UNIONS A f) f.
Axiom thm_INTERS_IN_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) f) /\ ((~ (f = (@set0 (A -> Prop)))) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s f) /\ (@IN (A -> Prop) t f)) -> (@subset A s t) \/ (@subset A t s)))) -> @IN (A -> Prop) (@INTERS A f) f.
Axiom thm_FINITE_SUBSET_UNIONS_DIRECTED_EQ : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (f = (@set0 (A -> Prop)))) /\ ((forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> exists v : A -> Prop, (@IN (A -> Prop) v f) /\ ((@subset A t v) /\ (@subset A u v))) /\ (@finite_set A s))) -> (@subset A s (@UNIONS A f)) = (exists t : A -> Prop, (@IN (A -> Prop) t f) /\ (@subset A s t)).
Axiom thm_FINITE_SUBSET_UNIONS_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((@finite_set A s) /\ ((@subset A s (@UNIONS A f)) /\ ((~ (f = (@set0 (A -> Prop)))) /\ (forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> (@subset A t u) \/ (@subset A u t))))) -> exists t : A -> Prop, (@IN (A -> Prop) t f) /\ (@subset A s t).
Axiom thm_FINREC : forall {A B : Type'} (b : B) (s : A -> Prop) (n : N) (a : B) (f : A -> B -> B), ((@FINREC A B f b s a N0) = ((s = (@set0 A)) /\ (a = b))) /\ ((@FINREC A B f b s a (N.succ n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((@FINREC A B f b (@DELETE A s x) c n) /\ (a = (f x c))))).
Axiom thm_FINREC_1_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, forall s : A -> Prop, forall a : B, (@FINREC A B f b s a (N.succ N0)) = (exists x : A, (s = (@INSERT A x (@set0 A))) /\ (a = (f x b))).
Axiom thm_FINREC_SUC_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> forall n : N, forall s : A -> Prop, forall z : B, (@FINREC A B f b s z (N.succ n)) -> forall x : A, (@IN A x s) -> exists w : B, (@FINREC A B f b (@DELETE A s x) w n) /\ (z = (f x w)).
Axiom thm_FINREC_UNIQUE_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> forall n1 : N, forall n2 : N, forall s : A -> Prop, forall a1 : B, forall a2 : B, ((@FINREC A B f b s a1 n1) /\ (@FINREC A B f b s a2 n2)) -> (a1 = a2) /\ (n1 = n2).
Axiom thm_FINREC_EXISTS_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, forall s : A -> Prop, (@finite_set A s) -> exists a : B, exists n : N, @FINREC A B f b s a n.
Axiom thm_FINREC_FUN_LEMMA : forall {A B C : Type'}, forall P : A -> Prop, forall R' : A -> B -> C -> Prop, ((forall s : A, (P s) -> exists a : B, exists n : C, R' s a n) /\ (forall n1 : C, forall n2 : C, forall s : A, forall a1 : B, forall a2 : B, ((R' s a1 n1) /\ (R' s a2 n2)) -> (a1 = a2) /\ (n1 = n2))) -> exists f : A -> B, forall s : A, forall a : B, (P s) -> (exists n : C, R' s a n) = ((f s) = a).
Axiom thm_FINREC_FUN : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> exists g : (A -> Prop) -> B, ((g (@set0 A)) = b) /\ (forall s : A -> Prop, forall x : A, ((@finite_set A s) /\ (@IN A x s)) -> (g s) = (f x (g (@DELETE A s x)))).
Axiom thm_SET_RECURSION_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> exists g : (A -> Prop) -> B, ((g (@set0 A)) = b) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (g (@INSERT A x s)) = (@COND B (@IN A x s) (g s) (f x (g s)))).
Axiom thm_ITSET : forall {A B : Type'}, forall b : B, forall f : A -> B -> B, forall s : A -> Prop, (@fold_set A B f s b) = (@ε ((A -> Prop) -> B) (fun g : (A -> Prop) -> B => ((g (@set0 A)) = b) /\ (forall x : A, forall s' : A -> Prop, (@finite_set A s') -> (g (@INSERT A x s')) = (@COND B (@IN A x s') (g s') (f x (g s'))))) s).
Axiom thm_FINITE_RECURSION : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> ((@fold_set A B f (@set0 A) b) = b) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@fold_set A B f (@INSERT A x s) b) = (@COND B (@IN A x s) (@fold_set A B f s b) (f x (@fold_set A B f s b)))).
Axiom thm_FINITE_RECURSION_DELETE : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> ((@fold_set A B f (@set0 A) b) = b) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@fold_set A B f s b) = (@COND B (@IN A x s) (f x (@fold_set A B f (@DELETE A s x) b)) (@fold_set A B f (@DELETE A s x) b))).
Axiom thm_ITSET_EQ : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B -> B, forall g : A -> B -> B, forall b : B, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> (f x) = (g x)) /\ ((forall x : A, forall y : A, forall s' : B, (~ (x = y)) -> (f x (f y s')) = (f y (f x s'))) /\ (forall x : A, forall y : A, forall s' : B, (~ (x = y)) -> (g x (g y s')) = (g y (g x s')))))) -> (@fold_set A B f s b) = (@fold_set A B g s b).
Axiom thm_CARD : forall {A : Type'}, forall s : A -> Prop, (@card A s) = (@fold_set A N (fun x : A => fun n : N => N.succ n) s N0).
Axiom thm_CARD_CLAUSES : forall {A : Type'}, ((@card A (@set0 A)) = N0) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@card A (@INSERT A x s)) = (@COND N (@IN A x s) (@card A s) (N.succ (@card A s)))).
Axiom thm_CARD_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ ((@setI A s t) = (@set0 A)))) -> (@card A (@setU A s t)) = (N.add (@card A s) (@card A t)).
Axiom thm_CARD_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@card A (@DELETE A s x)) = (@COND N (@IN A x s) (N.sub (@card A s) ((BIT1 N0))) (@card A s)).
Axiom thm_CARD_UNION_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@finite_set A u) /\ (((@setI A s t) = (@set0 A)) /\ ((@setU A s t) = u))) -> (N.add (@card A s) (@card A t)) = (@card A u).
Axiom thm_CARD_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@subset A t s)) -> (@card A (@setD A s t)) = (N.sub (@card A s) (@card A t)).
Axiom thm_CARD_EQ_0 : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> ((@card A s) = N0) = (s = (@set0 A)).
Axiom thm_CARD_SING : forall {A : Type'}, forall a : A, (@card A (@INSERT A a (@set0 A))) = ((BIT1 N0)).
Axiom thm_FINITE_INDUCT_DELETE : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@set0 A)) /\ (forall s : A -> Prop, ((@finite_set A s) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ ((P (@DELETE A s x)) -> P s))) -> forall s : A -> Prop, (@finite_set A s) -> P s.
Axiom thm_HAS_SIZE : forall {A : Type'}, forall s : A -> Prop, forall n : N, (@HAS_SIZE A s n) = ((@finite_set A s) /\ ((@card A s) = n)).
Axiom thm_HAS_SIZE_CARD : forall {A : Type'}, forall s : A -> Prop, forall n : N, (@HAS_SIZE A s n) -> (@card A s) = n.
Axiom thm_HAS_SIZE_0 : forall {A : Type'}, forall s : A -> Prop, (@HAS_SIZE A s N0) = (s = (@set0 A)).
Axiom thm_HAS_SIZE_SUC : forall {A : Type'}, forall s : A -> Prop, forall n : N, (@HAS_SIZE A s (N.succ n)) = ((~ (s = (@set0 A))) /\ (forall a : A, (@IN A a s) -> @HAS_SIZE A (@DELETE A s a) n)).
Axiom thm_HAS_SIZE_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : N, forall n : N, ((@HAS_SIZE A s m) /\ ((@HAS_SIZE A t n) /\ (@DISJOINT A s t))) -> @HAS_SIZE A (@setU A s t) (N.add m n).
Axiom thm_HAS_SIZE_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : N, forall n : N, ((@HAS_SIZE A s m) /\ ((@HAS_SIZE A t n) /\ (@subset A t s))) -> @HAS_SIZE A (@setD A s t) (N.sub m n).
Axiom thm_HAS_SIZE_UNIONS : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : N, forall n : N, ((@HAS_SIZE A s m) /\ ((forall x : A, (@IN A x s) -> @HAS_SIZE B (t x) n) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ (~ (x = y)))) -> @DISJOINT B (t x) (t y)))) -> @HAS_SIZE B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_109 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_109 (@IN A x s) (t x)))) (N.mul m n).
Axiom thm_FINITE_HAS_SIZE : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) = (@HAS_SIZE A s (@card A s)).
Axiom thm_HAS_SIZE_CLAUSES : forall {A : Type'} (n : N) (s : A -> Prop), ((@HAS_SIZE A s N0) = (s = (@set0 A))) /\ ((@HAS_SIZE A s (N.succ n)) = (exists a : A, exists t : A -> Prop, (@HAS_SIZE A t n) /\ ((~ (@IN A a t)) /\ (s = (@INSERT A a t))))).
Axiom thm_CARD_SUBSET_EQ : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@finite_set A b) /\ ((@subset A a b) /\ ((@card A a) = (@card A b)))) -> a = b.
Axiom thm_CARD_SUBSET : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@subset A a b) /\ (@finite_set A b)) -> N.le (@card A a) (@card A b).
Axiom thm_CARD_SUBSET_LE : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@finite_set A b) /\ ((@subset A a b) /\ (N.le (@card A b) (@card A a)))) -> a = b.
Axiom thm_SUBSET_CARD_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ (@subset A s t)) -> ((@card A s) = (@card A t)) = (s = t).
Axiom thm_FINITE_CARD_LE_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall n : N, ((@subset A s t) /\ ((@finite_set A t) /\ (N.le (@card A t) n))) -> (@finite_set A s) /\ (N.le (@card A s) n).
Axiom thm_CARD_PSUBSET : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@proper A a b) /\ (@finite_set A b)) -> N.lt (@card A a) (@card A b).
Axiom thm_CARD_PSUBSET_IMP : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@subset A a b) /\ (~ ((@card A a) = (@card A b)))) -> @proper A a b.
Axiom thm_CARD_PSUBSET_EQ : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@finite_set A b) /\ (@subset A a b)) -> (@proper A a b) = (N.lt (@card A a) (@card A b)).
Axiom thm_CARD_UNION_LE : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> N.le (@card A (@setU A s t)) (N.add (@card A s) (@card A t)).
Axiom thm_FINITE_CARD_LE_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : N, forall n : N, (((@finite_set A s) /\ (N.le (@card A s) m)) /\ ((@finite_set A t) /\ (N.le (@card A t) n))) -> (@finite_set A (@setU A s t)) /\ (N.le (@card A (@setU A s t)) (N.add m n)).
Axiom thm_CARD_UNIONS_LE : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : N, forall n : N, ((@HAS_SIZE A s m) /\ (forall x : A, (@IN A x s) -> (@finite_set B (t x)) /\ (N.le (@card B (t x)) n))) -> N.le (@card B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_115 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_115 (@IN A x s) (t x))))) (N.mul m n).
Axiom thm_CARD_UNION_GEN : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> (@card A (@setU A s t)) = (N.sub (N.add (@card A s) (@card A t)) (@card A (@setI A s t))).
Axiom thm_CARD_UNION_OVERLAP_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> ((@card A (@setU A s t)) = (N.add (@card A s) (@card A t))) = ((@setI A s t) = (@set0 A)).
Axiom thm_CARD_UNION_OVERLAP : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (N.lt (@card A (@setU A s t)) (N.add (@card A s) (@card A t))))) -> ~ ((@setI A s t) = (@set0 A)).
Axiom thm_CARD_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@finite_set A s)) -> (@card B (@IMAGE A B f s)) = (@card A s).
Axiom thm_HAS_SIZE_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : N, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@HAS_SIZE A s n)) -> @HAS_SIZE B (@IMAGE A B f s) n.
Axiom thm_CARD_IMAGE_LE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> N.le (@card B (@IMAGE A B f s)) (@card A s).
Axiom thm_FINITE_CARD_LE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : N, ((@finite_set A s) /\ (N.le (@card A s) n)) -> (@finite_set B (@IMAGE A B f s)) /\ (N.le (@card B (@IMAGE A B f s)) n).
Axiom thm_CARD_IMAGE_INJ_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((f x) = y))))) -> (@card B t) = (@card A s).
Axiom thm_CARD_SUBSET_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : B -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ (@subset B s (@IMAGE A B f t))) -> N.le (@card B s) (@card A t).
Axiom thm_HAS_SIZE_IMAGE_INJ_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : N, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@HAS_SIZE B (@IMAGE A B f s) n) = (@HAS_SIZE A s n).
Axiom thm_CARD_IMAGE_EQ_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> ((@card B (@IMAGE A B f s)) = (@card A s)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_EXISTS_SMALL_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : N, (exists t : B -> Prop, (@finite_set B t) /\ ((N.lt (@card B t) n) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t)))) = (exists t : A -> Prop, (@finite_set A t) /\ ((N.lt (@card A t) n) /\ ((@subset A t s) /\ ((forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE A B f t)))))).
Axiom thm_FORALL_SMALL_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : N, (forall t : B -> Prop, ((@finite_set B t) /\ ((N.lt (@card B t) n) /\ (@subset B t (@IMAGE A B f s)))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ ((N.lt (@card A t) n) /\ ((@subset A t s) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y))))) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_SMALL_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : N, (exists t : B -> Prop, (@finite_set B t) /\ ((N.lt (@card B t) n) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t)))) = (exists t : A -> Prop, (@finite_set A t) /\ ((N.lt (@card A t) n) /\ ((@subset A t s) /\ (P (@IMAGE A B f t))))).
Axiom thm_FORALL_SMALL_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : N, (forall t : B -> Prop, ((@finite_set B t) /\ ((N.lt (@card B t) n) /\ (@subset B t (@IMAGE A B f s)))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ ((N.lt (@card A t) n) /\ (@subset A t s))) -> P (@IMAGE A B f t)).
Axiom thm_CARD_IMAGE_LE2 : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((g x) = (g y)))) -> (f x) = (f y))) -> N.le (@card B (@IMAGE A B f s)) (@card C (@IMAGE A C g s)).
Axiom thm_CARD_IMAGE_LT2 : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((g x) = (g y)))) -> (f x) = (f y)) /\ (~ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> (g x) = (g y))))) -> N.lt (@card B (@IMAGE A B f s)) (@card C (@IMAGE A C g s)).
Axiom thm_CHOOSE_SUBSET_STRONG : forall {A : Type'}, forall n : N, forall s : A -> Prop, ((@finite_set A s) -> N.le n (@card A s)) -> exists t : A -> Prop, (@subset A t s) /\ (@HAS_SIZE A t n).
Axiom thm_CHOOSE_SUBSET_EQ : forall {A : Type'}, forall n : N, forall s : A -> Prop, ((@finite_set A s) -> N.le n (@card A s)) = (exists t : A -> Prop, (@subset A t s) /\ (@HAS_SIZE A t n)).
Axiom thm_CHOOSE_SUBSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> forall n : N, (N.le n (@card A s)) -> exists t : A -> Prop, (@subset A t s) /\ (@HAS_SIZE A t n).
Axiom thm_CHOOSE_SUBSET_BETWEEN : forall {A : Type'}, forall n : N, forall s : A -> Prop, forall u : A -> Prop, ((@subset A s u) /\ ((@finite_set A s) /\ ((N.le (@card A s) n) /\ ((@finite_set A u) -> N.le n (@card A u))))) -> exists t : A -> Prop, (@subset A s t) /\ ((@subset A t u) /\ (@HAS_SIZE A t n)).
Axiom thm_CARD_LE_UNIONS_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall n : N, ((forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> (@subset A t u) \/ (@subset A u t)) /\ (forall t : A -> Prop, (@IN (A -> Prop) t f) -> (@finite_set A t) /\ (N.le (@card A t) n))) -> (@finite_set A (@UNIONS A f)) /\ (N.le (@card A (@UNIONS A f)) n).
Axiom thm_CARD_LE_1 : forall {A : Type'}, forall s : A -> Prop, ((@finite_set A s) /\ (N.le (@card A s) ((BIT1 N0)))) = (exists a : A, @subset A s (@INSERT A a (@set0 A))).
Axiom thm_INVOLUTION_EVEN_NOFIXPOINTS : forall {A : Type'}, forall f : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> (@IN A (f x) s) /\ ((~ ((f x) = x)) /\ ((f (f x)) = x)))) -> N.Even (@card A s).
Axiom thm_INVOLUTION_EVEN_FIXPOINTS : forall {A : Type'}, forall f : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> (@IN A (f x) s) /\ ((f (f x)) = x))) -> (N.Even (@card A (@GSPEC A (fun GEN_PVAR_120 : A => exists x : A, @SETSPEC A GEN_PVAR_120 ((@IN A x s) /\ ((f x) = x)) x)))) = (N.Even (@card A s)).
Axiom thm_HAS_SIZE_PRODUCT_DEPENDENT : forall {A B : Type'}, forall s : A -> Prop, forall m : N, forall t : A -> B -> Prop, forall n : N, ((@HAS_SIZE A s m) /\ (forall x : A, (@IN A x s) -> @HAS_SIZE B (t x) n)) -> @HAS_SIZE (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_123 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_123 ((@IN A x s) /\ (@IN B y (t x))) (@pair A B x y))) (N.mul m n).
Axiom thm_FINITE_PRODUCT_DEPENDENT : forall {A B C : Type'}, forall f : A -> B -> C, forall s : A -> Prop, forall t : A -> B -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @finite_set B (t x))) -> @finite_set C (@GSPEC C (fun GEN_PVAR_128 : C => exists x : A, exists y : B, @SETSPEC C GEN_PVAR_128 ((@IN A x s) /\ (@IN B y (t x))) (f x y))).
Axiom thm_FINITE_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_129 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_129 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y))).
Axiom thm_CARD_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@card (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_130 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_130 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y)))) = (N.mul (@card A s) (@card B t)).
Axiom thm_HAS_SIZE_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall m : N, forall t : B -> Prop, forall n : N, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_131 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_131 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y))) (N.mul m n).
Axiom thm_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@CROSS A B s t) = (@GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y))).
Axiom thm_IN_CROSS : forall {A B : Type'}, forall x : A, forall y : B, forall s : A -> Prop, forall t : B -> Prop, (@IN (prod A B) (@pair A B x y) (@CROSS A B s t)) = ((@IN A x s) /\ (@IN B y t)).
Axiom thm_HAS_SIZE_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall m : N, forall n : N, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (prod A B) (@CROSS A B s t) (N.mul m n).
Axiom thm_FINITE_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (prod A B) (@CROSS A B s t).
Axiom thm_CARD_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@card (prod A B) (@CROSS A B s t)) = (N.mul (@card A s) (@card B t)).
Axiom thm_CROSS_EQ_EMPTY : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@CROSS A B s t) = (@set0 (prod A B))) = ((s = (@set0 A)) \/ (t = (@set0 B))).
Axiom thm_CROSS_EMPTY : forall {_98014 _98027 A B : Type'}, (forall s : A -> Prop, (@CROSS A _98014 s (@set0 _98014)) = (@set0 (prod A _98014))) /\ (forall t : B -> Prop, (@CROSS _98027 B (@set0 _98027) t) = (@set0 (prod _98027 B))).
Axiom thm_CROSS_SING : forall {A B : Type'}, forall x : A, forall y : B, (@CROSS A B (@INSERT A x (@set0 A)) (@INSERT B y (@set0 B))) = (@INSERT (prod A B) (@pair A B x y) (@set0 (prod A B))).
Axiom thm_CROSS_UNIV : forall {A B : Type'}, (@CROSS A B (@setT A) (@setT B)) = (@setT (prod A B)).
Axiom thm_FINITE_CROSS_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@finite_set (prod A B) (@CROSS A B s t)) = ((s = (@set0 A)) \/ ((t = (@set0 B)) \/ ((@finite_set A s) /\ (@finite_set B t)))).
Axiom thm_INFINITE_CROSS_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@INFINITE (prod A B) (@CROSS A B s t)) = (((~ (s = (@set0 A))) /\ (@INFINITE B t)) \/ ((@INFINITE A s) /\ (~ (t = (@set0 B))))).
Axiom thm_FINITE_CROSS_UNIV : forall {A B : Type'}, (@finite_set (prod A B) (@setT (prod A B))) = ((@finite_set A (@setT A)) /\ (@finite_set B (@setT B))).
Axiom thm_INFINITE_CROSS_UNIV : forall {A B : Type'}, (@INFINITE (prod A B) (@setT (prod A B))) = ((@INFINITE A (@setT A)) \/ (@INFINITE B (@setT B))).
Axiom thm_FINITE_UNIV_PAIR : forall {A : Type'}, (@finite_set (prod A A) (@setT (prod A A))) = (@finite_set A (@setT A)).
Axiom thm_INFINITE_UNIV_PAIR : forall {A : Type'}, (@INFINITE (prod A A) (@setT (prod A A))) = (@INFINITE A (@setT A)).
Axiom thm_FORALL_IN_CROSS : forall {A B : Type'}, forall P : (prod A B) -> Prop, forall s : A -> Prop, forall t : B -> Prop, (forall z : prod A B, (@IN (prod A B) z (@CROSS A B s t)) -> P z) = (forall x : A, forall y : B, ((@IN A x s) /\ (@IN B y t)) -> P (@pair A B x y)).
Axiom thm_EXISTS_IN_CROSS : forall {A B : Type'}, forall P : (prod A B) -> Prop, forall s : A -> Prop, forall t : B -> Prop, (exists z : prod A B, (@IN (prod A B) z (@CROSS A B s t)) /\ (P z)) = (exists x : A, exists y : B, (@IN A x s) /\ ((@IN B y t) /\ (P (@pair A B x y)))).
Axiom thm_SUBSET_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall s' : A -> Prop, forall t' : B -> Prop, (@subset (prod A B) (@CROSS A B s t) (@CROSS A B s' t')) = ((s = (@set0 A)) \/ ((t = (@set0 B)) \/ ((@subset A s s') /\ (@subset B t t')))).
Axiom thm_CROSS_MONO : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall s' : A -> Prop, forall t' : B -> Prop, ((@subset A s s') /\ (@subset B t t')) -> @subset (prod A B) (@CROSS A B s t) (@CROSS A B s' t').
Axiom thm_CROSS_EQ : forall {A B : Type'}, forall s : A -> Prop, forall s' : A -> Prop, forall t : B -> Prop, forall t' : B -> Prop, ((@CROSS A B s t) = (@CROSS A B s' t')) = ((((s = (@set0 A)) \/ (t = (@set0 B))) /\ ((s' = (@set0 A)) \/ (t' = (@set0 B)))) \/ ((s = s') /\ (t = t'))).
Axiom thm_IMAGE_FST_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@IMAGE (prod A B) A (@fst A B) (@CROSS A B s t)) = (@COND (A -> Prop) (t = (@set0 B)) (@set0 A) s).
Axiom thm_IMAGE_SND_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@IMAGE (prod A B) B (@snd A B) (@CROSS A B s t)) = (@COND (B -> Prop) (s = (@set0 A)) (@set0 B) t).
Axiom thm_IMAGE_PAIRED_CROSS : forall {A B C D : Type'}, forall f : A -> B, forall g : C -> D, forall s : A -> Prop, forall t : C -> Prop, (@IMAGE (prod A C) (prod B D) (@ε ((prod A C) -> prod B D) (fun f' : (prod A C) -> prod B D => forall x : A, forall y : C, @eq (prod B D) (f' (@pair A C x y)) (@pair B D (f x) (g y)))) (@CROSS A C s t)) = (@CROSS B D (@IMAGE A B f s) (@IMAGE C D g t)).
Axiom thm_CROSS_INTER : forall {A B : Type'}, (forall s : A -> Prop, forall t : B -> Prop, forall u : B -> Prop, (@CROSS A B s (@setI B t u)) = (@setI (prod A B) (@CROSS A B s t) (@CROSS A B s u))) /\ (forall s : A -> Prop, forall t : A -> Prop, forall u : B -> Prop, (@CROSS A B (@setI A s t) u) = (@setI (prod A B) (@CROSS A B s u) (@CROSS A B t u))).
Axiom thm_CROSS_UNION : forall {A B : Type'}, (forall s : A -> Prop, forall t : B -> Prop, forall u : B -> Prop, (@CROSS A B s (@setU B t u)) = (@setU (prod A B) (@CROSS A B s t) (@CROSS A B s u))) /\ (forall s : A -> Prop, forall t : A -> Prop, forall u : B -> Prop, (@CROSS A B (@setU A s t) u) = (@setU (prod A B) (@CROSS A B s u) (@CROSS A B t u))).
Axiom thm_CROSS_DIFF : forall {A B : Type'}, (forall s : A -> Prop, forall t : B -> Prop, forall u : B -> Prop, (@CROSS A B s (@setD B t u)) = (@setD (prod A B) (@CROSS A B s t) (@CROSS A B s u))) /\ (forall s : A -> Prop, forall t : A -> Prop, forall u : B -> Prop, (@CROSS A B (@setD A s t) u) = (@setD (prod A B) (@CROSS A B s u) (@CROSS A B t u))).
Axiom thm_INTER_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall s' : A -> Prop, forall t : B -> Prop, forall t' : B -> Prop, (@setI (prod A B) (@CROSS A B s t) (@CROSS A B s' t')) = (@CROSS A B (@setI A s s') (@setI B t t')).
Axiom thm_CROSS_UNIONS : forall {A B : Type'}, (forall s : A -> Prop, forall f : (A -> Prop) -> Prop, (@CROSS A A s (@UNIONS A f)) = (@UNIONS (prod A A) (@GSPEC ((prod A A) -> Prop) (fun GEN_PVAR_134 : (prod A A) -> Prop => exists t : A -> Prop, @SETSPEC ((prod A A) -> Prop) GEN_PVAR_134 (@IN (A -> Prop) t f) (@CROSS A A s t))))) /\ (forall f : (A -> Prop) -> Prop, forall t : B -> Prop, (@CROSS A B (@UNIONS A f) t) = (@UNIONS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_135 : (prod A B) -> Prop => exists s : A -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_135 (@IN (A -> Prop) s f) (@CROSS A B s t))))).
Axiom thm_CROSS_UNIONS_UNIONS : forall {A B : Type'}, forall f : (A -> Prop) -> Prop, forall g : (B -> Prop) -> Prop, (@CROSS A B (@UNIONS A f) (@UNIONS B g)) = (@UNIONS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_133 : (prod A B) -> Prop => exists s : A -> Prop, exists t : B -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_133 ((@IN (A -> Prop) s f) /\ (@IN (B -> Prop) t g)) (@CROSS A B s t)))).
Axiom thm_CROSS_INTERS : forall {A B : Type'}, (forall s : A -> Prop, forall f : (A -> Prop) -> Prop, (@CROSS A A s (@INTERS A f)) = (@COND ((prod A A) -> Prop) (f = (@set0 (A -> Prop))) (@CROSS A A s (@setT A)) (@INTERS (prod A A) (@GSPEC ((prod A A) -> Prop) (fun GEN_PVAR_139 : (prod A A) -> Prop => exists t : A -> Prop, @SETSPEC ((prod A A) -> Prop) GEN_PVAR_139 (@IN (A -> Prop) t f) (@CROSS A A s t)))))) /\ (forall f : (A -> Prop) -> Prop, forall t : B -> Prop, (@CROSS A B (@INTERS A f) t) = (@COND ((prod A B) -> Prop) (f = (@set0 (A -> Prop))) (@CROSS A B (@setT A) t) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_140 : (prod A B) -> Prop => exists s : A -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_140 (@IN (A -> Prop) s f) (@CROSS A B s t)))))).
Axiom thm_CROSS_INTERS_INTERS : forall {A B : Type'}, forall f : (A -> Prop) -> Prop, forall g : (B -> Prop) -> Prop, (@CROSS A B (@INTERS A f) (@INTERS B g)) = (@COND ((prod A B) -> Prop) (f = (@set0 (A -> Prop))) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_136 : (prod A B) -> Prop => exists t : B -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_136 (@IN (B -> Prop) t g) (@CROSS A B (@setT A) t)))) (@COND ((prod A B) -> Prop) (g = (@set0 (B -> Prop))) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_137 : (prod A B) -> Prop => exists s : A -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_137 (@IN (A -> Prop) s f) (@CROSS A B s (@setT B))))) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_138 : (prod A B) -> Prop => exists s : A -> Prop, exists t : B -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_138 ((@IN (A -> Prop) s f) /\ (@IN (B -> Prop) t g)) (@CROSS A B s t)))))).
Axiom thm_DISJOINT_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall s' : A -> Prop, forall t' : B -> Prop, (@DISJOINT (prod A B) (@CROSS A B s t) (@CROSS A B s' t')) = ((@DISJOINT A s s') \/ (@DISJOINT B t t')).
Axiom thm_ARB : forall {A : Type'}, (@ARB A) = (@ε A (fun x : A => False)).
Axiom thm_EXTENSIONAL : forall {A B : Type'}, forall s : A -> Prop, (@EXTENSIONAL A B s) = (@GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x s)) -> (f x) = (@ARB B)) f)).
Axiom thm_IN_EXTENSIONAL : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@IN (A -> B) f (@EXTENSIONAL A B s)) = (forall x : A, (~ (@IN A x s)) -> (f x) = (@ARB B)).
Axiom thm_IN_EXTENSIONAL_UNDEFINED : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, ((@IN (A -> B) f (@EXTENSIONAL A B s)) /\ (~ (@IN A x s))) -> (f x) = (@ARB B).
Axiom thm_EXTENSIONAL_EMPTY : forall {A B : Type'}, (@EXTENSIONAL A B (@set0 A)) = (@INSERT (A -> B) (fun x : A => @ARB B) (@set0 (A -> B))).
Axiom thm_EXTENSIONAL_UNIV : forall {A B : Type'}, forall f : A -> B, @EXTENSIONAL A B (@setT A) f.
Axiom thm_EXTENSIONAL_EQ : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@IN (A -> B) f (@EXTENSIONAL A B s)) /\ ((@IN (A -> B) g (@EXTENSIONAL A B s)) /\ (forall x : A, (@IN A x s) -> (f x) = (g x)))) -> f = g.
Axiom thm_RESTRICTION : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, (@RESTRICTION A B s f x) = (@COND B (@IN A x s) (f x) (@ARB B)).
Axiom thm_RESTRICTION_THM : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@RESTRICTION A B s f) = (fun x : A => @COND B (@IN A x s) (f x) (@ARB B)).
Axiom thm_RESTRICTION_DEFINED : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, (@IN A x s) -> (@RESTRICTION A B s f x) = (f x).
Axiom thm_RESTRICTION_UNDEFINED : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, (~ (@IN A x s)) -> (@RESTRICTION A B s f x) = (@ARB B).
Axiom thm_RESTRICTION_EQ : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, forall y : B, ((@IN A x s) /\ ((f x) = y)) -> (@RESTRICTION A B s f x) = y.
Axiom thm_RESTRICTION_IN_EXTENSIONAL : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, @IN (A -> B) (@RESTRICTION A B s f) (@EXTENSIONAL A B s).
Axiom thm_RESTRICTION_EXTENSION : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (forall x : A, (@IN A x s) -> (f x) = (g x)).
Axiom thm_RESTRICTION_FIXPOINT : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, ((@RESTRICTION A B s f) = f) = (@IN (A -> B) f (@EXTENSIONAL A B s)).
Axiom thm_RESTRICTION_UNIV : forall {A B : Type'}, forall f : A -> B, (@RESTRICTION A B (@setT A) f) = f.
Axiom thm_RESTRICTION_RESTRICTION : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> B, (@subset A s t) -> (@RESTRICTION A B s (@RESTRICTION A B t f)) = (@RESTRICTION A B s f).
Axiom thm_RESTRICTION_IDEMP : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@RESTRICTION A B s (@RESTRICTION A B s f)) = (@RESTRICTION A B s f).
Axiom thm_IMAGE_RESTRICTION : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) -> (@IMAGE A B (@RESTRICTION A B t f) s) = (@IMAGE A B f s).
Axiom thm_RESTRICTION_COMPOSE_RIGHT : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (@RESTRICTION A C s (@o A B C g (@RESTRICTION A B s f))) = (@RESTRICTION A C s (@o A B C g f)).
Axiom thm_RESTRICTION_COMPOSE_LEFT : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, forall t : B -> Prop, (@subset B (@IMAGE A B f s) t) -> (@RESTRICTION A C s (@o A B C (@RESTRICTION B C t g) f)) = (@RESTRICTION A C s (@o A B C g f)).
Axiom thm_RESTRICTION_COMPOSE : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, forall t : B -> Prop, (@subset B (@IMAGE A B f s) t) -> (@RESTRICTION A C s (@o A B C (@RESTRICTION B C t g) (@RESTRICTION A B s f))) = (@RESTRICTION A C s (@o A B C g f)).
Axiom thm_RESTRICTION_UNIQUE : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@RESTRICTION A B s f) = g) = ((@EXTENSIONAL A B s g) /\ (forall x : A, (@IN A x s) -> (f x) = (g x))).
Axiom thm_RESTRICTION_UNIQUE_ALT : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, (f = (@RESTRICTION A B s g)) = ((@EXTENSIONAL A B s f) /\ (forall x : A, (@IN A x s) -> (f x) = (g x))).
Axiom thm_cartesian_product : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A k f) /\ (forall i : K, (@IN K i k) -> @IN A (f i) (s i))) f)).
Axiom thm_IN_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, (@IN (K -> A) x (@cartesian_product A K k s)) = ((@EXTENSIONAL K A k x) /\ (forall i : K, (@IN K i k) -> @IN A (x i) (s i))).
Axiom thm_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_143 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_143 (forall i : K, @IN A (f i) (@COND (A -> Prop) (@IN K i k) (s i) (@INSERT A (@ARB A) (@set0 A)))) f)).
Axiom thm_RESTRICTION_IN_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall f : K -> A, (@IN (K -> A) (@RESTRICTION K A k f) (@cartesian_product A K k s)) = (forall i : K, (@IN K i k) -> @IN A (f i) (s i)).
Axiom thm_CARTESIAN_PRODUCT_AS_RESTRICTIONS : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_144 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_144 (forall i : K, (@IN K i k) -> @IN A (f i) (s i)) (@RESTRICTION K A k f))).
Axiom thm_CARTESIAN_PRODUCT_EQ_EMPTY : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, ((@cartesian_product A K k s) = (@set0 (K -> A))) = (exists i : K, (@IN K i k) /\ ((s i) = (@set0 A))).
Axiom thm_CARTESIAN_PRODUCT_EMPTY : forall {A K : Type'}, forall s : K -> A -> Prop, (@cartesian_product A K (@set0 K) s) = (@INSERT (K -> A) (fun i : K => @ARB A) (@set0 (K -> A))).
Axiom thm_CARTESIAN_PRODUCT_EQ_MEMBERS : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, forall y : K -> A, ((@IN (K -> A) x (@cartesian_product A K k s)) /\ ((@IN (K -> A) y (@cartesian_product A K k s)) /\ (forall i : K, (@IN K i k) -> (x i) = (y i)))) -> x = y.
Axiom thm_CARTESIAN_PRODUCT_EQ_MEMBERS_EQ : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, forall y : K -> A, ((@IN (K -> A) x (@cartesian_product A K k s)) /\ (@IN (K -> A) y (@cartesian_product A K k s))) -> (x = y) = (forall i : K, (@IN K i k) -> (x i) = (y i)).
Axiom thm_SUBSET_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@subset (K -> A) (@cartesian_product A K k s) (@cartesian_product A K k t)) = (((@cartesian_product A K k s) = (@set0 (K -> A))) \/ (forall i : K, (@IN K i k) -> @subset A (s i) (t i))).
Axiom thm_CARTESIAN_PRODUCT_EQ : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = ((((@cartesian_product A K k s) = (@set0 (K -> A))) /\ ((@cartesian_product A K k t) = (@set0 (K -> A)))) \/ (forall i : K, (@IN K i k) -> (s i) = (t i))).
Axiom thm_INTER_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@setI (K -> A) (@cartesian_product A K k s) (@cartesian_product A K k t)) = (@cartesian_product A K k (fun i : K => @setI A (s i) (t i))).
Axiom thm_CARTESIAN_PRODUCT_UNIV : forall {A K : Type'}, (@cartesian_product A K (@setT K) (fun i : K => @setT A)) = (@setT (K -> A)).
Axiom thm_CARTESIAN_PRODUCT_SINGS : forall {A K : Type'}, forall k : K -> Prop, forall x : K -> A, (@EXTENSIONAL K A k x) -> (@cartesian_product A K k (fun i : K => @INSERT A (x i) (@set0 A))) = (@INSERT (K -> A) x (@set0 (K -> A))).
Axiom thm_CARTESIAN_PRODUCT_SINGS_GEN : forall {A K : Type'}, forall k : K -> Prop, forall x : K -> A, (@cartesian_product A K k (fun i : K => @INSERT A (x i) (@set0 A))) = (@INSERT (K -> A) (@RESTRICTION K A k x) (@set0 (K -> A))).
Axiom thm_IMAGE_PROJECTION_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall i : K, (@IMAGE (K -> A) A (fun x : K -> A => x i) (@cartesian_product A K k s)) = (@COND (A -> Prop) ((@cartesian_product A K k s) = (@set0 (K -> A))) (@set0 A) (@COND (A -> Prop) (@IN K i k) (s i) (@INSERT A (@ARB A) (@set0 A)))).
Axiom thm_FORALL_CARTESIAN_PRODUCT_ELEMENTS : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (forall z : K -> A, forall i : K, ((@IN (K -> A) z (@cartesian_product A K k s)) /\ (@IN K i k)) -> P i (z i)) = (((@cartesian_product A K k s) = (@set0 (K -> A))) \/ (forall i : K, forall x : A, ((@IN K i k) /\ (@IN A x (s i))) -> P i x)).
Axiom thm_FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (~ ((@cartesian_product A K k s) = (@set0 (K -> A)))) -> (forall i : K, forall x : A, ((@IN K i k) /\ (@IN A x (s i))) -> P i x) = (forall z : K -> A, forall i : K, ((@IN (K -> A) z (@cartesian_product A K k s)) /\ (@IN K i k)) -> P i (z i)).
Axiom thm_EXISTS_CARTESIAN_PRODUCT_ELEMENT : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (exists z : K -> A, (@IN (K -> A) z (@cartesian_product A K k s)) /\ (forall i : K, (@IN K i k) -> P i (z i))) = (forall i : K, (@IN K i k) -> exists x : A, (@IN A x (s i)) /\ (P i x)).
Axiom thm_product_map : forall {A B K : Type'}, forall k : K -> Prop, forall f : K -> A -> B, (@product_map A B K k f) = (fun x : K -> A => @RESTRICTION K B k (fun i : K => f i (x i))).
Axiom thm_PRODUCT_MAP_RESTRICTION : forall {A B K : Type'}, forall f : K -> A -> B, forall k : K -> Prop, forall x : K -> A, (@product_map A B K k f (@RESTRICTION K A k x)) = (@RESTRICTION K B k (fun i : K => f i (x i))).
Axiom thm_IMAGE_PRODUCT_MAP : forall {A B K : Type'}, forall f : K -> A -> B, forall k : K -> Prop, forall s : K -> A -> Prop, (@IMAGE (K -> A) (K -> B) (@product_map A B K k f) (@cartesian_product A K k s)) = (@cartesian_product B K k (fun i : K => @IMAGE A B (f i) (s i))).
Axiom thm_disjoint_union : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@disjoint_union A K k s) = (@GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i k) /\ (@IN A x (s i))) (@pair K A i x))).
Axiom thm_SUBSET_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@subset (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> @subset A (s i) (t i)).
Axiom thm_DISJOINT_UNION_EQ : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, ((@disjoint_union A K k s) = (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> (s i) = (t i)).
Axiom thm_SUBSET_DISJOINT_UNION_EXISTS : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall u : (prod K A) -> Prop, (@subset (prod K A) u (@disjoint_union A K k s)) = (exists t : K -> A -> Prop, (u = (@disjoint_union A K k t)) /\ (forall i : K, (@IN K i k) -> @subset A (t i) (s i))).
Axiom thm_INTER_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@setI (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (@disjoint_union A K k (fun i : K => @setI A (s i) (t i))).
Axiom thm_UNION_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@setU (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (@disjoint_union A K k (fun i : K => @setU A (s i) (t i))).
Axiom thm_DISJOINT_UNION_EQ_EMPTY : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, ((@disjoint_union A K k s) = (@set0 (prod K A))) = (forall i : K, (@IN K i k) -> (s i) = (@set0 A)).
Axiom thm_DISJOINT_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@DISJOINT (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> @DISJOINT A (s i) (t i)).
Axiom thm_HAS_SIZE_FUNSPACE : forall {A B : Type'}, forall d : B, forall n : N, forall t : B -> Prop, forall m : N, forall s : A -> Prop, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_150 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_150 ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, (~ (@IN A x s)) -> (f x) = d)) f)) (N.pow n m).
Axiom thm_CARD_FUNSPACE : forall {A B : Type'} (d : B), forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@card (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_151 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_151 ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, (~ (@IN A x s)) -> (f x) = d)) f))) = (N.pow (@card B t) (@card A s)).
Axiom thm_FINITE_FUNSPACE : forall {A B : Type'} (d : B), forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_152 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_152 ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, (~ (@IN A x s)) -> (f x) = d)) f)).
Axiom thm_HAS_SIZE_FUNSPACE_UNIV : forall {A B : Type'}, forall m : N, forall n : N, ((@HAS_SIZE A (@setT A) m) /\ (@HAS_SIZE B (@setT B) n)) -> @HAS_SIZE (A -> B) (@setT (A -> B)) (N.pow n m).
Axiom thm_CARD_FUNSPACE_UNIV : forall {A B : Type'}, ((@finite_set A (@setT A)) /\ (@finite_set B (@setT B))) -> (@card (A -> B) (@setT (A -> B))) = (N.pow (@card B (@setT B)) (@card A (@setT A))).
Axiom thm_FINITE_FUNSPACE_UNIV : forall {A B : Type'}, ((@finite_set A (@setT A)) /\ (@finite_set B (@setT B))) -> @finite_set (A -> B) (@setT (A -> B)).
Axiom thm_HAS_SIZE_BOOL : @HAS_SIZE Prop (@setT Prop) ((BIT0 (BIT1 N0))).
Axiom thm_CARD_BOOL : (@card Prop (@setT Prop)) = ((BIT0 (BIT1 N0))).
Axiom thm_FINITE_BOOL : @finite_set Prop (@setT Prop).
Axiom thm_HAS_SIZE_POWERSET : forall {A : Type'}, forall s : A -> Prop, forall n : N, (@HAS_SIZE A s n) -> @HAS_SIZE (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_155 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_155 (@subset A t s) t)) (N.pow ((BIT0 (BIT1 N0))) n).
Axiom thm_CARD_POWERSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@card (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_156 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_156 (@subset A t s) t))) = (N.pow ((BIT0 (BIT1 N0))) (@card A s)).
Axiom thm_FINITE_POWERSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> @finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_157 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_157 (@subset A t s) t)).
Axiom thm_FINITE_POWERSET_EQ : forall {A : Type'}, forall s : A -> Prop, (@finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_158 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_158 (@subset A t s) t))) = (@finite_set A s).
Axiom thm_FINITE_RESTRICTED_SUBSETS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@finite_set A s) -> @finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_160 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_160 ((@subset A t s) /\ (P t)) t)).
Axiom thm_FINITE_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@finite_set A (@UNIONS A s)) = ((@finite_set (A -> Prop) s) /\ (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t)).
Axiom thm_FINITE_CARD_LE_UNIONS : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : N, forall n : N, ((forall x : A, (@IN A x s) -> (@finite_set B (t x)) /\ (N.le (@card B (t x)) n)) /\ ((@finite_set A s) /\ (N.le (@card A s) m))) -> (@finite_set B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_161 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_161 (@IN A x s) (t x))))) /\ (N.le (@card B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_162 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_162 (@IN A x s) (t x))))) (N.mul m n)).
Axiom thm_POWERSET_CLAUSES : forall {A : Type'}, ((@GSPEC (A -> Prop) (fun GEN_PVAR_163 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_163 (@subset A s (@set0 A)) s)) = (@INSERT (A -> Prop) (@set0 A) (@set0 (A -> Prop)))) /\ (forall a : A, forall t : A -> Prop, (@GSPEC (A -> Prop) (fun GEN_PVAR_164 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_164 (@subset A s (@INSERT A a t)) s)) = (@setU (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_165 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_165 (@subset A s t) s)) (@IMAGE (A -> Prop) (A -> Prop) (fun s : A -> Prop => @INSERT A a s) (@GSPEC (A -> Prop) (fun GEN_PVAR_166 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_166 (@subset A s t) s))))).
Axiom thm_FINITE_IMAGE_INFINITE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((@INFINITE A s) /\ (@finite_set B (@IMAGE A B f s))) -> exists a : A, (@IN A a s) /\ (@INFINITE A (@GSPEC A (fun GEN_PVAR_171 : A => exists x : A, @SETSPEC A GEN_PVAR_171 ((@IN A x s) /\ ((f x) = (f a))) x))).
Axiom thm_FINITE_RESTRICTED_POWERSET : forall {A : Type'}, forall s : A -> Prop, forall n : N, (@finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_176 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_176 ((@subset A t s) /\ (@HAS_SIZE A t n)) t))) = ((@finite_set A s) \/ (n = N0)).
Axiom thm_FINITE_RESTRICTED_FUNSPACE : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall k : A -> B, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_180 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_180 ((@subset B (@IMAGE A B f s) t) /\ (@subset A (@GSPEC A (fun GEN_PVAR_179 : A => exists x : A, @SETSPEC A GEN_PVAR_179 (~ ((f x) = (k x))) x)) s)) f)).
Axiom thm_NUMSEG_CLAUSES_LT : ((@GSPEC N (fun GEN_PVAR_181 : N => exists i : N, @SETSPEC N GEN_PVAR_181 (N.lt i N0) i)) = (@set0 N)) /\ (forall k : N, (@GSPEC N (fun GEN_PVAR_182 : N => exists i : N, @SETSPEC N GEN_PVAR_182 (N.lt i (N.succ k)) i)) = (@INSERT N k (@GSPEC N (fun GEN_PVAR_183 : N => exists i : N, @SETSPEC N GEN_PVAR_183 (N.lt i k) i)))).
Axiom thm_HAS_SIZE_NUMSEG_LT : forall n : N, @HAS_SIZE N (@GSPEC N (fun GEN_PVAR_184 : N => exists m : N, @SETSPEC N GEN_PVAR_184 (N.lt m n) m)) n.
Axiom thm_CARD_NUMSEG_LT : forall n : N, (@card N (@GSPEC N (fun GEN_PVAR_185 : N => exists m : N, @SETSPEC N GEN_PVAR_185 (N.lt m n) m))) = n.
Axiom thm_FINITE_NUMSEG_LT : forall n : N, @finite_set N (@GSPEC N (fun GEN_PVAR_186 : N => exists m : N, @SETSPEC N GEN_PVAR_186 (N.lt m n) m)).
Axiom thm_NUMSEG_CLAUSES_LE : ((@GSPEC N (fun GEN_PVAR_187 : N => exists i : N, @SETSPEC N GEN_PVAR_187 (N.le i N0) i)) = (@INSERT N N0 (@set0 N))) /\ (forall k : N, (@GSPEC N (fun GEN_PVAR_188 : N => exists i : N, @SETSPEC N GEN_PVAR_188 (N.le i (N.succ k)) i)) = (@INSERT N (N.succ k) (@GSPEC N (fun GEN_PVAR_189 : N => exists i : N, @SETSPEC N GEN_PVAR_189 (N.le i k) i)))).
Axiom thm_HAS_SIZE_NUMSEG_LE : forall n : N, @HAS_SIZE N (@GSPEC N (fun GEN_PVAR_190 : N => exists m : N, @SETSPEC N GEN_PVAR_190 (N.le m n) m)) (N.add n ((BIT1 N0))).
Axiom thm_FINITE_NUMSEG_LE : forall n : N, @finite_set N (@GSPEC N (fun GEN_PVAR_191 : N => exists m : N, @SETSPEC N GEN_PVAR_191 (N.le m n) m)).
Axiom thm_CARD_NUMSEG_LE : forall n : N, (@card N (@GSPEC N (fun GEN_PVAR_192 : N => exists m : N, @SETSPEC N GEN_PVAR_192 (N.le m n) m))) = (N.add n ((BIT1 N0))).
Axiom thm_num_FINITE : forall s : N -> Prop, (@finite_set N s) = (exists a : N, forall x : N, (@IN N x s) -> N.le x a).
Axiom thm_num_FINITE_AVOID : forall s : N -> Prop, (@finite_set N s) -> exists a : N, ~ (@IN N a s).
Axiom thm_num_INFINITE_EQ : forall s : N -> Prop, (@INFINITE N s) = (forall N' : N, exists n : N, (N.le N' n) /\ (@IN N n s)).
Axiom thm_num_INFINITE : @INFINITE N (@setT N).
Axiom thm_string_INFINITE : @INFINITE (list Ascii.ascii) (@setT (list Ascii.ascii)).
Axiom thm_FINITE_REAL_INTERVAL : (forall a : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_202 : R => exists x : R, @SETSPEC R GEN_PVAR_202 (Rlt a x) x)))) /\ ((forall a : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_203 : R => exists x : R, @SETSPEC R GEN_PVAR_203 (Rle a x) x)))) /\ ((forall b : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_204 : R => exists x : R, @SETSPEC R GEN_PVAR_204 (Rlt x b) x)))) /\ ((forall b : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_205 : R => exists x : R, @SETSPEC R GEN_PVAR_205 (Rle x b) x)))) /\ ((forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_206 : R => exists x : R, @SETSPEC R GEN_PVAR_206 ((Rlt a x) /\ (Rlt x b)) x))) = (Rle b a)) /\ ((forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_207 : R => exists x : R, @SETSPEC R GEN_PVAR_207 ((Rle a x) /\ (Rlt x b)) x))) = (Rle b a)) /\ ((forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_208 : R => exists x : R, @SETSPEC R GEN_PVAR_208 ((Rlt a x) /\ (Rle x b)) x))) = (Rle b a)) /\ (forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_209 : R => exists x : R, @SETSPEC R GEN_PVAR_209 ((Rle a x) /\ (Rle x b)) x))) = (Rle b a)))))))).
Axiom thm_real_INFINITE : @INFINITE R (@setT R).
Axiom thm_HAS_SIZE_INDEX : forall {A : Type'}, forall s : A -> Prop, forall n : N, (@HAS_SIZE A s n) -> exists f : N -> A, (forall m : N, (N.lt m n) -> @IN A (f m) s) /\ (forall x : A, (@IN A x s) -> @ex1 N (fun m : N => (N.lt m n) /\ ((f m) = x))).
Axiom thm_INFINITE_ENUMERATE : forall s : N -> Prop, (@INFINITE N s) -> exists r : N -> N, (forall m : N, forall n : N, (N.lt m n) -> N.lt (r m) (r n)) /\ ((@IMAGE N N r (@setT N)) = s).
Axiom thm_INFINITE_ENUMERATE_EQ : forall s : N -> Prop, (@INFINITE N s) = (exists r : N -> N, (forall m : N, forall n : N, (N.lt m n) -> N.lt (r m) (r n)) /\ ((@IMAGE N N r (@setT N)) = s)).
Axiom thm_INFINITE_ENUMERATE_SUBSET : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) = (exists f : N -> A, (forall x : N, @IN A (f x) s) /\ (forall x : N, forall y : N, ((f x) = (f y)) -> x = y)).
Axiom thm_set_of_list : forall {A : Type'} (h : A) (t : list A), ((@set_of_list A (@nil A)) = (@set0 A)) /\ ((@set_of_list A (@cons A h t)) = (@INSERT A h (@set_of_list A t))).
Axiom thm_list_of_set : forall {A : Type'}, forall s : A -> Prop, (@list_of_set A s) = (@ε (list A) (fun l : list A => ((@set_of_list A l) = s) /\ ((@lengthN A l) = (@card A s)))).
Axiom thm_LIST_OF_SET_PROPERTIES : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> ((@set_of_list A (@list_of_set A s)) = s) /\ ((@lengthN A (@list_of_set A s)) = (@card A s)).
Axiom thm_SET_OF_LIST_OF_SET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@set_of_list A (@list_of_set A s)) = s.
Axiom thm_LENGTH_LIST_OF_SET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@lengthN A (@list_of_set A s)) = (@card A s).
Axiom thm_MEM_LIST_OF_SET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> forall x : A, (@List.In A x (@list_of_set A s)) = (@IN A x s).
Axiom thm_FINITE_SET_OF_LIST : forall {A : Type'}, forall l : list A, @finite_set A (@set_of_list A l).
Axiom thm_IN_SET_OF_LIST : forall {A : Type'}, forall x : A, forall l : list A, (@IN A x (@set_of_list A l)) = (@List.In A x l).
Axiom thm_SET_OF_LIST_APPEND : forall {A : Type'}, forall l1 : list A, forall l2 : list A, (@set_of_list A (@app A l1 l2)) = (@setU A (@set_of_list A l1) (@set_of_list A l2)).
Axiom thm_SET_OF_LIST_MAP : forall {A B : Type'}, forall f : A -> B, forall l : list A, (@set_of_list B (@List.map A B f l)) = (@IMAGE A B f (@set_of_list A l)).
Axiom thm_SET_OF_LIST_EQ_EMPTY : forall {A : Type'}, forall l : list A, ((@set_of_list A l) = (@set0 A)) = (l = (@nil A)).
Axiom thm_LIST_OF_SET_EMPTY : forall {A : Type'}, (@list_of_set A (@set0 A)) = (@nil A).
Axiom thm_LIST_OF_SET_SING : forall {A : Type'}, forall a : A, (@list_of_set A (@INSERT A a (@set0 A))) = (@cons A a (@nil A)).
Axiom thm_pairwise : forall {A : Type'}, forall s : A -> Prop, forall r : A -> A -> Prop, (@pairwise A r s) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ (~ (x = y)))) -> r x y).
Axiom thm_PAIRWISE_EMPTY : forall {A : Type'}, forall r : A -> A -> Prop, (@pairwise A r (@set0 A)) = True.
Axiom thm_PAIRWISE_SING : forall {A : Type'}, forall r : A -> A -> Prop, forall x : A, (@pairwise A r (@INSERT A x (@set0 A))) = True.
Axiom thm_PAIRWISE_IMP : forall {A : Type'}, forall P : A -> A -> Prop, forall Q : A -> A -> Prop, forall s : A -> Prop, ((@pairwise A P s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((P x y) /\ (~ (x = y))))) -> Q x y)) -> @pairwise A Q s.
Axiom thm_PAIRWISE_MONO : forall {A : Type'}, forall r : A -> A -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@pairwise A r s) /\ (@subset A t s)) -> @pairwise A r t.
Axiom thm_PAIRWISE_AND : forall {A : Type'}, forall R' : A -> A -> Prop, forall R'' : A -> A -> Prop, forall s : A -> Prop, ((@pairwise A R' s) /\ (@pairwise A R'' s)) = (@pairwise A (fun x : A => fun y : A => (R' x y) /\ (R'' x y)) s).
Axiom thm_PAIRWISE_INSERT : forall {A : Type'}, forall r : A -> A -> Prop, forall x : A, forall s : A -> Prop, (@pairwise A r (@INSERT A x s)) = ((forall y : A, ((@IN A y s) /\ (~ (y = x))) -> (r x y) /\ (r y x)) /\ (@pairwise A r s)).
Axiom thm_PAIRWISE_INSERT_SYMMETRIC : forall {A : Type'}, forall r : A -> A -> Prop, forall x : A, forall s : A -> Prop, (forall y : A, (@IN A y s) -> (r x y) = (r y x)) -> (@pairwise A r (@INSERT A x s)) = ((forall y : A, ((@IN A y s) /\ (~ (y = x))) -> r x y) /\ (@pairwise A r s)).
Axiom thm_PAIRWISE_IMAGE : forall {A B : Type'} (s : A -> Prop), forall r : B -> B -> Prop, forall f : A -> B, (@pairwise B r (@IMAGE A B f s)) = (@pairwise A (fun x : A => fun y : A => (~ ((f x) = (f y))) -> r (f x) (f y)) s).
Axiom thm_PAIRWISE_UNION : forall {A : Type'}, forall R' : A -> A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@pairwise A R' (@setU A s t)) = ((@pairwise A R' s) /\ ((@pairwise A R' t) /\ (forall x : A, forall y : A, ((@IN A x (@setD A s t)) /\ (@IN A y (@setD A t s))) -> (R' x y) /\ (R' y x)))).
Axiom thm_PAIRWISE_CHAIN_UNIONS : forall {A : Type'}, forall R' : A -> A -> Prop, forall c : (A -> Prop) -> Prop, ((forall s : A -> Prop, (@IN (A -> Prop) s c) -> @pairwise A R' s) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s c) /\ (@IN (A -> Prop) t c)) -> (@subset A s t) \/ (@subset A t s))) -> @pairwise A R' (@UNIONS A c).
Axiom thm_DIFF_UNIONS_PAIRWISE_DISJOINT : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, ((@pairwise (A -> Prop) (@DISJOINT A) s) /\ (@subset (A -> Prop) t s)) -> (@setD A (@UNIONS A s) (@UNIONS A t)) = (@UNIONS A (@setD (A -> Prop) s t)).
Axiom thm_INTER_UNIONS_PAIRWISE_DISJOINT : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (@pairwise (A -> Prop) (@DISJOINT A) (@setU (A -> Prop) s t)) -> (@setI A (@UNIONS A s) (@UNIONS A t)) = (@UNIONS A (@setI (A -> Prop) s t)).
Axiom thm_PSUBSET_UNIONS_PAIRWISE_DISJOINT : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall v : (A -> Prop) -> Prop, ((@pairwise (A -> Prop) (@DISJOINT A) v) /\ (@proper (A -> Prop) u (@DELETE (A -> Prop) v (@set0 A)))) -> @proper A (@UNIONS A u) (@UNIONS A v).
Axiom thm_UNION_OF : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (@UNION_OF A P Q) = (fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (P u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> Q c) /\ ((@UNIONS A u) = s))).
Axiom thm_INTERSECTION_OF : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (@INTERSECTION_OF A P Q) = (fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (P u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> Q c) /\ ((@INTERS A u) = s))).
Axiom thm_UNION_OF_INC : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall s : A -> Prop, ((P (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) /\ (Q s)) -> @UNION_OF A P Q s.
Axiom thm_INTERSECTION_OF_INC : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall s : A -> Prop, ((P (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) /\ (Q s)) -> @INTERSECTION_OF A P Q s.
Axiom thm_UNION_OF_MONO : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall Q' : (A -> Prop) -> Prop, forall s : A -> Prop, ((@UNION_OF A P Q s) /\ (forall x : A -> Prop, (Q x) -> Q' x)) -> @UNION_OF A P Q' s.
Axiom thm_INTERSECTION_OF_MONO : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall Q' : (A -> Prop) -> Prop, forall s : A -> Prop, ((@INTERSECTION_OF A P Q s) /\ (forall x : A -> Prop, (Q x) -> Q' x)) -> @INTERSECTION_OF A P Q' s.
Axiom thm_FORALL_UNION_OF : forall {A : Type'} (P : ((A -> Prop) -> Prop) -> Prop) (Q : (A -> Prop) -> Prop) (R' : (A -> Prop) -> Prop), (forall s : A -> Prop, (@UNION_OF A P Q s) -> R' s) = (forall t : (A -> Prop) -> Prop, ((P t) /\ (forall c : A -> Prop, (@IN (A -> Prop) c t) -> Q c)) -> R' (@UNIONS A t)).
Axiom thm_FORALL_INTERSECTION_OF : forall {A : Type'} (P : ((A -> Prop) -> Prop) -> Prop) (Q : (A -> Prop) -> Prop) (R' : (A -> Prop) -> Prop), (forall s : A -> Prop, (@INTERSECTION_OF A P Q s) -> R' s) = (forall t : (A -> Prop) -> Prop, ((P t) /\ (forall c : A -> Prop, (@IN (A -> Prop) c t) -> Q c)) -> R' (@INTERS A t)).
Axiom thm_UNION_OF_EMPTY : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (P (@set0 (A -> Prop))) -> @UNION_OF A P Q (@set0 A).
Axiom thm_INTERSECTION_OF_EMPTY : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (P (@set0 (A -> Prop))) -> @INTERSECTION_OF A P Q (@setT A).
Axiom thm_ARBITRARY : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@ARBITRARY A s) = True.
Axiom thm_ARBITRARY_UNION_OF_ALT : forall {A : Type'}, forall B : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@ARBITRARY A) B s) = (forall x : A, (@IN A x s) -> exists u : A -> Prop, (@IN (A -> Prop) u B) /\ ((@IN A x u) /\ (@subset A u s))).
Axiom thm_ARBITRARY_UNION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @UNION_OF A (@ARBITRARY A) P (@set0 A).
Axiom thm_ARBITRARY_INTERSECTION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @INTERSECTION_OF A (@ARBITRARY A) P (@setT A).
Axiom thm_ARBITRARY_UNION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @UNION_OF A (@ARBITRARY A) P s.
Axiom thm_ARBITRARY_INTERSECTION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @INTERSECTION_OF A (@ARBITRARY A) P s.
Axiom thm_ARBITRARY_UNION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@ARBITRARY A) P s) = (@INTERSECTION_OF A (@ARBITRARY A) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_ARBITRARY_INTERSECTION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTERSECTION_OF A (@ARBITRARY A) P s) = (@UNION_OF A (@ARBITRARY A) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_ARBITRARY_UNION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@UNION_OF A (@ARBITRARY A) (@UNION_OF A (@ARBITRARY A) P)) = (@UNION_OF A (@ARBITRARY A) P).
Axiom thm_ARBITRARY_INTERSECTION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@INTERSECTION_OF A (@ARBITRARY A) (@INTERSECTION_OF A (@ARBITRARY A) P)) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Axiom thm_ARBITRARY_UNION_OF_UNIONS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @UNION_OF A (@ARBITRARY A) P s) -> @UNION_OF A (@ARBITRARY A) P (@UNIONS A u).
Axiom thm_ARBITRARY_UNION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@ARBITRARY A) P s) /\ (@UNION_OF A (@ARBITRARY A) P t)) -> @UNION_OF A (@ARBITRARY A) P (@setU A s t).
Axiom thm_ARBITRARY_INTERSECTION_OF_INTERS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @INTERSECTION_OF A (@ARBITRARY A) P s) -> @INTERSECTION_OF A (@ARBITRARY A) P (@INTERS A u).
Axiom thm_ARBITRARY_INTERSECTION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@ARBITRARY A) P s) /\ (@INTERSECTION_OF A (@ARBITRARY A) P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setI A s t).
Axiom thm_ARBITRARY_UNION_OF_INTER_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@ARBITRARY A) P s) /\ (@UNION_OF A (@ARBITRARY A) P t)) -> @UNION_OF A (@ARBITRARY A) P (@setI A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @UNION_OF A (@ARBITRARY A) P (@setI A s t)).
Axiom thm_ARBITRARY_UNION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setI A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@ARBITRARY A) P s) /\ (@UNION_OF A (@ARBITRARY A) P t)) -> @UNION_OF A (@ARBITRARY A) P (@setI A s t).
Axiom thm_ARBITRARY_INTERSECTION_OF_UNION_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@ARBITRARY A) P s) /\ (@INTERSECTION_OF A (@ARBITRARY A) P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setU A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setU A s t)).
Axiom thm_ARBITRARY_INTERSECTION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setU A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@ARBITRARY A) P s) /\ (@INTERSECTION_OF A (@ARBITRARY A) P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setU A s t).
Axiom thm_FINITE_UNION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @UNION_OF A (@finite_set (A -> Prop)) P (@set0 A).
Axiom thm_FINITE_INTERSECTION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setT A).
Axiom thm_FINITE_UNION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @UNION_OF A (@finite_set (A -> Prop)) P s.
Axiom thm_FINITE_INTERSECTION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P s.
Axiom thm_FINITE_UNION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@finite_set (A -> Prop)) P s) = (@INTERSECTION_OF A (@finite_set (A -> Prop)) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_FINITE_INTERSECTION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) = (@UNION_OF A (@finite_set (A -> Prop)) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_FINITE_UNION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@UNION_OF A (@finite_set (A -> Prop)) (@UNION_OF A (@finite_set (A -> Prop)) P)) = (@UNION_OF A (@finite_set (A -> Prop)) P).
Axiom thm_FINITE_INTERSECTION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@INTERSECTION_OF A (@finite_set (A -> Prop)) (@INTERSECTION_OF A (@finite_set (A -> Prop)) P)) = (@INTERSECTION_OF A (@finite_set (A -> Prop)) P).
Axiom thm_FINITE_UNION_OF_UNIONS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) u) /\ (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @UNION_OF A (@finite_set (A -> Prop)) P s)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@UNIONS A u).
Axiom thm_FINITE_UNION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@finite_set (A -> Prop)) P s) /\ (@UNION_OF A (@finite_set (A -> Prop)) P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setU A s t).
Axiom thm_FINITE_INTERSECTION_OF_INTERS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) u) /\ (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P s)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@INTERS A u).
Axiom thm_FINITE_INTERSECTION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) /\ (@INTERSECTION_OF A (@finite_set (A -> Prop)) P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setI A s t).
Axiom thm_FINITE_UNION_OF_INTER_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@finite_set (A -> Prop)) P s) /\ (@UNION_OF A (@finite_set (A -> Prop)) P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setI A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setI A s t)).
Axiom thm_FINITE_UNION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setI A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@finite_set (A -> Prop)) P s) /\ (@UNION_OF A (@finite_set (A -> Prop)) P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setI A s t).
Axiom thm_FINITE_INTERSECTION_OF_UNION_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) /\ (@INTERSECTION_OF A (@finite_set (A -> Prop)) P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setU A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setU A s t)).
Axiom thm_FINITE_INTERSECTION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setU A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) /\ (@INTERSECTION_OF A (@finite_set (A -> Prop)) P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setU A s t).
Axiom thm_CARD_SET_OF_LIST_LE : forall {A : Type'}, forall l : list A, N.le (@card A (@set_of_list A l)) (@lengthN A l).
Axiom thm_HAS_SIZE_SET_OF_LIST : forall {A : Type'}, forall l : list A, (@HAS_SIZE A (@set_of_list A l) (@lengthN A l)) = (@List.ForallOrdPairs A (fun x : A => fun y : A => ~ (x = y)) l).
Axiom thm_SURJECTIVE_IFF_INJECTIVE_GEN : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, ((@finite_set A s) /\ ((@finite_set B t) /\ (((@card A s) = (@card B t)) /\ (@subset B (@IMAGE A B f s) t)))) -> (forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_SURJECTIVE_IFF_INJECTIVE : forall {A : Type'}, forall s : A -> Prop, forall f : A -> A, ((@finite_set A s) /\ (@subset A (@IMAGE A A f s) s)) -> (forall y : A, (@IN A y s) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_IMAGE_IMP_INJECTIVE_GEN : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, ((@finite_set A s) /\ (((@card A s) = (@card B t)) /\ ((@IMAGE A B f s) = t))) -> forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y.
Axiom thm_IMAGE_IMP_INJECTIVE : forall {A : Type'}, forall s : A -> Prop, forall f : A -> A, ((@finite_set A s) /\ ((@IMAGE A A f s) = s)) -> forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y.
Axiom thm_HAS_SIZE_IMAGE_INJ_RESTRICT : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, forall P : B -> Prop, forall n : N, ((@finite_set A s) /\ ((@finite_set B t) /\ (((@card A s) = (@card B t)) /\ ((@subset B (@IMAGE A B f s) t) /\ ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@HAS_SIZE A (@GSPEC A (fun GEN_PVAR_219 : A => exists x : A, @SETSPEC A GEN_PVAR_219 ((@IN A x s) /\ (P (f x))) x)) n)))))) -> @HAS_SIZE B (@GSPEC B (fun GEN_PVAR_220 : B => exists x : B, @SETSPEC B GEN_PVAR_220 ((@IN B x t) /\ (P x)) x)) n.
Axiom thm_CARD_LE_INJ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((@finite_set B t) /\ (N.le (@card A s) (@card B t)))) -> exists f : A -> B, (@subset B (@IMAGE A B f s) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_FORALL_IN_CLAUSES : forall {A : Type'}, (forall P : A -> Prop, (forall x : A, (@IN A x (@set0 A)) -> P x) = True) /\ (forall P : A -> Prop, forall a : A, forall s : A -> Prop, (forall x : A, (@IN A x (@INSERT A a s)) -> P x) = ((P a) /\ (forall x : A, (@IN A x s) -> P x))).
Axiom thm_EXISTS_IN_CLAUSES : forall {A : Type'}, (forall P : A -> Prop, (exists x : A, (@IN A x (@set0 A)) /\ (P x)) = False) /\ (forall P : A -> Prop, forall a : A, forall s : A -> Prop, (exists x : A, (@IN A x (@INSERT A a s)) /\ (P x)) = ((P a) \/ (exists x : A, (@IN A x s) /\ (P x)))).
Axiom thm_INJECTIVE_ON_IMAGE : forall {A B : Type'}, forall f : A -> B, forall u : A -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@subset A s u) /\ ((@subset A t u) /\ ((@IMAGE A B f s) = (@IMAGE A B f t)))) -> s = t) = (forall x : A, forall y : A, ((@IN A x u) /\ ((@IN A y u) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_INJECTIVE_IMAGE : forall {A B : Type'}, forall f : A -> B, (forall s : A -> Prop, forall t : A -> Prop, ((@IMAGE A B f s) = (@IMAGE A B f t)) -> s = t) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_SURJECTIVE_ON_IMAGE : forall {A B : Type'}, forall f : A -> B, forall u : A -> Prop, forall v : B -> Prop, (forall t : B -> Prop, (@subset B t v) -> exists s : A -> Prop, (@subset A s u) /\ ((@IMAGE A B f s) = t)) = (forall y : B, (@IN B y v) -> exists x : A, (@IN A x u) /\ ((f x) = y)).
Axiom thm_SURJECTIVE_IMAGE : forall {A B : Type'}, forall f : A -> B, (forall t : B -> Prop, exists s : A -> Prop, (@IMAGE A B f s) = t) = (forall y : B, exists x : A, (f x) = y).
Axiom thm_INJECTIVE_ON_PREIMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall u : B -> Prop, (forall t : B -> Prop, forall t' : B -> Prop, ((@subset B t u) /\ ((@subset B t' u) /\ ((@GSPEC A (fun GEN_PVAR_222 : A => exists x : A, @SETSPEC A GEN_PVAR_222 ((@IN A x s) /\ (@IN B (f x) t)) x)) = (@GSPEC A (fun GEN_PVAR_223 : A => exists x : A, @SETSPEC A GEN_PVAR_223 ((@IN A x s) /\ (@IN B (f x) t')) x))))) -> t = t') = (@subset B u (@IMAGE A B f s)).
Axiom thm_SURJECTIVE_ON_PREIMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall u : B -> Prop, (forall k : A -> Prop, (@subset A k s) -> exists t : B -> Prop, (@subset B t u) /\ ((@GSPEC A (fun GEN_PVAR_224 : A => exists x : A, @SETSPEC A GEN_PVAR_224 ((@IN A x s) /\ (@IN B (f x) t)) x)) = k)) = ((@subset B (@IMAGE A B f s) u) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_INJECTIVE_PREIMAGE : forall {A B : Type'}, forall f : A -> B, (forall t : B -> Prop, forall t' : B -> Prop, ((@GSPEC A (fun GEN_PVAR_225 : A => exists x : A, @SETSPEC A GEN_PVAR_225 (@IN B (f x) t) x)) = (@GSPEC A (fun GEN_PVAR_226 : A => exists x : A, @SETSPEC A GEN_PVAR_226 (@IN B (f x) t') x))) -> t = t') = ((@IMAGE A B f (@setT A)) = (@setT B)).
Axiom thm_SURJECTIVE_PREIMAGE : forall {A B : Type'}, forall f : A -> B, (forall k : A -> Prop, exists t : B -> Prop, (@GSPEC A (fun GEN_PVAR_227 : A => exists x : A, @SETSPEC A GEN_PVAR_227 (@IN B (f x) t) x)) = k) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_CARD_EQ_BIJECTION : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((@finite_set B t) /\ ((@card A s) = (@card B t)))) -> exists f : A -> B, (forall x : A, (@IN A x s) -> @IN B (f x) t) /\ ((forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_CARD_EQ_BIJECTIONS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((@finite_set B t) /\ ((@card A s) = (@card B t)))) -> exists f : A -> B, exists g : B -> A, (forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)).
Axiom thm_CARD_EQ_BIJECTIONS_SPECIAL : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall a : A, forall b : B, ((@finite_set A s) /\ ((@finite_set B t) /\ (((@card A s) = (@card B t)) /\ ((@IN A a s) /\ (@IN B b t))))) -> exists f : A -> B, exists g : B -> A, ((f a) = b) /\ (((g b) = a) /\ ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)))).
Axiom thm_BIJECTIONS_HAS_SIZE : forall {A B : Type'} (n : N), forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, forall g : B -> A, ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ ((forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)) /\ (@HAS_SIZE A s n))) -> @HAS_SIZE B t n.
Axiom thm_BIJECTIONS_HAS_SIZE_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, forall g : B -> A, ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y))) -> forall n : N, (@HAS_SIZE A s n) = (@HAS_SIZE B t n).
Axiom thm_BIJECTIONS_CARD_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, forall g : B -> A, (((@finite_set A s) \/ (@finite_set B t)) /\ ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)))) -> (@card A s) = (@card B t).
Axiom thm_WF_FINITE : forall {A : Type'}, forall lt2 : A -> A -> Prop, ((forall x : A, ~ (lt2 x x)) /\ ((forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) /\ (forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_229 : A => exists y : A, @SETSPEC A GEN_PVAR_229 (lt2 y x) y))))) -> @well_founded A lt2.
Axiom thm_WF_PSUBSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> @well_founded (A -> Prop) (fun t1 : A -> Prop => fun t2 : A -> Prop => (@proper A t1 t2) /\ (@subset A t2 s)).
Axiom thm_le_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@le_c A B s t) = (exists f : A -> B, (forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_lt_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@lt_c A B s t) = ((@le_c A B s t) /\ (~ (@le_c B A t s))).
Axiom thm_eq_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@eq_c A B s t) = (exists f : A -> B, (forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((f x) = y)))).
Axiom thm_ge_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@ge_c A B s t) = (@le_c B A t s).
Axiom thm_gt_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@gt_c A B s t) = (@lt_c B A t s).
Axiom thm_LE_C : forall {A B : Type'}, forall s : B -> Prop, forall t : A -> Prop, (@le_c B A s t) = (exists g : A -> B, forall x : B, (@IN B x s) -> exists y : A, (@IN A y t) /\ ((g y) = x)).
Axiom thm_GE_C : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@ge_c A B s t) = (exists f : A -> B, forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ (y = (f x))).
Axiom thm_COUNTABLE : forall {A : Type'}, forall t : A -> Prop, (@COUNTABLE A t) = (@ge_c N A (@setT N) t).
Axiom thm_SUP_EQ : forall s : R -> Prop, forall t : R -> Prop, (forall b : R, (forall x : R, (@IN R x s) -> Rle x b) = (forall x : R, (@IN R x t) -> Rle x b)) -> (sup s) = (sup t).
Axiom thm_SUP : forall s : R -> Prop, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> Rle x b)) -> (forall x : R, (@IN R x s) -> Rle x (sup s)) /\ (forall b : R, (forall x : R, (@IN R x s) -> Rle x b) -> Rle (sup s) b).
Axiom thm_SUP_FINITE_LEMMA : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> exists b : R, (@IN R b s) /\ (forall x : R, (@IN R x s) -> Rle x b).
Axiom thm_SUP_FINITE : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (@IN R (sup s) s) /\ (forall x : R, (@IN R x s) -> Rle x (sup s)).
Axiom thm_REAL_LE_SUP_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rle a (sup s)) = (exists x : R, (@IN R x s) /\ (Rle a x)).
Axiom thm_REAL_SUP_LE_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rle (sup s) a) = (forall x : R, (@IN R x s) -> Rle x a).
Axiom thm_REAL_LT_SUP_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rlt a (sup s)) = (exists x : R, (@IN R x s) /\ (Rlt a x)).
Axiom thm_REAL_SUP_LT_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rlt (sup s) a) = (forall x : R, (@IN R x s) -> Rlt x a).
Axiom thm_REAL_SUP_UNIQUE : forall s : R -> Prop, forall b : R, ((forall x : R, (@IN R x s) -> Rle x b) /\ (forall b' : R, (Rlt b' b) -> exists x : R, (@IN R x s) /\ (Rlt b' x))) -> (sup s) = b.
Axiom thm_REAL_SUP_LE_SUBSET : forall s : R -> Prop, forall t : R -> Prop, ((~ (s = (@set0 R))) /\ ((@subset R s t) /\ (exists b : R, forall x : R, (@IN R x t) -> Rle x b))) -> Rle (sup s) (sup t).
Axiom thm_REAL_SUP_BOUNDS : forall s : R -> Prop, forall a : R, forall b : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> (Rle a x) /\ (Rle x b))) -> (Rle a (sup s)) /\ (Rle (sup s) b).
Axiom thm_REAL_ABS_SUP_LE : forall s : R -> Prop, forall a : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> Rle (Rabs x) a)) -> Rle (Rabs (sup s)) a.
Axiom thm_REAL_SUP_ASCLOSE : forall s : R -> Prop, forall l : R, forall e : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> Rle (Rabs (Rminus x l)) e)) -> Rle (Rabs (Rminus (sup s) l)) e.
Axiom thm_SUP_UNIQUE_FINITE : forall (a : R), forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> ((sup s) = a) = ((@IN R a s) /\ (forall y : R, (@IN R y s) -> Rle y a)).
Axiom thm_SUP_INSERT_FINITE : forall x : R, forall s : R -> Prop, (@finite_set R s) -> (sup (@INSERT R x s)) = (@COND R (s = (@set0 R)) x (Rmax x (sup s))).
Axiom thm_SUP_SING : forall a : R, (sup (@INSERT R a (@set0 R))) = a.
Axiom thm_SUP_INSERT_INSERT : forall a : R, forall b : R, forall s : R -> Prop, (sup (@INSERT R b (@INSERT R a s))) = (sup (@INSERT R (Rmax a b) s)).
Axiom thm_REAL_LE_SUP : forall s : R -> Prop, forall a : R, forall b : R, forall y : R, ((@IN R y s) /\ ((Rle a y) /\ (forall x : R, (@IN R x s) -> Rle x b))) -> Rle a (sup s).
Axiom thm_REAL_SUP_LE_EQ : forall s : R -> Prop, forall y : R, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> Rle x b)) -> (Rle (sup s) y) = (forall x : R, (@IN R x s) -> Rle x y).
Axiom thm_SUP_UNIQUE : forall s : R -> Prop, forall b : R, (forall c : R, (forall x : R, (@IN R x s) -> Rle x c) = (Rle b c)) -> (sup s) = b.
Axiom thm_SUP_UNION : forall s : R -> Prop, forall t : R -> Prop, ((~ (s = (@set0 R))) /\ ((~ (t = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> Rle x b) /\ (exists c : R, forall x : R, (@IN R x t) -> Rle x c)))) -> (sup (@setU R s t)) = (Rmax (sup s) (sup t)).
Axiom thm_ELEMENT_LE_SUP : forall s : R -> Prop, forall a : R, ((exists b : R, forall x : R, (@IN R x s) -> Rle x b) /\ (@IN R a s)) -> Rle a (sup s).
Axiom thm_SUP_APPROACH : forall s : R -> Prop, forall c : R, ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> Rle x b) /\ (Rlt c (sup s)))) -> exists x : R, (@IN R x s) /\ (Rlt c x).
Axiom thm_REAL_MAX_SUP : forall x : R, forall y : R, (Rmax x y) = (sup (@INSERT R x (@INSERT R y (@set0 R)))).
Axiom thm_inf : forall s : R -> Prop, (inf s) = (@ε R (fun a : R => (forall x : R, (@IN R x s) -> Rle a x) /\ (forall b : R, (forall x : R, (@IN R x s) -> Rle b x) -> Rle b a))).
Axiom thm_INF_EQ : forall s : R -> Prop, forall t : R -> Prop, (forall a : R, (forall x : R, (@IN R x s) -> Rle a x) = (forall x : R, (@IN R x t) -> Rle a x)) -> (inf s) = (inf t).
Axiom thm_INF : forall s : R -> Prop, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> Rle b x)) -> (forall x : R, (@IN R x s) -> Rle (inf s) x) /\ (forall b : R, (forall x : R, (@IN R x s) -> Rle b x) -> Rle b (inf s)).
Axiom thm_INF_FINITE_LEMMA : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> exists b : R, (@IN R b s) /\ (forall x : R, (@IN R x s) -> Rle b x).
Axiom thm_INF_FINITE : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (@IN R (inf s) s) /\ (forall x : R, (@IN R x s) -> Rle (inf s) x).
Axiom thm_REAL_LE_INF_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rle a (inf s)) = (forall x : R, (@IN R x s) -> Rle a x).
Axiom thm_REAL_INF_LE_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rle (inf s) a) = (exists x : R, (@IN R x s) /\ (Rle x a)).
Axiom thm_REAL_LT_INF_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rlt a (inf s)) = (forall x : R, (@IN R x s) -> Rlt a x).
Axiom thm_REAL_INF_LT_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (Rlt (inf s) a) = (exists x : R, (@IN R x s) /\ (Rlt x a)).
Axiom thm_REAL_INF_UNIQUE : forall s : R -> Prop, forall b : R, ((forall x : R, (@IN R x s) -> Rle b x) /\ (forall b' : R, (Rlt b b') -> exists x : R, (@IN R x s) /\ (Rlt x b'))) -> (inf s) = b.
Axiom thm_REAL_LE_INF : forall (s : R -> Prop), forall b : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> Rle b x)) -> Rle b (inf s).
Axiom thm_REAL_LE_INF_SUBSET : forall s : R -> Prop, forall t : R -> Prop, ((~ (t = (@set0 R))) /\ ((@subset R t s) /\ (exists b : R, forall x : R, (@IN R x s) -> Rle b x))) -> Rle (inf s) (inf t).
Axiom thm_REAL_INF_BOUNDS : forall s : R -> Prop, forall a : R, forall b : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> (Rle a x) /\ (Rle x b))) -> (Rle a (inf s)) /\ (Rle (inf s) b).
Axiom thm_REAL_ABS_INF_LE : forall s : R -> Prop, forall a : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> Rle (Rabs x) a)) -> Rle (Rabs (inf s)) a.
Axiom thm_REAL_INF_ASCLOSE : forall s : R -> Prop, forall l : R, forall e : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> Rle (Rabs (Rminus x l)) e)) -> Rle (Rabs (Rminus (inf s) l)) e.
Axiom thm_INF_UNIQUE_FINITE : forall (a : R), forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> ((inf s) = a) = ((@IN R a s) /\ (forall y : R, (@IN R y s) -> Rle a y)).
Axiom thm_INF_INSERT_FINITE : forall x : R, forall s : R -> Prop, (@finite_set R s) -> (inf (@INSERT R x s)) = (@COND R (s = (@set0 R)) x (Rmin x (inf s))).
Axiom thm_INF_SING : forall a : R, (inf (@INSERT R a (@set0 R))) = a.
Axiom thm_INF_INSERT_INSERT : forall a : R, forall b : R, forall s : R -> Prop, (inf (@INSERT R b (@INSERT R a s))) = (inf (@INSERT R (Rmin a b) s)).
Axiom thm_REAL_SUP_EQ_INF : forall s : R -> Prop, ((~ (s = (@set0 R))) /\ (exists B : R, forall x : R, (@IN R x s) -> Rle (Rabs x) B)) -> ((sup s) = (inf s)) = (exists a : R, s = (@INSERT R a (@set0 R))).
Axiom thm_REAL_INF_LE : forall s : R -> Prop, forall a : R, forall b : R, forall y : R, ((@IN R y s) /\ ((Rle y b) /\ (forall x : R, (@IN R x s) -> Rle a x))) -> Rle (inf s) b.
Axiom thm_REAL_LE_INF_EQ : forall s : R -> Prop, forall y : R, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> Rle b x)) -> (Rle y (inf s)) = (forall x : R, (@IN R x s) -> Rle y x).
Axiom thm_INF_UNIQUE : forall s : R -> Prop, forall b : R, (forall c : R, (forall x : R, (@IN R x s) -> Rle c x) = (Rle c b)) -> (inf s) = b.
Axiom thm_INF_UNION : forall s : R -> Prop, forall t : R -> Prop, ((~ (s = (@set0 R))) /\ ((~ (t = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> Rle b x) /\ (exists c : R, forall x : R, (@IN R x t) -> Rle c x)))) -> (inf (@setU R s t)) = (Rmin (inf s) (inf t)).
Axiom thm_INF_LE_ELEMENT : forall s : R -> Prop, forall a : R, ((exists b : R, forall x : R, (@IN R x s) -> Rle b x) /\ (@IN R a s)) -> Rle (inf s) a.
Axiom thm_INF_APPROACH : forall s : R -> Prop, forall c : R, ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> Rle b x) /\ (Rlt (inf s) c))) -> exists x : R, (@IN R x s) /\ (Rlt x c).
Axiom thm_REAL_MIN_INF : forall x : R, forall y : R, (Rmin x y) = (inf (@INSERT R x (@INSERT R y (@set0 R)))).
Axiom thm_has_inf : forall s : R -> Prop, forall b : R, (has_inf s b) = (forall c : R, (forall x : R, (@IN R x s) -> Rle c x) = (Rle c b)).
Axiom thm_has_sup : forall s : R -> Prop, forall b : R, (has_sup s b) = (forall c : R, (forall x : R, (@IN R x s) -> Rle x c) = (Rle b c)).
Axiom thm_HAS_INF_LBOUND : forall s : R -> Prop, forall b : R, forall x : R, ((has_inf s b) /\ (@IN R x s)) -> Rle b x.
Axiom thm_HAS_SUP_UBOUND : forall s : R -> Prop, forall b : R, forall x : R, ((has_sup s b) /\ (@IN R x s)) -> Rle x b.
Axiom thm_HAS_INF_INF : forall s : R -> Prop, forall l : R, (has_inf s l) = ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> Rle b x) /\ ((inf s) = l))).
Axiom thm_HAS_SUP_SUP : forall s : R -> Prop, forall l : R, (has_sup s l) = ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> Rle x b) /\ ((sup s) = l))).
Axiom thm_INF_EXISTS : forall s : R -> Prop, (exists l : R, has_inf s l) = ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> Rle b x)).
Axiom thm_SUP_EXISTS : forall s : R -> Prop, (exists l : R, has_sup s l) = ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> Rle x b)).
Axiom thm_HAS_INF_APPROACH : forall s : R -> Prop, forall l : R, forall c : R, ((has_inf s l) /\ (Rlt l c)) -> exists x : R, (@IN R x s) /\ (Rlt x c).
Axiom thm_HAS_SUP_APPROACH : forall s : R -> Prop, forall l : R, forall c : R, ((has_sup s l) /\ (Rlt c l)) -> exists x : R, (@IN R x s) /\ (Rlt c x).
Axiom thm_HAS_INF : forall s : R -> Prop, forall l : R, (has_inf s l) = ((~ (s = (@set0 R))) /\ ((forall x : R, (@IN R x s) -> Rle l x) /\ (forall c : R, (Rlt l c) -> exists x : R, (@IN R x s) /\ (Rlt x c)))).
Axiom thm_HAS_SUP : forall s : R -> Prop, forall l : R, (has_sup s l) = ((~ (s = (@set0 R))) /\ ((forall x : R, (@IN R x s) -> Rle x l) /\ (forall c : R, (Rlt c l) -> exists x : R, (@IN R x s) /\ (Rlt c x)))).
Axiom thm_HAS_INF_LE : forall s : R -> Prop, forall t : R -> Prop, forall l : R, forall m : R, ((has_inf s l) /\ ((has_inf t m) /\ (forall y : R, (@IN R y t) -> exists x : R, (@IN R x s) /\ (Rle x y)))) -> Rle l m.
Axiom thm_HAS_SUP_LE : forall s : R -> Prop, forall t : R -> Prop, forall l : R, forall m : R, ((has_sup s l) /\ ((has_sup t m) /\ (forall y : R, (@IN R y t) -> exists x : R, (@IN R x s) /\ (Rle y x)))) -> Rle m l.
Axiom thm_numseg : forall m : N, forall n : N, (Ninterval m n) = (@GSPEC N (fun GEN_PVAR_231 : N => exists x : N, @SETSPEC N GEN_PVAR_231 ((N.le m x) /\ (N.le x n)) x)).
Axiom thm_FINITE_NUMSEG : forall m : N, forall n : N, @finite_set N (Ninterval m n).
Axiom thm_NUMSEG_COMBINE_R : forall m : N, forall p : N, forall n : N, ((N.le m (N.add p ((BIT1 N0)))) /\ (N.le p n)) -> (@setU N (Ninterval m p) (Ninterval (N.add p ((BIT1 N0))) n)) = (Ninterval m n).
Axiom thm_NUMSEG_COMBINE_L : forall m : N, forall p : N, forall n : N, ((N.le m p) /\ (N.le p (N.add n ((BIT1 N0))))) -> (@setU N (Ninterval m (N.sub p ((BIT1 N0)))) (Ninterval p n)) = (Ninterval m n).
Axiom thm_NUMSEG_LREC : forall m : N, forall n : N, (N.le m n) -> (@INSERT N m (Ninterval (N.add m ((BIT1 N0))) n)) = (Ninterval m n).
Axiom thm_NUMSEG_RREC : forall m : N, forall n : N, (N.le m n) -> (@INSERT N n (Ninterval m (N.sub n ((BIT1 N0))))) = (Ninterval m n).
Axiom thm_NUMSEG_REC : forall m : N, forall n : N, (N.le m (N.succ n)) -> (Ninterval m (N.succ n)) = (@INSERT N (N.succ n) (Ninterval m n)).
Axiom thm_IN_NUMSEG : forall m : N, forall n : N, forall p : N, (@IN N p (Ninterval m n)) = ((N.le m p) /\ (N.le p n)).
Axiom thm_IN_NUMSEG_0 : forall m : N, forall n : N, (@IN N m (Ninterval N0 n)) = (N.le m n).
Axiom thm_NUMSEG_SING : forall n : N, (Ninterval n n) = (@INSERT N n (@set0 N)).
Axiom thm_NUMSEG_EMPTY : forall m : N, forall n : N, ((Ninterval m n) = (@set0 N)) = (N.lt n m).
Axiom thm_EMPTY_NUMSEG : forall m : N, forall n : N, (N.lt n m) -> (Ninterval m n) = (@set0 N).
Axiom thm_FINITE_SUBSET_NUMSEG : forall s : N -> Prop, (@finite_set N s) = (exists n : N, @subset N s (Ninterval N0 n)).
Axiom thm_CARD_NUMSEG_LEMMA : forall m : N, forall d : N, (@card N (Ninterval m (N.add m d))) = (N.add d ((BIT1 N0))).
Axiom thm_CARD_NUMSEG : forall m : N, forall n : N, (@card N (Ninterval m n)) = (N.sub (N.add n ((BIT1 N0))) m).
Axiom thm_HAS_SIZE_NUMSEG : forall m : N, forall n : N, @HAS_SIZE N (Ninterval m n) (N.sub (N.add n ((BIT1 N0))) m).
Axiom thm_CARD_NUMSEG_1 : forall n : N, (@card N (Ninterval ((BIT1 N0)) n)) = n.
Axiom thm_HAS_SIZE_NUMSEG_1 : forall n : N, @HAS_SIZE N (Ninterval ((BIT1 N0)) n) n.
Axiom thm_NUMSEG_CLAUSES : (forall m : N, (Ninterval m N0) = (@COND (N -> Prop) (m = N0) (@INSERT N N0 (@set0 N)) (@set0 N))) /\ (forall m : N, forall n : N, (Ninterval m (N.succ n)) = (@COND (N -> Prop) (N.le m (N.succ n)) (@INSERT N (N.succ n) (Ninterval m n)) (Ninterval m n))).
Axiom thm_FINITE_INDEX_NUMSEG : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) = (exists f : N -> A, (forall i : N, forall j : N, ((@IN N i (Ninterval ((BIT1 N0)) (@card A s))) /\ ((@IN N j (Ninterval ((BIT1 N0)) (@card A s))) /\ ((f i) = (f j)))) -> i = j) /\ (s = (@IMAGE N A f (Ninterval ((BIT1 N0)) (@card A s))))).
Axiom thm_FINITE_INDEX_NUMBERS : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) = (exists k : N -> Prop, exists f : N -> A, (forall i : N, forall j : N, ((@IN N i k) /\ ((@IN N j k) /\ ((f i) = (f j)))) -> i = j) /\ ((@finite_set N k) /\ (s = (@IMAGE N A f k)))).
Axiom thm_INTER_NUMSEG : forall m : N, forall n : N, forall p : N, forall q : N, (@setI N (Ninterval m n) (Ninterval p q)) = (Ninterval (N.max m p) (N.min n q)).
Axiom thm_DISJOINT_NUMSEG : forall m : N, forall n : N, forall p : N, forall q : N, (@DISJOINT N (Ninterval m n) (Ninterval p q)) = ((N.lt n p) \/ ((N.lt q m) \/ ((N.lt n m) \/ (N.lt q p)))).
Axiom thm_NUMSEG_ADD_SPLIT : forall m : N, forall n : N, forall p : N, (N.le m (N.add n ((BIT1 N0)))) -> (Ninterval m (N.add n p)) = (@setU N (Ninterval m n) (Ninterval (N.add n ((BIT1 N0))) (N.add n p))).
Axiom thm_NUMSEG_OFFSET_IMAGE : forall m : N, forall n : N, forall p : N, (Ninterval (N.add m p) (N.add n p)) = (@IMAGE N N (fun i : N => N.add i p) (Ninterval m n)).
Axiom thm_SUBSET_NUMSEG : forall m : N, forall n : N, forall p : N, forall q : N, (@subset N (Ninterval m n) (Ninterval p q)) = ((N.lt n m) \/ ((N.le p m) /\ (N.le n q))).
Axiom thm_NUMSEG_LE : forall n : N, (@GSPEC N (fun GEN_PVAR_233 : N => exists x : N, @SETSPEC N GEN_PVAR_233 (N.le x n) x)) = (Ninterval N0 n).
Axiom thm_NUMSEG_LT : forall n : N, (@GSPEC N (fun GEN_PVAR_234 : N => exists x : N, @SETSPEC N GEN_PVAR_234 (N.lt x n) x)) = (@COND (N -> Prop) (n = N0) (@set0 N) (Ninterval N0 (N.sub n ((BIT1 N0))))).
Axiom thm_TOPOLOGICAL_SORT : forall {A : Type'}, forall lt2 : A -> A -> Prop, ((forall x : A, forall y : A, ((lt2 x y) /\ (lt2 y x)) -> x = y) /\ (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z)) -> forall n : N, forall s : A -> Prop, (@HAS_SIZE A s n) -> exists f : N -> A, (s = (@IMAGE N A f (Ninterval ((BIT1 N0)) n))) /\ (forall j : N, forall k : N, ((@IN N j (Ninterval ((BIT1 N0)) n)) /\ ((@IN N k (Ninterval ((BIT1 N0)) n)) /\ (N.lt j k))) -> ~ (lt2 (f k) (f j))).
Axiom thm_FINITE_INT_SEG : (forall l : Z, forall r : Z, @finite_set Z (@GSPEC Z (fun GEN_PVAR_235 : Z => exists x : Z, @SETSPEC Z GEN_PVAR_235 ((Z.le l x) /\ (Z.le x r)) x))) /\ ((forall l : Z, forall r : Z, @finite_set Z (@GSPEC Z (fun GEN_PVAR_236 : Z => exists x : Z, @SETSPEC Z GEN_PVAR_236 ((Z.le l x) /\ (Z.lt x r)) x))) /\ ((forall l : Z, forall r : Z, @finite_set Z (@GSPEC Z (fun GEN_PVAR_237 : Z => exists x : Z, @SETSPEC Z GEN_PVAR_237 ((Z.lt l x) /\ (Z.le x r)) x))) /\ (forall l : Z, forall r : Z, @finite_set Z (@GSPEC Z (fun GEN_PVAR_238 : Z => exists x : Z, @SETSPEC Z GEN_PVAR_238 ((Z.lt l x) /\ (Z.lt x r)) x))))).
Axiom thm_neutral : forall {A : Type'}, forall op : A -> A -> A, (@neutral A op) = (@ε A (fun x : A => forall y : A, ((op x y) = y) /\ ((op y x) = y))).
Axiom thm_monoidal : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) = ((forall x : A, forall y : A, (op x y) = (op y x)) /\ ((forall x : A, forall y : A, forall z : A, (op x (op y z)) = (op (op x y) z)) /\ (forall x : A, (op (@neutral A op) x) = x))).
Axiom thm_MONOIDAL_AC : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) -> (forall a : A, (op (@neutral A op) a) = a) /\ ((forall a : A, (op a (@neutral A op)) = a) /\ ((forall a : A, forall b : A, (op a b) = (op b a)) /\ ((forall a : A, forall b : A, forall c : A, (op (op a b) c) = (op a (op b c))) /\ (forall a : A, forall b : A, forall c : A, (op a (op b c)) = (op b (op a c)))))).
Axiom thm_support : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall op : B -> B -> B, (@support A B op f s) = (@GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))) x)).
Axiom thm_iterate : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall op : B -> B -> B, (@iterate A B op s f) = (@COND B (@finite_set A (@support A B op f s)) (@fold_set A B (fun x : A => fun a : B => op (f x) a) (@support A B op f s) (@neutral B op)) (@neutral B op)).
Axiom thm_IN_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall x : A, forall s : A -> Prop, (@IN A x (@support A B op f s)) = ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))).
Axiom thm_SUPPORT_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@support A B op f (@support A B op f s)) = (@support A B op f s).
Axiom thm_SUPPORT_EMPTY : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (@neutral B op)) = ((@support A B op f s) = (@set0 A)).
Axiom thm_SUPPORT_SUBSET : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, @subset A (@support A B op f s) s.
Axiom thm_FINITE_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> @finite_set A (@support A B op f s).
Axiom thm_SUPPORT_CLAUSES : forall {A B C : Type'} (op : C -> C -> C), (forall f : A -> C, (@support A C op f (@set0 A)) = (@set0 A)) /\ ((forall f : A -> C, forall x : A, forall s : A -> Prop, (@support A C op f (@INSERT A x s)) = (@COND (A -> Prop) ((f x) = (@neutral C op)) (@support A C op f s) (@INSERT A x (@support A C op f s)))) /\ ((forall f : A -> C, forall x : A, forall s : A -> Prop, (@support A C op f (@DELETE A s x)) = (@DELETE A (@support A C op f s) x)) /\ ((forall f : A -> C, forall s : A -> Prop, forall t : A -> Prop, (@support A C op f (@setU A s t)) = (@setU A (@support A C op f s) (@support A C op f t))) /\ ((forall f : A -> C, forall s : A -> Prop, forall t : A -> Prop, (@support A C op f (@setI A s t)) = (@setI A (@support A C op f s) (@support A C op f t))) /\ ((forall f : A -> C, forall s : A -> Prop, forall t : A -> Prop, (@support A C op f (@setD A s t)) = (@setD A (@support A C op f s) (@support A C op f t))) /\ (forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (@support B C op g (@IMAGE A B f s)) = (@IMAGE A B f (@support A C op (@o A B C g f) s)))))))).
Axiom thm_SUPPORT_DELTA : forall {A B : Type'}, forall op : B -> B -> B, forall s : A -> Prop, forall f : A -> B, forall a : A, (@support A B op (fun x : A => @COND B (x = a) (f x) (@neutral B op)) s) = (@COND (A -> Prop) (@IN A a s) (@support A B op f (@INSERT A a (@set0 A))) (@set0 A)).
Axiom thm_FINITE_SUPPORT_DELTA : forall {A B : Type'} (s : A -> Prop), forall op : B -> B -> B, forall f : A -> B, forall a : A, @finite_set A (@support A B op (fun x : A => @COND B (x = a) (f x) (@neutral B op)) s).
Axiom thm_ITERATE_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@iterate A B op (@support A B op f s) f) = (@iterate A B op s f).
Axiom thm_ITERATE_EXPAND_CASES : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@iterate A B op s f) = (@COND B (@finite_set A (@support A B op f s)) (@iterate A B op (@support A B op f s) f) (@neutral B op)).
Axiom thm_ITERATE_CLAUSES_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> (forall f : A -> B, (@iterate A B op (@set0 A) f) = (@neutral B op)) /\ (forall f : A -> B, forall x : A, forall s : A -> Prop, (@finite_set A (@support A B op f s)) -> (@iterate A B op (@INSERT A x s) f) = (@COND B (@IN A x s) (@iterate A B op s f) (op (f x) (@iterate A B op s f)))).
Axiom thm_ITERATE_CLAUSES : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> (forall f : A -> C, (@iterate A C op (@set0 A) f) = (@neutral C op)) /\ (forall f : B -> C, forall x : B, forall s : B -> Prop, (@finite_set B s) -> (@iterate B C op (@INSERT B x s) f) = (@COND C (@IN B x s) (@iterate B C op s f) (op (f x) (@iterate B C op s f)))).
Axiom thm_ITERATE_UNION : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (@DISJOINT A s t))) -> (@iterate A B op (@setU A s t) f) = (op (@iterate A B op s f) (@iterate A B op t f)).
Axiom thm_ITERATE_UNION_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A (@support A B op f s)) /\ ((@finite_set A (@support A B op f t)) /\ (@DISJOINT A (@support A B op f s) (@support A B op f t)))) -> (@iterate A B op (@setU A s t) f) = (op (@iterate A B op s f) (@iterate A B op t f)).
Axiom thm_ITERATE_DIFF : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@subset A t s)) -> (op (@iterate A B op (@setD A s t) f) (@iterate A B op t f)) = (@iterate A B op s f).
Axiom thm_ITERATE_DIFF_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A (@support A B op f s)) /\ (@subset A (@support A B op f t) (@support A B op f s))) -> (op (@iterate A B op (@setD A s t) f) (@iterate A B op t f)) = (@iterate A B op s f).
Axiom thm_ITERATE_INCL_EXCL : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall s : A -> Prop, forall t : A -> Prop, forall f : A -> B, ((@finite_set A s) /\ (@finite_set A t)) -> (op (@iterate A B op s f) (@iterate A B op t f)) = (op (@iterate A B op (@setU A s t) f) (@iterate A B op (@setI A s t) f)).
Axiom thm_ITERATE_CLOSED : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : B -> Prop, ((P (@neutral B op)) /\ (forall x : B, forall y : B, ((P x) /\ (P y)) -> P (op x y))) -> forall f : A -> B, forall s : A -> Prop, (forall x : A, ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))) -> P (f x)) -> P (@iterate A B op s f).
Axiom thm_ITERATE_RELATED : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall R' : B -> B -> Prop, ((R' (@neutral B op) (@neutral B op)) /\ (forall x1 : B, forall y1 : B, forall x2 : B, forall y2 : B, ((R' x1 x2) /\ (R' y1 y2)) -> R' (op x1 y1) (op x2 y2))) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))) -> R' (@iterate A B op s f) (@iterate A B op s g).
Axiom thm_ITERATE_EQ_NEUTRAL : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (@neutral B op)) -> (@iterate A B op s f) = (@neutral B op).
Axiom thm_ITERATE_SING : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall x : A, (@iterate A B op (@INSERT A x (@set0 A)) f) = (f x).
Axiom thm_ITERATE_CLOSED_NONEMPTY : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : B -> Prop, (forall x : B, forall y : B, ((P x) /\ (P y)) -> P (op x y)) -> forall f : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> P (f x)))) -> P (@iterate A B op s f).
Axiom thm_ITERATE_RELATED_NONEMPTY : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall R' : B -> B -> Prop, (forall x1 : B, forall y1 : B, forall x2 : B, forall y2 : B, ((R' x1 x2) /\ (R' y1 y2)) -> R' (op x1 y1) (op x2 y2)) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x)))) -> R' (@iterate A B op s f) (@iterate A B op s g).
Axiom thm_ITERATE_DELETE : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (op (f a) (@iterate A B op (@DELETE A s a) f)) = (@iterate A B op s f).
Axiom thm_ITERATE_DELTA : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall a : A, forall s : A -> Prop, (@iterate A B op s (fun x : A => @COND B (x = a) (f x) (@neutral B op))) = (@COND B (@IN A a s) (f a) (@neutral B op)).
Axiom thm_ITERATE_IMAGE : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@iterate B C op (@IMAGE A B f s) g) = (@iterate A C op s (@o A B C g f)).
Axiom thm_ITERATE_BIJECTION : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@iterate A B op s f) = (@iterate A B op s (@o A A B f p)).
Axiom thm_ITERATE_ITERATE_PRODUCT : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> C, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> @finite_set B (t i))) -> (@iterate A C op s (fun i : A => @iterate B C op (t i) (x i))) = (@iterate (prod A B) C op (@GSPEC (prod A B) (fun GEN_PVAR_243 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_243 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@ε ((prod A B) -> C) (fun f : (prod A B) -> C => forall i : A, forall j : B, @eq C (f (@pair A B i j)) (x i j)))).
Axiom thm_ITERATE_EQ : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@iterate A B op s f) = (@iterate A B op s g).
Axiom thm_ITERATE_RESTRICT_SET : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : A -> Prop, forall s : A -> Prop, forall f : A -> B, (@iterate A B op (@GSPEC A (fun GEN_PVAR_244 : A => exists x : A, @SETSPEC A GEN_PVAR_244 ((@IN A x s) /\ (P x)) x)) f) = (@iterate A B op s (fun x : A => @COND B (P x) (f x) (@neutral B op))).
Axiom thm_ITERATE_EQ_GENERAL : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : B -> Prop, forall f : A -> C, forall g : B -> C, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@iterate A C op s f) = (@iterate B C op t g).
Axiom thm_ITERATE_EQ_GENERAL_INVERSES : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : B -> Prop, forall f : A -> C, forall g : B -> C, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@iterate A C op s f) = (@iterate B C op t g).
Axiom thm_ITERATE_INJECTION : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall p : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((p x) = (p y)))) -> x = y))) -> (@iterate A B op s (@o A A B f p)) = (@iterate A B op s f).
Axiom thm_ITERATE_UNION_NONZERO : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (forall x : A, (@IN A x (@setI A s t)) -> (f x) = (@neutral B op)))) -> (@iterate A B op (@setU A s t) f) = (op (@iterate A B op s f) (@iterate A B op t f)).
Axiom thm_ITERATE_OP : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, (@finite_set A s) -> (@iterate A B op s (fun x : A => op (f x) (g x))) = (op (@iterate A B op s f) (@iterate A B op s g)).
Axiom thm_ITERATE_SUPERSET : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall u : A -> Prop, forall v : A -> Prop, ((@subset A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (@neutral B op))) -> (@iterate A B op v f) = (@iterate A B op u f).
Axiom thm_ITERATE_UNIV : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, (@subset A (@support A B op f (@setT A)) s) -> (@iterate A B op s f) = (@iterate A B op (@setT A) f).
Axiom thm_ITERATE_SWAP : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B -> C, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@iterate A C op s (fun i : A => @iterate B C op t (f i))) = (@iterate B C op t (fun j : B => @iterate A C op s (fun i : A => f i j))).
Axiom thm_ITERATE_IMAGE_NONZERO : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall g : B -> C, forall f : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((f x) = (f y))))) -> (g (f x)) = (@neutral C op))) -> (@iterate B C op (@IMAGE A B f s) g) = (@iterate A C op s (@o A B C g f)).
Axiom thm_ITERATE_IMAGE_GEN : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B, forall g : A -> C, forall s : A -> Prop, (@finite_set A s) -> (@iterate A C op s g) = (@iterate B C op (@IMAGE A B f s) (fun y : B => @iterate A C op (@GSPEC A (fun GEN_PVAR_247 : A => exists x : A, @SETSPEC A GEN_PVAR_247 ((@IN A x s) /\ ((f x) = y)) x)) g)).
Axiom thm_ITERATE_CASES : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall s : A -> Prop, forall P : A -> Prop, forall f : A -> B, forall g : A -> B, (@finite_set A s) -> (@iterate A B op s (fun x : A => @COND B (P x) (f x) (g x))) = (op (@iterate A B op (@GSPEC A (fun GEN_PVAR_250 : A => exists x : A, @SETSPEC A GEN_PVAR_250 ((@IN A x s) /\ (P x)) x)) f) (@iterate A B op (@GSPEC A (fun GEN_PVAR_251 : A => exists x : A, @SETSPEC A GEN_PVAR_251 ((@IN A x s) /\ (~ (P x))) x)) g)).
Axiom thm_ITERATE_OP_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@finite_set A (@support A B op f s)) /\ (@finite_set A (@support A B op g s))) -> (@iterate A B op s (fun x : A => op (f x) (g x))) = (op (@iterate A B op s f) (@iterate A B op s g)).
Axiom thm_ITERATE_CLAUSES_NUMSEG : forall {A : Type'} (f : N -> A), forall op : A -> A -> A, (@monoidal A op) -> (forall m : N, (@iterate N A op (Ninterval m N0) f) = (@COND A (m = N0) (f N0) (@neutral A op))) /\ (forall m : N, forall n : N, (@iterate N A op (Ninterval m (N.succ n)) f) = (@COND A (N.le m (N.succ n)) (op (@iterate N A op (Ninterval m n) f) (f (N.succ n))) (@iterate N A op (Ninterval m n) f))).
Axiom thm_ITERATE_CLAUSES_NUMSEG_LT : forall {A : Type'} (f : N -> A), forall op : A -> A -> A, (@monoidal A op) -> ((@iterate N A op (@GSPEC N (fun GEN_PVAR_256 : N => exists i : N, @SETSPEC N GEN_PVAR_256 (N.lt i N0) i)) f) = (@neutral A op)) /\ (forall k : N, (@iterate N A op (@GSPEC N (fun GEN_PVAR_257 : N => exists i : N, @SETSPEC N GEN_PVAR_257 (N.lt i (N.succ k)) i)) f) = (op (@iterate N A op (@GSPEC N (fun GEN_PVAR_258 : N => exists i : N, @SETSPEC N GEN_PVAR_258 (N.lt i k) i)) f) (f k))).
Axiom thm_ITERATE_CLAUSES_NUMSEG_LE : forall {A : Type'} (f : N -> A), forall op : A -> A -> A, (@monoidal A op) -> ((@iterate N A op (@GSPEC N (fun GEN_PVAR_259 : N => exists i : N, @SETSPEC N GEN_PVAR_259 (N.le i N0) i)) f) = (f N0)) /\ (forall k : N, (@iterate N A op (@GSPEC N (fun GEN_PVAR_260 : N => exists i : N, @SETSPEC N GEN_PVAR_260 (N.le i (N.succ k)) i)) f) = (op (@iterate N A op (@GSPEC N (fun GEN_PVAR_261 : N => exists i : N, @SETSPEC N GEN_PVAR_261 (N.le i k) i)) f) (f (N.succ k)))).
Axiom thm_ITERATE_PAIR : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) -> forall f : N -> A, forall m : N, forall n : N, (@iterate N A op (Ninterval (N.mul ((BIT0 (BIT1 N0))) m) (N.add (N.mul ((BIT0 (BIT1 N0))) n) ((BIT1 N0)))) f) = (@iterate N A op (Ninterval m n) (fun i : N => op (f (N.mul ((BIT0 (BIT1 N0))) i)) (f (N.add (N.mul ((BIT0 (BIT1 N0))) i) ((BIT1 N0)))))).
Axiom thm_ITERATE_REFLECT : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) -> forall x : N -> A, forall m : N, forall n : N, (@iterate N A op (Ninterval m n) x) = (@COND A (N.lt n m) (@neutral A op) (@iterate N A op (Ninterval N0 (N.sub n m)) (fun i : N => x (N.sub n i)))).
Axiom thm_ITERATO_SUPPORT : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (@iterato A K dom neut op ltle (@GSPEC K (fun GEN_PVAR_270 : K => exists i : K, @SETSPEC K GEN_PVAR_270 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) f) = (@iterato A K dom neut op ltle k f).
Axiom thm_ITERATO_EXPAND_CASES : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (@iterato A K dom neut op ltle k f) = (@COND A (@finite_set K (@GSPEC K (fun GEN_PVAR_271 : K => exists i : K, @SETSPEC K GEN_PVAR_271 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) (@iterato A K dom neut op ltle (@GSPEC K (fun GEN_PVAR_272 : K => exists i : K, @SETSPEC K GEN_PVAR_272 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) f) neut).
Axiom thm_ITERATO_CLAUSES_GEN : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@set0 K) f) = neut) /\ (forall i : K, forall k : K -> Prop, ((@finite_set K (@GSPEC K (fun GEN_PVAR_274 : K => exists j : K, @SETSPEC K GEN_PVAR_274 ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j))) /\ ((forall j : K, (@IN K j k) -> (i = j) \/ ((ltle i j) \/ (ltle j i))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) -> (@iterato A K dom neut op ltle (@INSERT K i k) f) = (@COND A ((@IN A (f i) dom) -> ((f i) = neut) \/ (@IN K i k)) (@iterato A K dom neut op ltle k f) (op (f i) (@iterato A K dom neut op ltle k f)))).
Axiom thm_ITERATO_CLAUSES : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@set0 K) f) = neut) /\ (forall i : K, forall k : K -> Prop, ((@finite_set K (@GSPEC K (fun GEN_PVAR_275 : K => exists i' : K, @SETSPEC K GEN_PVAR_275 ((@IN K i' k) /\ (@IN A (f i') (@setD A dom (@INSERT A neut (@set0 A))))) i'))) /\ (forall j : K, (@IN K j k) -> (ltle i j) /\ (~ (ltle j i)))) -> (@iterato A K dom neut op ltle (@INSERT K i k) f) = (@COND A ((@IN A (f i) dom) -> ((f i) = neut) \/ (@IN K i k)) (@iterato A K dom neut op ltle k f) (op (f i) (@iterato A K dom neut op ltle k f)))).
Axiom thm_ITERATO_CLAUSES_EXISTS : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@set0 K) f) = neut) /\ (forall k : K -> Prop, ((@finite_set K (@GSPEC K (fun GEN_PVAR_276 : K => exists i : K, @SETSPEC K GEN_PVAR_276 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_277 : K => exists i : K, @SETSPEC K GEN_PVAR_277 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) -> exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ ((@iterato A K dom neut op ltle k f) = (op (f i) (@iterato A K dom neut op ltle (@DELETE K k i) f))))).
Axiom thm_ITERATO_EQ : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall g : K -> A, (forall i : K, (@IN K i k) -> (f i) = (g i)) -> (@iterato A K dom neut op ltle k f) = (@iterato A K dom neut op ltle k g).
Axiom thm_ITERATO_INDUCT : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall P : A -> Prop, ((P neut) /\ (forall i : K, forall x : A, ((@IN K i k) /\ ((@IN A (f i) dom) /\ ((~ ((f i) = neut)) /\ (P x)))) -> P (op (f i) x))) -> P (@iterato A K dom neut op ltle k f).
Axiom thm_ITERATO_CLOSED : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall P : A -> Prop, ((P neut) /\ ((forall x : A, forall y : A, ((P x) /\ (P y)) -> P (op x y)) /\ (forall i : K, ((@IN K i k) /\ ((@IN A (f i) dom) /\ (~ ((f i) = neut)))) -> P (f i)))) -> P (@iterato A K dom neut op ltle k f).
Axiom thm_ITERATO_ITERATE : forall {A K : Type'}, forall op : A -> A -> A, forall ltle : K -> K -> Prop, (@monoidal A op) -> (@iterato A K (@setT A) (@neutral A op) op ltle) = (@iterate K A op).
Axiom thm_ITERATO_CLAUSES_NUMSEG_LEFT : forall {A : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall f : N -> A, forall m : N, forall n : N, (@iterato A N dom neut op N.le (Ninterval m n) f) = (@COND A (N.le m n) (@COND A ((@IN A (f m) dom) -> (f m) = neut) (@iterato A N dom neut op N.le (Ninterval (N.add m ((BIT1 N0))) n) f) (op (f m) (@iterato A N dom neut op N.le (Ninterval (N.add m ((BIT1 N0))) n) f))) neut).
Axiom thm_nproduct : forall {A : Type'}, (@nproduct A) = (@iterate A N N.mul).
Axiom thm_NEUTRAL_MUL : (@neutral N N.mul) = ((BIT1 N0)).
Axiom thm_MONOIDAL_MUL : @monoidal N N.mul.
Axiom thm_NPRODUCT_CLAUSES : forall {A B : Type'}, (forall f : A -> N, (@nproduct A (@set0 A) f) = ((BIT1 N0))) /\ (forall x : B, forall f : B -> N, forall s : B -> Prop, (@finite_set B s) -> (@nproduct B (@INSERT B x s) f) = (@COND N (@IN B x s) (@nproduct B s f) (N.mul (f x) (@nproduct B s f)))).
Axiom thm_iproduct : forall {A : Type'}, (@iproduct A) = (@iterate A Z Z.mul).
Axiom thm_NEUTRAL_INT_MUL : (@neutral Z Z.mul) = (Z_of_N ((BIT1 N0))).
Axiom thm_MONOIDAL_INT_MUL : @monoidal Z Z.mul.
Axiom thm_IPRODUCT_CLAUSES : forall {A B : Type'}, (forall f : A -> Z, (@iproduct A (@set0 A) f) = (Z_of_N ((BIT1 N0)))) /\ (forall x : B, forall f : B -> Z, forall s : B -> Prop, (@finite_set B s) -> (@iproduct B (@INSERT B x s) f) = (@COND Z (@IN B x s) (@iproduct B s f) (Z.mul (f x) (@iproduct B s f)))).
Axiom thm_product : forall {A : Type'}, (@product A) = (@iterate A R Rmult).
Axiom thm_NEUTRAL_REAL_MUL : (@neutral R Rmult) = (R_of_N ((BIT1 N0))).
Axiom thm_MONOIDAL_REAL_MUL : @monoidal R Rmult.
Axiom thm_PRODUCT_CLAUSES : forall {A B : Type'}, (forall f : A -> R, (@product A (@set0 A) f) = (R_of_N ((BIT1 N0)))) /\ (forall x : B, forall f : B -> R, forall s : B -> Prop, (@finite_set B s) -> (@product B (@INSERT B x s) f) = (@COND R (@IN B x s) (@product B s f) (Rmult (f x) (@product B s f)))).
Axiom thm_isum : forall {A : Type'}, (@isum A) = (@iterate A Z Z.add).
Axiom thm_NEUTRAL_INT_ADD : (@neutral Z Z.add) = (Z_of_N N0).
Axiom thm_MONOIDAL_INT_ADD : @monoidal Z Z.add.
Axiom thm_ISUM_CLAUSES : forall {A B : Type'}, (forall f : A -> Z, (@isum A (@set0 A) f) = (Z_of_N N0)) /\ (forall x : B, forall f : B -> Z, forall s : B -> Prop, (@finite_set B s) -> (@isum B (@INSERT B x s) f) = (@COND Z (@IN B x s) (@isum B s f) (Z.add (f x) (@isum B s f)))).
Axiom thm_nsum : forall {A : Type'}, (@nsum A) = (@iterate A N N.add).
Axiom thm_NEUTRAL_ADD : (@neutral N N.add) = N0.
Axiom thm_MONOIDAL_ADD : @monoidal N N.add.
Axiom thm_NSUM_DEGENERATE : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, (~ (@finite_set A (@GSPEC A (fun GEN_PVAR_286 : A => exists x : A, @SETSPEC A GEN_PVAR_286 ((@IN A x s) /\ (~ ((f x) = N0))) x)))) -> (@nsum A s f) = N0.
Axiom thm_NSUM_CLAUSES : forall {A B : Type'}, (forall f : A -> N, (@nsum A (@set0 A) f) = N0) /\ (forall x : B, forall f : B -> N, forall s : B -> Prop, (@finite_set B s) -> (@nsum B (@INSERT B x s) f) = (@COND N (@IN B x s) (@nsum B s f) (N.add (f x) (@nsum B s f)))).
Axiom thm_NSUM_UNION : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (@DISJOINT A s t))) -> (@nsum A (@setU A s t) f) = (N.add (@nsum A s f) (@nsum A t f)).
Axiom thm_NSUM_DIFF : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@subset A t s)) -> (@nsum A (@setD A s t) f) = (N.sub (@nsum A s f) (@nsum A t f)).
Axiom thm_NSUM_INCL_EXCL : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> N, ((@finite_set A s) /\ (@finite_set A t)) -> (N.add (@nsum A s f) (@nsum A t f)) = (N.add (@nsum A (@setU A s t) f) (@nsum A (@setI A s t) f)).
Axiom thm_NSUM_SUPPORT : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, (@nsum A (@support A N N.add f s) f) = (@nsum A s f).
Axiom thm_NSUM_ADD : forall {A : Type'}, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s (fun x : A => N.add (f x) (g x))) = (N.add (@nsum A s f) (@nsum A s g)).
Axiom thm_NSUM_ADD_GEN : forall {A : Type'}, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((@finite_set A (@GSPEC A (fun GEN_PVAR_287 : A => exists x : A, @SETSPEC A GEN_PVAR_287 ((@IN A x s) /\ (~ ((f x) = N0))) x))) /\ (@finite_set A (@GSPEC A (fun GEN_PVAR_288 : A => exists x : A, @SETSPEC A GEN_PVAR_288 ((@IN A x s) /\ (~ ((g x) = N0))) x)))) -> (@nsum A s (fun x : A => N.add (f x) (g x))) = (N.add (@nsum A s f) (@nsum A s g)).
Axiom thm_NSUM_EQ_0 : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = N0) -> (@nsum A s f) = N0.
Axiom thm_NSUM_0 : forall {A : Type'}, forall s : A -> Prop, (@nsum A s (fun n : A => N0)) = N0.
Axiom thm_NSUM_LMUL : forall {A : Type'}, forall f : A -> N, forall c : N, forall s : A -> Prop, (@nsum A s (fun x : A => N.mul c (f x))) = (N.mul c (@nsum A s f)).
Axiom thm_NSUM_RMUL : forall {A : Type'}, forall f : A -> N, forall c : N, forall s : A -> Prop, (@nsum A s (fun x : A => N.mul (f x) c)) = (N.mul (@nsum A s f) c).
Axiom thm_NSUM_LE : forall {A : Type'}, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> N.le (f x) (g x))) -> N.le (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_LT : forall {A : Type'}, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> N.le (f x) (g x)) /\ (exists x : A, (@IN A x s) /\ (N.lt (f x) (g x))))) -> N.lt (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_LT_ALL : forall {A : Type'}, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> N.lt (f x) (g x)))) -> N.lt (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_EQ : forall {A : Type'}, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@nsum A s f) = (@nsum A s g).
Axiom thm_NSUM_CONST : forall {A : Type'}, forall c : N, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s (fun n : A => c)) = (N.mul (@card A s) c).
Axiom thm_NSUM_POS_BOUND : forall {A : Type'}, forall f : A -> N, forall b : N, forall s : A -> Prop, ((@finite_set A s) /\ (N.le (@nsum A s f) b)) -> forall x : A, (@IN A x s) -> N.le (f x) b.
Axiom thm_NSUM_EQ_0_IFF : forall {A : Type'} (f : A -> N), forall s : A -> Prop, (@finite_set A s) -> ((@nsum A s f) = N0) = (forall x : A, (@IN A x s) -> (f x) = N0).
Axiom thm_NSUM_POS_LT : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, ((@finite_set A s) /\ (exists x : A, (@IN A x s) /\ (N.lt N0 (f x)))) -> N.lt N0 (@nsum A s f).
Axiom thm_NSUM_POS_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> N, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall i : A, (@IN A i s) -> N.lt N0 (f i)))) -> N.lt N0 (@nsum A s f).
Axiom thm_NSUM_DELETE : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (N.add (f a) (@nsum A (@DELETE A s a) f)) = (@nsum A s f).
Axiom thm_NSUM_SING : forall {A : Type'}, forall f : A -> N, forall x : A, (@nsum A (@INSERT A x (@set0 A)) f) = (f x).
Axiom thm_NSUM_DELTA : forall {A : Type'} (b : N), forall s : A -> Prop, forall a : A, (@nsum A s (fun x : A => @COND N (x = a) b N0)) = (@COND N (@IN A a s) b N0).
Axiom thm_NSUM_SWAP : forall {A B : Type'}, forall f : A -> B -> N, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@nsum A s (fun i : A => @nsum B t (f i))) = (@nsum B t (fun j : B => @nsum A s (fun i : A => f i j))).
Axiom thm_NSUM_IMAGE : forall {A B : Type'}, forall f : A -> B, forall g : B -> N, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@nsum B (@IMAGE A B f s) g) = (@nsum A s (@o A B N g f)).
Axiom thm_NSUM_SUPERSET : forall {A : Type'}, forall f : A -> N, forall u : A -> Prop, forall v : A -> Prop, ((@subset A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = N0)) -> (@nsum A v f) = (@nsum A u f).
Axiom thm_NSUM_UNIV : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, (@subset A (@support A N N.add f (@setT A)) s) -> (@nsum A s f) = (@nsum A (@setT A) f).
Axiom thm_NSUM_UNION_RZERO : forall {A : Type'}, forall f : A -> N, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A u) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = N0)) -> (@nsum A (@setU A u v) f) = (@nsum A u f).
Axiom thm_NSUM_UNION_LZERO : forall {A : Type'}, forall f : A -> N, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A v) /\ (forall x : A, ((@IN A x u) /\ (~ (@IN A x v))) -> (f x) = N0)) -> (@nsum A (@setU A u v) f) = (@nsum A v f).
Axiom thm_NSUM_RESTRICT : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s (fun x : A => @COND N (@IN A x s) (f x) N0)) = (@nsum A s f).
Axiom thm_NSUM_BOUND : forall {A : Type'}, forall s : A -> Prop, forall f : A -> N, forall b : N, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> N.le (f x) b)) -> N.le (@nsum A s f) (N.mul (@card A s) b).
Axiom thm_NSUM_BOUND_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> N, forall b : N, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> N.le (f x) (N.div b (@card A s))))) -> N.le (@nsum A s f) b.
Axiom thm_NSUM_BOUND_LT : forall {A : Type'}, forall s : A -> Prop, forall f : A -> N, forall b : N, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> N.le (f x) b) /\ (exists x : A, (@IN A x s) /\ (N.lt (f x) b)))) -> N.lt (@nsum A s f) (N.mul (@card A s) b).
Axiom thm_NSUM_BOUND_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> N, forall b : N, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> N.lt (f x) b))) -> N.lt (@nsum A s f) (N.mul (@card A s) b).
Axiom thm_NSUM_BOUND_LT_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> N, forall b : N, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> N.lt (f x) (N.div b (@card A s))))) -> N.lt (@nsum A s f) b.
Axiom thm_NSUM_UNION_EQ : forall {A : Type'} (f : A -> N), forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@finite_set A u) /\ (((@setI A s t) = (@set0 A)) /\ ((@setU A s t) = u))) -> (N.add (@nsum A s f) (@nsum A t f)) = (@nsum A u f).
Axiom thm_NSUM_EQ_SUPERSET : forall {A : Type'} (g : A -> N), forall f : A -> N, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ ((@subset A t s) /\ ((forall x : A, (@IN A x t) -> (f x) = (g x)) /\ (forall x : A, ((@IN A x s) /\ (~ (@IN A x t))) -> (f x) = N0)))) -> (@nsum A s f) = (@nsum A t g).
Axiom thm_NSUM_RESTRICT_SET : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall f : A -> N, (@nsum A (@GSPEC A (fun GEN_PVAR_289 : A => exists x : A, @SETSPEC A GEN_PVAR_289 ((@IN A x s) /\ (P x)) x)) f) = (@nsum A s (fun x : A => @COND N (P x) (f x) N0)).
Axiom thm_NSUM_NSUM_RESTRICT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall f : A -> B -> N, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@nsum A s (fun x : A => @nsum B (@GSPEC B (fun GEN_PVAR_290 : B => exists y : B, @SETSPEC B GEN_PVAR_290 ((@IN B y t) /\ (R' x y)) y)) (fun y : B => f x y))) = (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_291 : A => exists x : A, @SETSPEC A GEN_PVAR_291 ((@IN A x s) /\ (R' x y)) x)) (fun x : A => f x y))).
Axiom thm_CARD_EQ_NSUM : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@card A s) = (@nsum A s (fun x : A => (BIT1 N0))).
Axiom thm_NSUM_MULTICOUNT_GEN : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : B -> N, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@card A (@GSPEC A (fun GEN_PVAR_293 : A => exists i : A, @SETSPEC A GEN_PVAR_293 ((@IN A i s) /\ (R' i j)) i))) = (k j)))) -> (@nsum A s (fun i : A => @card B (@GSPEC B (fun GEN_PVAR_294 : B => exists j : B, @SETSPEC B GEN_PVAR_294 ((@IN B j t) /\ (R' i j)) j)))) = (@nsum B t (fun i : B => k i)).
Axiom thm_NSUM_MULTICOUNT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : N, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@card A (@GSPEC A (fun GEN_PVAR_295 : A => exists i : A, @SETSPEC A GEN_PVAR_295 ((@IN A i s) /\ (R' i j)) i))) = k))) -> (@nsum A s (fun i : A => @card B (@GSPEC B (fun GEN_PVAR_296 : B => exists j : B, @SETSPEC B GEN_PVAR_296 ((@IN B j t) /\ (R' i j)) j)))) = (N.mul k (@card B t)).
Axiom thm_NSUM_IMAGE_GEN : forall {A B : Type'}, forall f : A -> B, forall g : A -> N, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s g) = (@nsum B (@IMAGE A B f s) (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_297 : A => exists x : A, @SETSPEC A GEN_PVAR_297 ((@IN A x s) /\ ((f x) = y)) x)) g)).
Axiom thm_NSUM_GROUP : forall {A B : Type'}, forall f : A -> B, forall g : A -> N, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@subset B (@IMAGE A B f s) t)) -> (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_298 : A => exists x : A, @SETSPEC A GEN_PVAR_298 ((@IN A x s) /\ ((f x) = y)) x)) g)) = (@nsum A s g).
Axiom thm_NSUM_GROUP_RELATION : forall {A B : Type'}, forall R' : A -> B -> Prop, forall g : A -> N, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @ex1 B (fun y : B => (@IN B y t) /\ (R' x y)))) -> (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_299 : A => exists x : A, @SETSPEC A GEN_PVAR_299 ((@IN A x s) /\ (R' x y)) x)) g)) = (@nsum A s g).
Axiom thm_NSUM_SUBSET : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> N, ((@finite_set A u) /\ ((@finite_set A v) /\ (forall x : A, (@IN A x (@setD A u v)) -> (f x) = N0))) -> N.le (@nsum A u f) (@nsum A v f).
Axiom thm_NSUM_SUBSET_SIMPLE : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> N, ((@finite_set A v) /\ (@subset A u v)) -> N.le (@nsum A u f) (@nsum A v f).
Axiom thm_NSUM_LE_GEN : forall {A : Type'}, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> N.le (f x) (g x)) /\ (@finite_set A (@GSPEC A (fun GEN_PVAR_301 : A => exists x : A, @SETSPEC A GEN_PVAR_301 ((@IN A x s) /\ (~ ((g x) = N0))) x)))) -> N.le (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_MUL_BOUND : forall {A : Type'}, forall a : A -> N, forall b : A -> N, forall s : A -> Prop, (@finite_set A s) -> N.le (@nsum A s (fun i : A => N.mul (a i) (b i))) (N.mul (@nsum A s a) (@nsum A s b)).
Axiom thm_NSUM_IMAGE_NONZERO : forall {A B : Type'}, forall d : B -> N, forall i : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((i x) = (i y))))) -> (d (i x)) = N0)) -> (@nsum B (@IMAGE A B i s) d) = (@nsum A s (@o A B N d i)).
Axiom thm_NSUM_BIJECTION : forall {A : Type'}, forall f : A -> N, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@nsum A s f) = (@nsum A s (@o A A N f p)).
Axiom thm_NSUM_NSUM_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> N, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> @finite_set B (t i))) -> (@nsum A s (fun i : A => @nsum B (t i) (x i))) = (@nsum (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_302 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_302 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@ε ((prod A B) -> N) (fun f : (prod A B) -> N => forall i : A, forall j : B, @eq N (f (@pair A B i j)) (x i j)))).
Axiom thm_NSUM_EQ_GENERAL : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> N, forall g : B -> N, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@nsum A s f) = (@nsum B t g).
Axiom thm_NSUM_EQ_GENERAL_INVERSES : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> N, forall g : B -> N, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@nsum A s f) = (@nsum B t g).
Axiom thm_NSUM_INJECTION : forall {A : Type'}, forall f : A -> N, forall p : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((p x) = (p y)))) -> x = y))) -> (@nsum A s (@o A A N f p)) = (@nsum A s f).
Axiom thm_NSUM_UNION_NONZERO : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (forall x : A, (@IN A x (@setI A s t)) -> (f x) = N0))) -> (@nsum A (@setU A s t) f) = (N.add (@nsum A s f) (@nsum A t f)).
Axiom thm_NSUM_UNIONS_NONZERO : forall {A : Type'}, forall f : A -> N, forall s : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t) /\ (forall t1 : A -> Prop, forall t2 : A -> Prop, forall x : A, ((@IN (A -> Prop) t1 s) /\ ((@IN (A -> Prop) t2 s) /\ ((~ (t1 = t2)) /\ ((@IN A x t1) /\ (@IN A x t2))))) -> (f x) = N0))) -> (@nsum A (@UNIONS A s) f) = (@nsum (A -> Prop) s (fun t : A -> Prop => @nsum A t f)).
Axiom thm_NSUM_CASES : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, forall f : A -> N, forall g : A -> N, (@finite_set A s) -> (@nsum A s (fun x : A => @COND N (P x) (f x) (g x))) = (N.add (@nsum A (@GSPEC A (fun GEN_PVAR_303 : A => exists x : A, @SETSPEC A GEN_PVAR_303 ((@IN A x s) /\ (P x)) x)) f) (@nsum A (@GSPEC A (fun GEN_PVAR_304 : A => exists x : A, @SETSPEC A GEN_PVAR_304 ((@IN A x s) /\ (~ (P x))) x)) g)).
Axiom thm_NSUM_CLOSED : forall {A : Type'}, forall P : N -> Prop, forall f : A -> N, forall s : A -> Prop, ((P N0) /\ ((forall x : N, forall y : N, ((P x) /\ (P y)) -> P (N.add x y)) /\ (forall a : A, (@IN A a s) -> P (f a)))) -> P (@nsum A s f).
Axiom thm_NSUM_RELATED : forall {A : Type'}, forall R' : N -> N -> Prop, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((R' N0 N0) /\ ((forall m : N, forall n : N, forall m' : N, forall n' : N, ((R' m n) /\ (R' m' n')) -> R' (N.add m m') (N.add n n')) /\ ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_CLOSED_NONEMPTY : forall {A : Type'}, forall P : N -> Prop, forall f : A -> N, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ ((forall x : N, forall y : N, ((P x) /\ (P y)) -> P (N.add x y)) /\ (forall a : A, (@IN A a s) -> P (f a))))) -> P (@nsum A s f).
Axiom thm_NSUM_RELATED_NONEMPTY : forall {A : Type'}, forall R' : N -> N -> Prop, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((forall m : N, forall n : N, forall m' : N, forall n' : N, ((R' m n) /\ (R' m' n')) -> R' (N.add m m') (N.add n n')) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_ADD_NUMSEG : forall f : N -> N, forall g : N -> N, forall m : N, forall n : N, (@nsum N (Ninterval m n) (fun i : N => N.add (f i) (g i))) = (N.add (@nsum N (Ninterval m n) f) (@nsum N (Ninterval m n) g)).
Axiom thm_NSUM_LE_NUMSEG : forall f : N -> N, forall g : N -> N, forall m : N, forall n : N, (forall i : N, ((N.le m i) /\ (N.le i n)) -> N.le (f i) (g i)) -> N.le (@nsum N (Ninterval m n) f) (@nsum N (Ninterval m n) g).
Axiom thm_NSUM_EQ_NUMSEG : forall f : N -> N, forall g : N -> N, forall m : N, forall n : N, (forall i : N, ((N.le m i) /\ (N.le i n)) -> (f i) = (g i)) -> (@nsum N (Ninterval m n) f) = (@nsum N (Ninterval m n) g).
Axiom thm_NSUM_CONST_NUMSEG : forall c : N, forall m : N, forall n : N, (@nsum N (Ninterval m n) (fun n' : N => c)) = (N.mul (N.sub (N.add n ((BIT1 N0))) m) c).
Axiom thm_NSUM_EQ_0_NUMSEG : forall f : N -> N, forall m : N, forall n : N, (forall i : N, ((N.le m i) /\ (N.le i n)) -> (f i) = N0) -> (@nsum N (Ninterval m n) f) = N0.
Axiom thm_NSUM_EQ_0_IFF_NUMSEG : forall f : N -> N, forall m : N, forall n : N, ((@nsum N (Ninterval m n) f) = N0) = (forall i : N, ((N.le m i) /\ (N.le i n)) -> (f i) = N0).
Axiom thm_NSUM_TRIV_NUMSEG : forall f : N -> N, forall m : N, forall n : N, (N.lt n m) -> (@nsum N (Ninterval m n) f) = N0.
Axiom thm_NSUM_SING_NUMSEG : forall f : N -> N, forall n : N, (@nsum N (Ninterval n n) f) = (f n).
Axiom thm_NSUM_CLAUSES_NUMSEG : forall (f : N -> N), (forall m : N, (@nsum N (Ninterval m N0) f) = (@COND N (m = N0) (f N0) N0)) /\ (forall m : N, forall n : N, (@nsum N (Ninterval m (N.succ n)) f) = (@COND N (N.le m (N.succ n)) (N.add (@nsum N (Ninterval m n) f) (f (N.succ n))) (@nsum N (Ninterval m n) f))).
Axiom thm_NSUM_CLAUSES_NUMSEG_LT : forall (f : N -> N), ((@nsum N (@GSPEC N (fun GEN_PVAR_305 : N => exists i : N, @SETSPEC N GEN_PVAR_305 (N.lt i N0) i)) f) = N0) /\ (forall k : N, (@nsum N (@GSPEC N (fun GEN_PVAR_306 : N => exists i : N, @SETSPEC N GEN_PVAR_306 (N.lt i (N.succ k)) i)) f) = (N.add (@nsum N (@GSPEC N (fun GEN_PVAR_307 : N => exists i : N, @SETSPEC N GEN_PVAR_307 (N.lt i k) i)) f) (f k))).
Axiom thm_NSUM_CLAUSES_NUMSEG_LE : forall (f : N -> N), ((@nsum N (@GSPEC N (fun GEN_PVAR_308 : N => exists i : N, @SETSPEC N GEN_PVAR_308 (N.le i N0) i)) f) = (f N0)) /\ (forall k : N, (@nsum N (@GSPEC N (fun GEN_PVAR_309 : N => exists i : N, @SETSPEC N GEN_PVAR_309 (N.le i (N.succ k)) i)) f) = (N.add (@nsum N (@GSPEC N (fun GEN_PVAR_310 : N => exists i : N, @SETSPEC N GEN_PVAR_310 (N.le i k) i)) f) (f (N.succ k)))).
Axiom thm_NSUM_SWAP_NUMSEG : forall a : N, forall b : N, forall c : N, forall d : N, forall f : N -> N -> N, (@nsum N (Ninterval a b) (fun i : N => @nsum N (Ninterval c d) (f i))) = (@nsum N (Ninterval c d) (fun j : N => @nsum N (Ninterval a b) (fun i : N => f i j))).
Axiom thm_NSUM_ADD_SPLIT : forall f : N -> N, forall m : N, forall n : N, forall p : N, (N.le m (N.add n ((BIT1 N0)))) -> (@nsum N (Ninterval m (N.add n p)) f) = (N.add (@nsum N (Ninterval m n) f) (@nsum N (Ninterval (N.add n ((BIT1 N0))) (N.add n p)) f)).
Axiom thm_NSUM_OFFSET : forall p : N, forall f : N -> N, forall m : N, forall n : N, (@nsum N (Ninterval (N.add m p) (N.add n p)) f) = (@nsum N (Ninterval m n) (fun i : N => f (N.add i p))).
Axiom thm_NSUM_OFFSET_0 : forall f : N -> N, forall m : N, forall n : N, (N.le m n) -> (@nsum N (Ninterval m n) f) = (@nsum N (Ninterval N0 (N.sub n m)) (fun i : N => f (N.add i m))).
Axiom thm_NSUM_CLAUSES_LEFT : forall f : N -> N, forall m : N, forall n : N, (N.le m n) -> (@nsum N (Ninterval m n) f) = (N.add (f m) (@nsum N (Ninterval (N.add m ((BIT1 N0))) n) f)).
Axiom thm_NSUM_CLAUSES_RIGHT : forall f : N -> N, forall m : N, forall n : N, ((N.lt N0 n) /\ (N.le m n)) -> (@nsum N (Ninterval m n) f) = (N.add (@nsum N (Ninterval m (N.sub n ((BIT1 N0)))) f) (f n)).
Axiom thm_NSUM_PAIR : forall f : N -> N, forall m : N, forall n : N, (@nsum N (Ninterval (N.mul ((BIT0 (BIT1 N0))) m) (N.add (N.mul ((BIT0 (BIT1 N0))) n) ((BIT1 N0)))) f) = (@nsum N (Ninterval m n) (fun i : N => N.add (f (N.mul ((BIT0 (BIT1 N0))) i)) (f (N.add (N.mul ((BIT0 (BIT1 N0))) i) ((BIT1 N0)))))).
Axiom thm_NSUM_REFLECT : forall x : N -> N, forall m : N, forall n : N, (@nsum N (Ninterval m n) x) = (@COND N (N.lt n m) N0 (@nsum N (Ninterval N0 (N.sub n m)) (fun i : N => x (N.sub n i)))).
Axiom thm_MOD_NSUM_MOD : forall {A : Type'}, forall f : A -> N, forall n : N, forall s : A -> Prop, (@finite_set A s) -> (N.modulo (@nsum A s f) n) = (N.modulo (@nsum A s (fun i : A => N.modulo (f i) n)) n).
Axiom thm_MOD_NSUM_MOD_NUMSEG : forall f : N -> N, forall a : N, forall b : N, forall n : N, (N.modulo (@nsum N (Ninterval a b) f) n) = (N.modulo (@nsum N (Ninterval a b) (fun i : N => N.modulo (f i) n)) n).
Axiom thm_CONG_NSUM : forall {A : Type'}, forall n : N, forall f : A -> N, forall g : A -> N, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @eq2 N (f x) (g x) (num_mod n))) -> @eq2 N (@nsum A s f) (@nsum A s g) (num_mod n).
Axiom thm_CARD_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t) /\ (forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t s) /\ ((@IN (A -> Prop) u s) /\ (~ (t = u)))) -> (@setI A t u) = (@set0 A)))) -> (@card A (@UNIONS A s)) = (@nsum (A -> Prop) s (@card A)).
Axiom thm_NEUTRAL_REAL_ADD : (@neutral R Rplus) = (R_of_N N0).
Axiom thm_MONOIDAL_REAL_ADD : @monoidal R Rplus.
Axiom thm_SUM_DEGENERATE : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (~ (@finite_set A (@GSPEC A (fun GEN_PVAR_313 : A => exists x : A, @SETSPEC A GEN_PVAR_313 ((@IN A x s) /\ (~ ((f x) = (R_of_N N0)))) x)))) -> (@sum A s f) = (R_of_N N0).
Axiom thm_SUM_CLAUSES : forall {A B : Type'}, (forall f : A -> R, (@sum A (@set0 A) f) = (R_of_N N0)) /\ (forall x : B, forall f : B -> R, forall s : B -> Prop, (@finite_set B s) -> (@sum B (@INSERT B x s) f) = (@COND R (@IN B x s) (@sum B s f) (Rplus (f x) (@sum B s f)))).
Axiom thm_SUM_UNION : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (@DISJOINT A s t))) -> (@sum A (@setU A s t) f) = (Rplus (@sum A s f) (@sum A t f)).
Axiom thm_SUM_INCL_EXCL : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> R, ((@finite_set A s) /\ (@finite_set A t)) -> (Rplus (@sum A s f) (@sum A t f)) = (Rplus (@sum A (@setU A s t) f) (@sum A (@setI A s t) f)).
Axiom thm_SUM_SUPPORT : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@sum A (@support A R Rplus f s) f) = (@sum A s f).
Axiom thm_SUM_ADD_GEN : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A (@GSPEC A (fun GEN_PVAR_314 : A => exists x : A, @SETSPEC A GEN_PVAR_314 ((@IN A x s) /\ (~ ((f x) = (R_of_N N0)))) x))) /\ (@finite_set A (@GSPEC A (fun GEN_PVAR_315 : A => exists x : A, @SETSPEC A GEN_PVAR_315 ((@IN A x s) /\ (~ ((g x) = (R_of_N N0)))) x)))) -> (@sum A s (fun x : A => Rplus (f x) (g x))) = (Rplus (@sum A s f) (@sum A s g)).
Axiom thm_SUM_LMUL : forall {A : Type'}, forall f : A -> R, forall c : R, forall s : A -> Prop, (@sum A s (fun x : A => Rmult c (f x))) = (Rmult c (@sum A s f)).
Axiom thm_SUM_RMUL : forall {A : Type'}, forall f : A -> R, forall c : R, forall s : A -> Prop, (@sum A s (fun x : A => Rmult (f x) c)) = (Rmult (@sum A s f) c).
Axiom thm_SUM_LT : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> Rle (f x) (g x)) /\ (exists x : A, (@IN A x s) /\ (Rlt (f x) (g x))))) -> Rlt (@sum A s f) (@sum A s g).
Axiom thm_SUM_LT_ALL : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> Rlt (f x) (g x)))) -> Rlt (@sum A s f) (@sum A s g).
Axiom thm_SUM_POS_LT : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> Rle (R_of_N N0) (f x)) /\ (exists x : A, (@IN A x s) /\ (Rlt (R_of_N N0) (f x))))) -> Rlt (R_of_N N0) (@sum A s f).
Axiom thm_SUM_POS_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall i : A, (@IN A i s) -> Rlt (R_of_N N0) (f i)))) -> Rlt (R_of_N N0) (@sum A s f).
Axiom thm_SUM_POS_LE : forall {A : Type'} (f : A -> R), forall s : A -> Prop, (forall x : A, (@IN A x s) -> Rle (R_of_N N0) (f x)) -> Rle (R_of_N N0) (@sum A s f).
Axiom thm_SUM_POS_BOUND : forall {A : Type'}, forall f : A -> R, forall b : R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> Rle (R_of_N N0) (f x)) /\ (Rle (@sum A s f) b))) -> forall x : A, (@IN A x s) -> Rle (f x) b.
Axiom thm_SUM_POS_EQ_0 : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> Rle (R_of_N N0) (f x)) /\ ((@sum A s f) = (R_of_N N0)))) -> forall x : A, (@IN A x s) -> (f x) = (R_of_N N0).
Axiom thm_SUM_ZERO_EXISTS : forall {A : Type'}, forall u : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((@sum A s u) = (R_of_N N0))) -> (forall i : A, (@IN A i s) -> (u i) = (R_of_N N0)) \/ (exists j : A, exists k : A, (@IN A j s) /\ ((Rlt (u j) (R_of_N N0)) /\ ((@IN A k s) /\ (Rgt (u k) (R_of_N N0))))).
Axiom thm_SUM_DELETE : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (@sum A (@DELETE A s a) f) = (Rminus (@sum A s f) (f a)).
Axiom thm_SUM_DELETE_CASES : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall a : A, (@finite_set A s) -> (@sum A (@DELETE A s a) f) = (@COND R (@IN A a s) (Rminus (@sum A s f) (f a)) (@sum A s f)).
Axiom thm_SUM_SING : forall {A : Type'}, forall f : A -> R, forall x : A, (@sum A (@INSERT A x (@set0 A)) f) = (f x).
Axiom thm_SUM_DELTA : forall {A : Type'} (b : R), forall s : A -> Prop, forall a : A, (@sum A s (fun x : A => @COND R (x = a) b (R_of_N N0))) = (@COND R (@IN A a s) b (R_of_N N0)).
Axiom thm_SUM_IMAGE : forall {A B : Type'}, forall f : A -> B, forall g : B -> R, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@sum B (@IMAGE A B f s) g) = (@sum A s (@o A B R g f)).
Axiom thm_SUM_SUPERSET : forall {A : Type'}, forall f : A -> R, forall u : A -> Prop, forall v : A -> Prop, ((@subset A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (R_of_N N0))) -> (@sum A v f) = (@sum A u f).
Axiom thm_SUM_UNIV : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@subset A (@support A R Rplus f (@setT A)) s) -> (@sum A s f) = (@sum A (@setT A) f).
Axiom thm_SUM_UNION_RZERO : forall {A : Type'}, forall f : A -> R, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A u) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (R_of_N N0))) -> (@sum A (@setU A u v) f) = (@sum A u f).
Axiom thm_SUM_UNION_LZERO : forall {A : Type'}, forall f : A -> R, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A v) /\ (forall x : A, ((@IN A x u) /\ (~ (@IN A x v))) -> (f x) = (R_of_N N0))) -> (@sum A (@setU A u v) f) = (@sum A v f).
Axiom thm_SUM_RESTRICT : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@finite_set A s) -> (@sum A s (fun x : A => @COND R (@IN A x s) (f x) (R_of_N N0))) = (@sum A s f).
Axiom thm_SUM_BOUND_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> Rle (f x) (Rdiv b (R_of_N (@card A s)))))) -> Rle (@sum A s f) b.
Axiom thm_SUM_ABS_BOUND : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> Rle (Rabs (f x)) b)) -> Rle (Rabs (@sum A s f)) (Rmult (R_of_N (@card A s)) b).
Axiom thm_SUM_BOUND_LT : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> Rle (f x) b) /\ (exists x : A, (@IN A x s) /\ (Rlt (f x) b)))) -> Rlt (@sum A s f) (Rmult (R_of_N (@card A s)) b).
Axiom thm_SUM_BOUND_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> Rlt (f x) b))) -> Rlt (@sum A s f) (Rmult (R_of_N (@card A s)) b).
Axiom thm_SUM_BOUND_LT_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> Rlt (f x) (Rdiv b (R_of_N (@card A s)))))) -> Rlt (@sum A s f) b.
Axiom thm_SUM_UNION_EQ : forall {A : Type'} (f : A -> R), forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@finite_set A u) /\ (((@setI A s t) = (@set0 A)) /\ ((@setU A s t) = u))) -> (Rplus (@sum A s f) (@sum A t f)) = (@sum A u f).
Axiom thm_SUM_EQ_SUPERSET : forall {A : Type'} (g : A -> R), forall f : A -> R, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ ((@subset A t s) /\ ((forall x : A, (@IN A x t) -> (f x) = (g x)) /\ (forall x : A, ((@IN A x s) /\ (~ (@IN A x t))) -> (f x) = (R_of_N N0))))) -> (@sum A s f) = (@sum A t g).
Axiom thm_SUM_RESTRICT_SET : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall f : A -> R, (@sum A (@GSPEC A (fun GEN_PVAR_318 : A => exists x : A, @SETSPEC A GEN_PVAR_318 ((@IN A x s) /\ (P x)) x)) f) = (@sum A s (fun x : A => @COND R (P x) (f x) (R_of_N N0))).
Axiom thm_SUM_SUM_RESTRICT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall f : A -> B -> R, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@sum A s (fun x : A => @sum B (@GSPEC B (fun GEN_PVAR_319 : B => exists y : B, @SETSPEC B GEN_PVAR_319 ((@IN B y t) /\ (R' x y)) y)) (fun y : B => f x y))) = (@sum B t (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_320 : A => exists x : A, @SETSPEC A GEN_PVAR_320 ((@IN A x s) /\ (R' x y)) x)) (fun x : A => f x y))).
Axiom thm_CARD_EQ_SUM : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (R_of_N (@card A s)) = (@sum A s (fun x : A => R_of_N ((BIT1 N0)))).
Axiom thm_SUM_MULTICOUNT_GEN : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : B -> N, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@card A (@GSPEC A (fun GEN_PVAR_322 : A => exists i : A, @SETSPEC A GEN_PVAR_322 ((@IN A i s) /\ (R' i j)) i))) = (k j)))) -> (@sum A s (fun i : A => R_of_N (@card B (@GSPEC B (fun GEN_PVAR_323 : B => exists j : B, @SETSPEC B GEN_PVAR_323 ((@IN B j t) /\ (R' i j)) j))))) = (@sum B t (fun i : B => R_of_N (k i))).
Axiom thm_SUM_MULTICOUNT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : N, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@card A (@GSPEC A (fun GEN_PVAR_324 : A => exists i : A, @SETSPEC A GEN_PVAR_324 ((@IN A i s) /\ (R' i j)) i))) = k))) -> (@sum A s (fun i : A => R_of_N (@card B (@GSPEC B (fun GEN_PVAR_325 : B => exists j : B, @SETSPEC B GEN_PVAR_325 ((@IN B j t) /\ (R' i j)) j))))) = (R_of_N (N.mul k (@card B t))).
Axiom thm_SUM_IMAGE_GEN : forall {A B : Type'}, forall f : A -> B, forall g : A -> R, forall s : A -> Prop, (@finite_set A s) -> (@sum A s g) = (@sum B (@IMAGE A B f s) (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_326 : A => exists x : A, @SETSPEC A GEN_PVAR_326 ((@IN A x s) /\ ((f x) = y)) x)) g)).
Axiom thm_SUM_GROUP_RELATION : forall {A B : Type'}, forall R' : A -> B -> Prop, forall g : A -> R, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @ex1 B (fun y : B => (@IN B y t) /\ (R' x y)))) -> (@sum B t (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_328 : A => exists x : A, @SETSPEC A GEN_PVAR_328 ((@IN A x s) /\ (R' x y)) x)) g)) = (@sum A s g).
Axiom thm_REAL_OF_NUM_SUM : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, (@finite_set A s) -> (R_of_N (@nsum A s f)) = (@sum A s (fun x : A => R_of_N (f x))).
Axiom thm_SUM_SUBSET : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> R, ((@finite_set A u) /\ ((@finite_set A v) /\ ((forall x : A, (@IN A x (@setD A u v)) -> Rle (f x) (R_of_N N0)) /\ (forall x : A, (@IN A x (@setD A v u)) -> Rle (R_of_N N0) (f x))))) -> Rle (@sum A u f) (@sum A v f).
Axiom thm_SUM_SUBSET_SIMPLE : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> R, ((@finite_set A v) /\ ((@subset A u v) /\ (forall x : A, (@IN A x (@setD A v u)) -> Rle (R_of_N N0) (f x)))) -> Rle (@sum A u f) (@sum A v f).
Axiom thm_SUM_MUL_BOUND : forall {A : Type'}, forall a : A -> R, forall b : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> (Rle (R_of_N N0) (a i)) /\ (Rle (R_of_N N0) (b i)))) -> Rle (@sum A s (fun i : A => Rmult (a i) (b i))) (Rmult (@sum A s a) (@sum A s b)).
Axiom thm_SUM_IMAGE_NONZERO : forall {A B : Type'}, forall d : B -> R, forall i : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((i x) = (i y))))) -> (d (i x)) = (R_of_N N0))) -> (@sum B (@IMAGE A B i s) d) = (@sum A s (@o A B R d i)).
Axiom thm_SUM_BIJECTION : forall {A : Type'}, forall f : A -> R, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@sum A s f) = (@sum A s (@o A A R f p)).
Axiom thm_SUM_SUM_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> R, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> @finite_set B (t i))) -> (@sum A s (fun i : A => @sum B (t i) (x i))) = (@sum (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_329 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_329 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@ε ((prod A B) -> R) (fun f : (prod A B) -> R => forall i : A, forall j : B, @eq R (f (@pair A B i j)) (x i j)))).
Axiom thm_SUM_EQ_GENERAL : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> R, forall g : B -> R, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@sum A s f) = (@sum B t g).
Axiom thm_SUM_EQ_GENERAL_INVERSES : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> R, forall g : B -> R, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@sum A s f) = (@sum B t g).
Axiom thm_SUM_INJECTION : forall {A : Type'}, forall f : A -> R, forall p : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((p x) = (p y)))) -> x = y))) -> (@sum A s (@o A A R f p)) = (@sum A s f).
Axiom thm_SUM_UNION_NONZERO : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (forall x : A, (@IN A x (@setI A s t)) -> (f x) = (R_of_N N0)))) -> (@sum A (@setU A s t) f) = (Rplus (@sum A s f) (@sum A t f)).
Axiom thm_SUM_UNIONS_NONZERO : forall {A : Type'}, forall f : A -> R, forall s : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t) /\ (forall t1 : A -> Prop, forall t2 : A -> Prop, forall x : A, ((@IN (A -> Prop) t1 s) /\ ((@IN (A -> Prop) t2 s) /\ ((~ (t1 = t2)) /\ ((@IN A x t1) /\ (@IN A x t2))))) -> (f x) = (R_of_N N0)))) -> (@sum A (@UNIONS A s) f) = (@sum (A -> Prop) s (fun t : A -> Prop => @sum A t f)).
Axiom thm_SUM_CASES : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, forall f : A -> R, forall g : A -> R, (@finite_set A s) -> (@sum A s (fun x : A => @COND R (P x) (f x) (g x))) = (Rplus (@sum A (@GSPEC A (fun GEN_PVAR_330 : A => exists x : A, @SETSPEC A GEN_PVAR_330 ((@IN A x s) /\ (P x)) x)) f) (@sum A (@GSPEC A (fun GEN_PVAR_331 : A => exists x : A, @SETSPEC A GEN_PVAR_331 ((@IN A x s) /\ (~ (P x))) x)) g)).
Axiom thm_SUM_CASES_1 : forall {A : Type'} (y : R) (f : A -> R), forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (@sum A s (fun x : A => @COND R (x = a) y (f x))) = (Rplus (@sum A s f) (Rminus y (f a))).
Axiom thm_SUM_LE_INCLUDED : forall {A B : Type'}, forall f : A -> R, forall g : B -> R, forall s : A -> Prop, forall t : B -> Prop, forall i : B -> A, ((@finite_set A s) /\ ((@finite_set B t) /\ ((forall y : B, (@IN B y t) -> Rle (R_of_N N0) (g y)) /\ (forall x : A, (@IN A x s) -> exists y : B, (@IN B y t) /\ (((i y) = x) /\ (Rle (f x) (g y))))))) -> Rle (@sum A s f) (@sum B t g).
Axiom thm_SUM_IMAGE_LE : forall {A B : Type'}, forall f : A -> B, forall g : B -> R, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> Rle (R_of_N N0) (g (f x)))) -> Rle (@sum B (@IMAGE A B f s) g) (@sum A s (@o A B R g f)).
Axiom thm_SUM_CLOSED : forall {A : Type'}, forall P : R -> Prop, forall f : A -> R, forall s : A -> Prop, ((P (R_of_N N0)) /\ ((forall x : R, forall y : R, ((P x) /\ (P y)) -> P (Rplus x y)) /\ (forall a : A, (@IN A a s) -> P (f a)))) -> P (@sum A s f).
Axiom thm_SUM_RELATED : forall {A : Type'}, forall R' : R -> R -> Prop, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((R' (R_of_N N0) (R_of_N N0)) /\ ((forall m : R, forall n : R, forall m' : R, forall n' : R, ((R' m n) /\ (R' m' n')) -> R' (Rplus m m') (Rplus n n')) /\ ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@sum A s f) (@sum A s g).
Axiom thm_SUM_CLOSED_NONEMPTY : forall {A : Type'}, forall P : R -> Prop, forall f : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ ((forall x : R, forall y : R, ((P x) /\ (P y)) -> P (Rplus x y)) /\ (forall a : A, (@IN A a s) -> P (f a))))) -> P (@sum A s f).
Axiom thm_SUM_RELATED_NONEMPTY : forall {A : Type'}, forall R' : R -> R -> Prop, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((forall m : R, forall n : R, forall m' : R, forall n' : R, ((R' m n) /\ (R' m' n')) -> R' (Rplus m m') (Rplus n n')) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@sum A s f) (@sum A s g).
Axiom thm_REAL_OF_NUM_SUM_GEN : forall {A : Type'}, forall f : A -> N, forall s : A -> Prop, (@finite_set A (@GSPEC A (fun GEN_PVAR_335 : A => exists i : A, @SETSPEC A GEN_PVAR_335 ((@IN A i s) /\ (~ ((f i) = N0))) i))) -> (R_of_N (@nsum A s f)) = (@sum A s (fun x : A => R_of_N (f x))).
Axiom thm_SUM_ADD_NUMSEG : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (@sum N (Ninterval m n) (fun i : N => Rplus (f i) (g i))) = (Rplus (@sum N (Ninterval m n) f) (@sum N (Ninterval m n) g)).
Axiom thm_SUM_SUB_NUMSEG : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (@sum N (Ninterval m n) (fun i : N => Rminus (f i) (g i))) = (Rminus (@sum N (Ninterval m n) f) (@sum N (Ninterval m n) g)).
Axiom thm_SUM_LE_NUMSEG : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (forall i : N, ((N.le m i) /\ (N.le i n)) -> Rle (f i) (g i)) -> Rle (@sum N (Ninterval m n) f) (@sum N (Ninterval m n) g).
Axiom thm_SUM_EQ_NUMSEG : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (forall i : N, ((N.le m i) /\ (N.le i n)) -> (f i) = (g i)) -> (@sum N (Ninterval m n) f) = (@sum N (Ninterval m n) g).
Axiom thm_SUM_ABS_NUMSEG : forall f : N -> R, forall m : N, forall n : N, Rle (Rabs (@sum N (Ninterval m n) f)) (@sum N (Ninterval m n) (fun i : N => Rabs (f i))).
Axiom thm_SUM_CONST_NUMSEG : forall c : R, forall m : N, forall n : N, (@sum N (Ninterval m n) (fun n' : N => c)) = (Rmult (R_of_N (N.sub (N.add n ((BIT1 N0))) m)) c).
Axiom thm_SUM_EQ_0_NUMSEG : forall f : N -> R, forall m : N, forall n : N, (forall i : N, ((N.le m i) /\ (N.le i n)) -> (f i) = (R_of_N N0)) -> (@sum N (Ninterval m n) f) = (R_of_N N0).
Axiom thm_SUM_TRIV_NUMSEG : forall f : N -> R, forall m : N, forall n : N, (N.lt n m) -> (@sum N (Ninterval m n) f) = (R_of_N N0).
Axiom thm_SUM_POS_LE_NUMSEG : forall m : N, forall n : N, forall f : N -> R, (forall p : N, ((N.le m p) /\ (N.le p n)) -> Rle (R_of_N N0) (f p)) -> Rle (R_of_N N0) (@sum N (Ninterval m n) f).
Axiom thm_SUM_POS_EQ_0_NUMSEG : forall f : N -> R, forall m : N, forall n : N, ((forall p : N, ((N.le m p) /\ (N.le p n)) -> Rle (R_of_N N0) (f p)) /\ ((@sum N (Ninterval m n) f) = (R_of_N N0))) -> forall p : N, ((N.le m p) /\ (N.le p n)) -> (f p) = (R_of_N N0).
Axiom thm_SUM_SING_NUMSEG : forall f : N -> R, forall n : N, (@sum N (Ninterval n n) f) = (f n).
Axiom thm_SUM_CLAUSES_NUMSEG : forall (f : N -> R), (forall m : N, (@sum N (Ninterval m N0) f) = (@COND R (m = N0) (f N0) (R_of_N N0))) /\ (forall m : N, forall n : N, (@sum N (Ninterval m (N.succ n)) f) = (@COND R (N.le m (N.succ n)) (Rplus (@sum N (Ninterval m n) f) (f (N.succ n))) (@sum N (Ninterval m n) f))).
Axiom thm_SUM_CLAUSES_NUMSEG_LT : forall (f : N -> R), ((@sum N (@GSPEC N (fun GEN_PVAR_336 : N => exists i : N, @SETSPEC N GEN_PVAR_336 (N.lt i N0) i)) f) = (R_of_N N0)) /\ (forall k : N, (@sum N (@GSPEC N (fun GEN_PVAR_337 : N => exists i : N, @SETSPEC N GEN_PVAR_337 (N.lt i (N.succ k)) i)) f) = (Rplus (@sum N (@GSPEC N (fun GEN_PVAR_338 : N => exists i : N, @SETSPEC N GEN_PVAR_338 (N.lt i k) i)) f) (f k))).
Axiom thm_SUM_CLAUSES_NUMSEG_LE : forall (f : N -> R), ((@sum N (@GSPEC N (fun GEN_PVAR_339 : N => exists i : N, @SETSPEC N GEN_PVAR_339 (N.le i N0) i)) f) = (f N0)) /\ (forall k : N, (@sum N (@GSPEC N (fun GEN_PVAR_340 : N => exists i : N, @SETSPEC N GEN_PVAR_340 (N.le i (N.succ k)) i)) f) = (Rplus (@sum N (@GSPEC N (fun GEN_PVAR_341 : N => exists i : N, @SETSPEC N GEN_PVAR_341 (N.le i k) i)) f) (f (N.succ k)))).
Axiom thm_SUM_SWAP_NUMSEG : forall a : N, forall b : N, forall c : N, forall d : N, forall f : N -> N -> R, (@sum N (Ninterval a b) (fun i : N => @sum N (Ninterval c d) (f i))) = (@sum N (Ninterval c d) (fun j : N => @sum N (Ninterval a b) (fun i : N => f i j))).
Axiom thm_SUM_ADD_SPLIT : forall f : N -> R, forall m : N, forall n : N, forall p : N, (N.le m (N.add n ((BIT1 N0)))) -> (@sum N (Ninterval m (N.add n p)) f) = (Rplus (@sum N (Ninterval m n) f) (@sum N (Ninterval (N.add n ((BIT1 N0))) (N.add n p)) f)).
Axiom thm_SUM_OFFSET_0 : forall f : N -> R, forall m : N, forall n : N, (N.le m n) -> (@sum N (Ninterval m n) f) = (@sum N (Ninterval N0 (N.sub n m)) (fun i : N => f (N.add i m))).
Axiom thm_SUM_CLAUSES_LEFT : forall f : N -> R, forall m : N, forall n : N, (N.le m n) -> (@sum N (Ninterval m n) f) = (Rplus (f m) (@sum N (Ninterval (N.add m ((BIT1 N0))) n) f)).
Axiom thm_SUM_CLAUSES_RIGHT : forall f : N -> R, forall m : N, forall n : N, ((N.lt N0 n) /\ (N.le m n)) -> (@sum N (Ninterval m n) f) = (Rplus (@sum N (Ninterval m (N.sub n ((BIT1 N0)))) f) (f n)).
Axiom thm_SUM_PAIR : forall f : N -> R, forall m : N, forall n : N, (@sum N (Ninterval (N.mul ((BIT0 (BIT1 N0))) m) (N.add (N.mul ((BIT0 (BIT1 N0))) n) ((BIT1 N0)))) f) = (@sum N (Ninterval m n) (fun i : N => Rplus (f (N.mul ((BIT0 (BIT1 N0))) i)) (f (N.add (N.mul ((BIT0 (BIT1 N0))) i) ((BIT1 N0)))))).
Axiom thm_SUM_REFLECT : forall x : N -> R, forall m : N, forall n : N, (@sum N (Ninterval m n) x) = (@COND R (N.lt n m) (R_of_N N0) (@sum N (Ninterval N0 (N.sub n m)) (fun i : N => x (N.sub n i)))).
Axiom thm_REAL_OF_NUM_SUM_NUMSEG : forall f : N -> N, forall m : N, forall n : N, (R_of_N (@nsum N (Ninterval m n) f)) = (@sum N (Ninterval m n) (fun i : N => R_of_N (f i))).
Axiom thm_SUM_PARTIAL_SUC : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (@sum N (Ninterval m n) (fun k : N => Rmult (f k) (Rminus (g (N.add k ((BIT1 N0)))) (g k)))) = (@COND R (N.le m n) (Rminus (Rminus (Rmult (f (N.add n ((BIT1 N0)))) (g (N.add n ((BIT1 N0))))) (Rmult (f m) (g m))) (@sum N (Ninterval m n) (fun k : N => Rmult (g (N.add k ((BIT1 N0)))) (Rminus (f (N.add k ((BIT1 N0)))) (f k))))) (R_of_N N0)).
Axiom thm_SUM_PARTIAL_PRE : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (@sum N (Ninterval m n) (fun k : N => Rmult (f k) (Rminus (g k) (g (N.sub k ((BIT1 N0))))))) = (@COND R (N.le m n) (Rminus (Rminus (Rmult (f (N.add n ((BIT1 N0)))) (g n)) (Rmult (f m) (g (N.sub m ((BIT1 N0)))))) (@sum N (Ninterval m n) (fun k : N => Rmult (g k) (Rminus (f (N.add k ((BIT1 N0)))) (f k))))) (R_of_N N0)).
Axiom thm_SUM_DIFFS : forall (f : N -> R), forall m : N, forall n : N, (@sum N (Ninterval m n) (fun k : N => Rminus (f k) (f (N.add k ((BIT1 N0)))))) = (@COND R (N.le m n) (Rminus (f m) (f (N.add n ((BIT1 N0))))) (R_of_N N0)).
Axiom thm_SUM_DIFFS_ALT : forall (f : N -> R), forall m : N, forall n : N, (@sum N (Ninterval m n) (fun k : N => Rminus (f (N.add k ((BIT1 N0)))) (f k))) = (@COND R (N.le m n) (Rminus (f (N.add n ((BIT1 N0)))) (f m)) (R_of_N N0)).
Axiom thm_SUM_COMBINE_R : forall f : N -> R, forall m : N, forall n : N, forall p : N, ((N.le m (N.add n ((BIT1 N0)))) /\ (N.le n p)) -> (Rplus (@sum N (Ninterval m n) f) (@sum N (Ninterval (N.add n ((BIT1 N0))) p) f)) = (@sum N (Ninterval m p) f).
Axiom thm_SUM_COMBINE_L : forall f : N -> R, forall m : N, forall n : N, forall p : N, ((N.lt N0 n) /\ ((N.le m n) /\ (N.le n (N.add p ((BIT1 N0)))))) -> (Rplus (@sum N (Ninterval m (N.sub n ((BIT1 N0)))) f) (@sum N (Ninterval n p) f)) = (@sum N (Ninterval m p) f).
Axiom thm_REAL_SUB_POW : forall x : R, forall y : R, forall n : N, (N.le ((BIT1 N0)) n) -> (Rminus (Rpow x n) (Rpow y n)) = (Rmult (Rminus x y) (@sum N (Ninterval N0 (N.sub n ((BIT1 N0)))) (fun i : N => Rmult (Rpow x i) (Rpow y (N.sub (N.sub n ((BIT1 N0))) i))))).
Axiom thm_REAL_SUB_POW_R1 : forall x : R, forall n : N, (N.le ((BIT1 N0)) n) -> (Rminus (Rpow x n) (R_of_N ((BIT1 N0)))) = (Rmult (Rminus x (R_of_N ((BIT1 N0)))) (@sum N (Ninterval N0 (N.sub n ((BIT1 N0)))) (fun i : N => Rpow x i))).
Axiom thm_REAL_SUB_POW_L1 : forall x : R, forall n : N, (N.le ((BIT1 N0)) n) -> (Rminus (R_of_N ((BIT1 N0))) (Rpow x n)) = (Rmult (Rminus (R_of_N ((BIT1 N0))) x) (@sum N (Ninterval N0 (N.sub n ((BIT1 N0)))) (fun i : N => Rpow x i))).
Axiom thm_REAL_SUB_POLYFUN : forall a : N -> R, forall x : R, forall y : R, forall n : N, (N.le ((BIT1 N0)) n) -> (Rminus (@sum N (Ninterval N0 n) (fun i : N => Rmult (a i) (Rpow x i))) (@sum N (Ninterval N0 n) (fun i : N => Rmult (a i) (Rpow y i)))) = (Rmult (Rminus x y) (@sum N (Ninterval N0 (N.sub n ((BIT1 N0)))) (fun j : N => Rmult (@sum N (Ninterval (N.add j ((BIT1 N0))) n) (fun i : N => Rmult (a i) (Rpow y (N.sub (N.sub i j) ((BIT1 N0)))))) (Rpow x j)))).
Axiom thm_REAL_SUB_POLYFUN_ALT : forall a : N -> R, forall x : R, forall y : R, forall n : N, (N.le ((BIT1 N0)) n) -> (Rminus (@sum N (Ninterval N0 n) (fun i : N => Rmult (a i) (Rpow x i))) (@sum N (Ninterval N0 n) (fun i : N => Rmult (a i) (Rpow y i)))) = (Rmult (Rminus x y) (@sum N (Ninterval N0 (N.sub n ((BIT1 N0)))) (fun j : N => Rmult (@sum N (Ninterval N0 (N.sub (N.sub n j) ((BIT1 N0)))) (fun k : N => Rmult (a (N.add j (N.add k ((BIT1 N0))))) (Rpow y k))) (Rpow x j)))).
Axiom thm_REAL_POLYFUN_ROOTBOUND : forall n : N, forall c : N -> R, (~ (forall i : N, (@IN N i (Ninterval N0 n)) -> (c i) = (R_of_N N0))) -> (@finite_set R (@GSPEC R (fun GEN_PVAR_347 : R => exists x : R, @SETSPEC R GEN_PVAR_347 ((@sum N (Ninterval N0 n) (fun i : N => Rmult (c i) (Rpow x i))) = (R_of_N N0)) x))) /\ (N.le (@card R (@GSPEC R (fun GEN_PVAR_348 : R => exists x : R, @SETSPEC R GEN_PVAR_348 ((@sum N (Ninterval N0 n) (fun i : N => Rmult (c i) (Rpow x i))) = (R_of_N N0)) x))) n).
Axiom thm_REAL_POLYFUN_FINITE_ROOTS : forall n : N, forall c : N -> R, (@finite_set R (@GSPEC R (fun GEN_PVAR_350 : R => exists x : R, @SETSPEC R GEN_PVAR_350 ((@sum N (Ninterval N0 n) (fun i : N => Rmult (c i) (Rpow x i))) = (R_of_N N0)) x))) = (exists i : N, (@IN N i (Ninterval N0 n)) /\ (~ ((c i) = (R_of_N N0)))).
Axiom thm_REAL_POLYFUN_EQ_0 : forall n : N, forall c : N -> R, (forall x : R, (@sum N (Ninterval N0 n) (fun i : N => Rmult (c i) (Rpow x i))) = (R_of_N N0)) = (forall i : N, (@IN N i (Ninterval N0 n)) -> (c i) = (R_of_N N0)).
Axiom thm_REAL_POLYFUN_EQ_CONST : forall n : N, forall c : N -> R, forall k : R, (forall x : R, (@sum N (Ninterval N0 n) (fun i : N => Rmult (c i) (Rpow x i))) = k) = (((c N0) = k) /\ (forall i : N, (@IN N i (Ninterval ((BIT1 N0)) n)) -> (c i) = (R_of_N N0))).
Axiom thm_polynomial_function : forall p : R -> R, (polynomial_function p) = (exists m : N, exists c : N -> R, forall x : R, (p x) = (@sum N (Ninterval N0 m) (fun i : N => Rmult (c i) (Rpow x i)))).
Axiom thm_POLYNOMIAL_FUNCTION_CONST : forall c : R, polynomial_function (fun x : R => c).
Axiom thm_POLYNOMIAL_FUNCTION_ID : polynomial_function (fun x : R => x).
Axiom thm_POLYNOMIAL_FUNCTION_I : polynomial_function (@I R).
Axiom thm_POLYNOMIAL_FUNCTION_ADD : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : R => Rplus (p x) (q x)).
Axiom thm_POLYNOMIAL_FUNCTION_LMUL : forall p : R -> R, forall c : R, (polynomial_function p) -> polynomial_function (fun x : R => Rmult c (p x)).
Axiom thm_POLYNOMIAL_FUNCTION_RMUL : forall p : R -> R, forall c : R, (polynomial_function p) -> polynomial_function (fun x : R => Rmult (p x) c).
Axiom thm_POLYNOMIAL_FUNCTION_NEG : forall p : R -> R, (polynomial_function (fun x : R => Ropp (p x))) = (polynomial_function p).
Axiom thm_POLYNOMIAL_FUNCTION_SUB : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : R => Rminus (p x) (q x)).
Axiom thm_POLYNOMIAL_FUNCTION_MUL : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : R => Rmult (p x) (q x)).
Axiom thm_POLYNOMIAL_FUNCTION_SUM : forall {A : Type'}, forall s : A -> Prop, forall p : R -> A -> R, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> polynomial_function (fun x : R => p x i))) -> polynomial_function (fun x : R => @sum A s (p x)).
Axiom thm_POLYNOMIAL_FUNCTION_POW : forall p : R -> R, forall n : N, (polynomial_function p) -> polynomial_function (fun x : R => Rpow (p x) n).
Axiom thm_POLYNOMIAL_FUNCTION_INDUCT : forall P : (R -> R) -> Prop, ((P (fun x : R => x)) /\ ((forall c : R, P (fun x : R => c)) /\ ((forall p : R -> R, forall q : R -> R, ((P p) /\ (P q)) -> P (fun x : R => Rplus (p x) (q x))) /\ (forall p : R -> R, forall q : R -> R, ((P p) /\ (P q)) -> P (fun x : R => Rmult (p x) (q x)))))) -> forall p : R -> R, (polynomial_function p) -> P p.
Axiom thm_POLYNOMIAL_FUNCTION_o : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (@o R R R p q).
Axiom thm_POLYNOMIAL_FUNCTION_FINITE_ROOTS : forall p : R -> R, forall a : R, (polynomial_function p) -> (@finite_set R (@GSPEC R (fun GEN_PVAR_353 : R => exists x : R, @SETSPEC R GEN_PVAR_353 ((p x) = a) x))) = (~ (forall x : R, (p x) = a)).
Axiom thm_dimindex : forall {A : Type'}, forall s : A -> Prop, (@dimindex A s) = (@COND N (@finite_set A (@setT A)) (@card A (@setT A)) ((BIT1 N0))).
Axiom thm_DIMINDEX_NONZERO : forall {A : Type'}, forall s : A -> Prop, ~ ((@dimindex A s) = N0).
Axiom thm_DIMINDEX_GE_1 : forall {A : Type'}, forall s : A -> Prop, N.le ((BIT1 N0)) (@dimindex A s).
Axiom thm_DIMINDEX_UNIV : forall {A : Type'}, forall s : A -> Prop, (@dimindex A s) = (@dimindex A (@setT A)).
Axiom thm_DIMINDEX_UNIQUE : forall {A : Type'} (n : N), (@HAS_SIZE A (@setT A) n) -> (@dimindex A (@setT A)) = n.
Axiom thm_UNIV_HAS_SIZE_DIMINDEX : forall {N' : Type'}, (@HAS_SIZE N' (@setT N') (@dimindex N' (@setT N'))) = (@finite_set N' (@setT N')).
Axiom thm_HAS_SIZE_1 : @HAS_SIZE unit (@setT unit) ((BIT1 N0)).
Axiom thm_NUMSEG_LT_DIMINDEX : forall {N' : Type'}, (@GSPEC N (fun GEN_PVAR_354 : N => exists i : N, @SETSPEC N GEN_PVAR_354 (N.lt i (@dimindex N' (@setT N'))) i)) = (Ninterval N0 (N.sub (@dimindex N' (@setT N')) ((BIT1 N0)))).
Axiom thm_FINITE_IMAGE_IMAGE : forall {A : Type'}, (@setT (finite_image A)) = (@IMAGE N (finite_image A) (@finite_index A) (Ninterval ((BIT1 N0)) (@dimindex A (@setT A)))).
Axiom thm_HAS_SIZE_FINITE_IMAGE : forall {A : Type'}, forall s : A -> Prop, @HAS_SIZE (finite_image A) (@setT (finite_image A)) (@dimindex A s).
Axiom thm_CARD_FINITE_IMAGE : forall {A : Type'}, forall s : A -> Prop, (@card (finite_image A) (@setT (finite_image A))) = (@dimindex A s).
Axiom thm_FINITE_FINITE_IMAGE : forall {A : Type'}, @finite_set (finite_image A) (@setT (finite_image A)).
Axiom thm_DIMINDEX_FINITE_IMAGE : forall {A : Type'}, forall s : (finite_image A) -> Prop, forall t : A -> Prop, (@dimindex (finite_image A) s) = (@dimindex A t).
Axiom thm_FINITE_INDEX_WORKS : forall {A : Type'}, forall i : finite_image A, @ex1 N (fun n : N => (N.le ((BIT1 N0)) n) /\ ((N.le n (@dimindex A (@setT A))) /\ ((@finite_index A n) = i))).
Axiom thm_FINITE_INDEX_INJ : forall {A : Type'}, forall i : N, forall j : N, ((N.le ((BIT1 N0)) i) /\ ((N.le i (@dimindex A (@setT A))) /\ ((N.le ((BIT1 N0)) j) /\ (N.le j (@dimindex A (@setT A)))))) -> ((@finite_index A i) = (@finite_index A j)) = (i = j).
Axiom thm_FORALL_FINITE_INDEX : forall {N' : Type'} (P : (finite_image N') -> Prop), (forall k : finite_image N', P k) = (forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex N' (@setT N')))) -> P (@finite_index N' i)).
Axiom thm_finite_index : forall {A N' : Type'}, forall x : cart A N', forall i : N, (@dollar A N' x i) = (@dest_cart A N' x (@finite_index N' i)).
Axiom thm_CART_EQ : forall {A B : Type'}, forall x : cart A B, forall y : cart A B, (x = y) = (forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B x i) = (@dollar A B y i)).
Axiom thm_lambda : forall {A B : Type'}, forall g : N -> A, (@lambda A B g) = (@ε (cart A B) (fun f : cart A B => forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (g i))).
Axiom thm_LAMBDA_BETA : forall {A B : Type'} (g : N -> A), forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B (@lambda A B g) i) = (g i).
Axiom thm_LAMBDA_UNIQUE : forall {A B : Type'}, forall f : cart A B, forall g : N -> A, (forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (g i)) = ((@lambda A B g) = f).
Axiom thm_LAMBDA_ETA : forall {A B : Type'}, forall g : cart A B, (@lambda A B (fun i : N => @dollar A B g i)) = g.
Axiom thm_FINITE_INDEX_INRANGE : forall {A N' : Type'}, forall i : N, exists k : N, (N.le ((BIT1 N0)) k) /\ ((N.le k (@dimindex N' (@setT N'))) /\ (forall x : cart A N', (@dollar A N' x i) = (@dollar A N' x k))).
Axiom thm_FINITE_INDEX_INRANGE_2 : forall {A B N' : Type'}, forall i : N, exists k : N, (N.le ((BIT1 N0)) k) /\ ((N.le k (@dimindex N' (@setT N'))) /\ ((forall x : cart A N', (@dollar A N' x i) = (@dollar A N' x k)) /\ (forall y : cart B N', (@dollar B N' y i) = (@dollar B N' y k)))).
Axiom thm_CART_EQ_FULL : forall {A N' : Type'}, forall x : cart A N', forall y : cart A N', (x = y) = (forall i : N, (@dollar A N' x i) = (@dollar A N' y i)).
Axiom thm_pastecart : forall {A M N' : Type'}, forall f : cart A M, forall g : cart A N', (@pastecart A M N' f g) = (@lambda A (finite_sum M N') (fun i : N => @COND A (N.le i (@dimindex M (@setT M))) (@dollar A M f i) (@dollar A N' g (N.sub i (@dimindex M (@setT M)))))).
Axiom thm_fstcart : forall {A M N' : Type'}, forall f : cart A (finite_sum M N'), (@fstcart A M N' f) = (@lambda A M (fun i : N => @dollar A (finite_sum M N') f i)).
Axiom thm_sndcart : forall {A M N' : Type'}, forall f : cart A (finite_sum M N'), (@sndcart A M N' f) = (@lambda A N' (fun i : N => @dollar A (finite_sum M N') f (N.add i (@dimindex M (@setT M))))).
Axiom thm_FINITE_SUM_IMAGE : forall {A B : Type'}, (@setT (finite_sum A B)) = (@IMAGE N (finite_sum A B) (@mk_finite_sum A B) (Ninterval ((BIT1 N0)) (N.add (@dimindex A (@setT A)) (@dimindex B (@setT B))))).
Axiom thm_DIMINDEX_HAS_SIZE_FINITE_SUM : forall {M N' : Type'}, @HAS_SIZE (finite_sum M N') (@setT (finite_sum M N')) (N.add (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_DIMINDEX_FINITE_SUM : forall {M N' : Type'}, (@dimindex (finite_sum M N') (@setT (finite_sum M N'))) = (N.add (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_FSTCART_PASTECART : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', (@fstcart A M N' (@pastecart A M N' x y)) = x.
Axiom thm_SNDCART_PASTECART : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', (@sndcart A M N' (@pastecart A M N' x y)) = y.
Axiom thm_PASTECART_FST_SND : forall {A M N' : Type'}, forall z : cart A (finite_sum M N'), (@pastecart A M N' (@fstcart A M N' z) (@sndcart A M N' z)) = z.
Axiom thm_PASTECART_EQ : forall {A M N' : Type'}, forall x : cart A (finite_sum M N'), forall y : cart A (finite_sum M N'), (x = y) = (((@fstcart A M N' x) = (@fstcart A M N' y)) /\ ((@sndcart A M N' x) = (@sndcart A M N' y))).
Axiom thm_FORALL_PASTECART : forall {A M N' : Type'} (P : (cart A (finite_sum M N')) -> Prop), (forall p : cart A (finite_sum M N'), P p) = (forall x : cart A M, forall y : cart A N', P (@pastecart A M N' x y)).
Axiom thm_EXISTS_PASTECART : forall {A M N' : Type'} (P : (cart A (finite_sum M N')) -> Prop), (exists p : cart A (finite_sum M N'), P p) = (exists x : cart A M, exists y : cart A N', P (@pastecart A M N' x y)).
Axiom thm_PASTECART_INJ : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', forall w : cart A M, forall z : cart A N', ((@pastecart A M N' x y) = (@pastecart A M N' w z)) = ((x = w) /\ (y = z)).
Axiom thm_FSTCART_COMPONENT : forall {A M N' : Type'}, forall x : cart A (finite_sum M N'), forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex M (@setT M)))) -> (@dollar A M (@fstcart A M N' x) i) = (@dollar A (finite_sum M N') x i).
Axiom thm_SNDCART_COMPONENT : forall {A M N' : Type'}, forall x : cart A (finite_sum M N'), forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex N' (@setT N')))) -> (@dollar A N' (@sndcart A M N' x) i) = (@dollar A (finite_sum M N') x (N.add i (@dimindex M (@setT M)))).
Axiom thm_PASTECART_COMPONENT : forall {A M N' : Type'}, (forall u : cart A M, forall v : cart A N', forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex M (@setT M)))) -> (@dollar A (finite_sum M N') (@pastecart A M N' u v) i) = (@dollar A M u i)) /\ (forall u : cart A M, forall v : cart A N', forall i : N, ((N.le (N.add (@dimindex M (@setT M)) ((BIT1 N0))) i) /\ (N.le i (N.add (@dimindex M (@setT M)) (@dimindex N' (@setT N'))))) -> (@dollar A (finite_sum M N') (@pastecart A M N' u v) i) = (@dollar A N' v (N.sub i (@dimindex M (@setT M))))).
Axiom thm_FINITE_DIFF_IMAGE : forall {A B : Type'}, (@setT (finite_diff A B)) = (@IMAGE N (finite_diff A B) (@mk_finite_diff A B) (Ninterval ((BIT1 N0)) (@COND N (N.lt (@dimindex B (@setT B)) (@dimindex A (@setT A))) (N.sub (@dimindex A (@setT A)) (@dimindex B (@setT B))) ((BIT1 N0))))).
Axiom thm_DIMINDEX_HAS_SIZE_FINITE_DIFF : forall {M N' : Type'}, @HAS_SIZE (finite_diff M N') (@setT (finite_diff M N')) (@COND N (N.lt (@dimindex N' (@setT N')) (@dimindex M (@setT M))) (N.sub (@dimindex M (@setT M)) (@dimindex N' (@setT N'))) ((BIT1 N0))).
Axiom thm_DIMINDEX_FINITE_DIFF : forall {M N' : Type'}, (@dimindex (finite_diff M N') (@setT (finite_diff M N'))) = (@COND N (N.lt (@dimindex N' (@setT N')) (@dimindex M (@setT M))) (N.sub (@dimindex M (@setT M)) (@dimindex N' (@setT N'))) ((BIT1 N0))).
Axiom thm_FINITE_PROD_IMAGE : forall {A B : Type'}, (@setT (finite_prod A B)) = (@IMAGE N (finite_prod A B) (@mk_finite_prod A B) (Ninterval ((BIT1 N0)) (N.mul (@dimindex A (@setT A)) (@dimindex B (@setT B))))).
Axiom thm_DIMINDEX_HAS_SIZE_FINITE_PROD : forall {M N' : Type'}, @HAS_SIZE (finite_prod M N') (@setT (finite_prod M N')) (N.mul (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_DIMINDEX_FINITE_PROD : forall {M N' : Type'}, (@dimindex (finite_prod M N') (@setT (finite_prod M N'))) = (N.mul (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_tybit0_INDUCT : forall {A : Type'}, forall P : (tybit0 A) -> Prop, (forall a : finite_sum A A, P (@mktybit0 A a)) -> forall x : tybit0 A, P x.
Axiom thm_tybit0_RECURSION : forall {A Z' : Type'}, forall f : (finite_sum A A) -> Z', exists fn : (tybit0 A) -> Z', forall a : finite_sum A A, (fn (@mktybit0 A a)) = (f a).
Axiom thm_tybit1_INDUCT : forall {A : Type'}, forall P : (tybit1 A) -> Prop, (forall a : finite_sum (finite_sum A A) unit, P (@mktybit1 A a)) -> forall x : tybit1 A, P x.
Axiom thm_tybit1_RECURSION : forall {A Z' : Type'}, forall f : (finite_sum (finite_sum A A) unit) -> Z', exists fn : (tybit1 A) -> Z', forall a : finite_sum (finite_sum A A) unit, (fn (@mktybit1 A a)) = (f a).
Axiom thm_HAS_SIZE_TYBIT0 : forall {A : Type'}, @HAS_SIZE (tybit0 A) (@setT (tybit0 A)) (N.mul ((BIT0 (BIT1 N0))) (@dimindex A (@setT A))).
Axiom thm_HAS_SIZE_TYBIT1 : forall {A : Type'}, @HAS_SIZE (tybit1 A) (@setT (tybit1 A)) (N.add (N.mul ((BIT0 (BIT1 N0))) (@dimindex A (@setT A))) ((BIT1 N0))).
Axiom thm_DIMINDEX_TYBIT0 : forall {A : Type'}, (@dimindex (tybit0 A) (@setT (tybit0 A))) = (N.mul ((BIT0 (BIT1 N0))) (@dimindex A (@setT A))).
Axiom thm_DIMINDEX_TYBIT1 : forall {A : Type'}, (@dimindex (tybit1 A) (@setT (tybit1 A))) = (N.add (N.mul ((BIT0 (BIT1 N0))) (@dimindex A (@setT A))) ((BIT1 N0))).
Axiom thm_DIMINDEX_CLAUSES : forall {A : Type'}, ((@dimindex unit (@setT unit)) = ((BIT1 N0))) /\ (((@dimindex (tybit0 A) (@setT (tybit0 A))) = (N.mul ((BIT0 (BIT1 N0))) (@dimindex A (@setT A)))) /\ ((@dimindex (tybit1 A) (@setT (tybit1 A))) = (N.add (N.mul ((BIT0 (BIT1 N0))) (@dimindex A (@setT A))) ((BIT1 N0))))).
Axiom thm_FINITE_1 : @finite_set unit (@setT unit).
Axiom thm_FINITE_TYBIT0 : forall {A : Type'}, @finite_set (tybit0 A) (@setT (tybit0 A)).
Axiom thm_FINITE_TYBIT1 : forall {A : Type'}, @finite_set (tybit1 A) (@setT (tybit1 A)).
Axiom thm_FINITE_CLAUSES : forall {A : Type'}, (@finite_set unit (@setT unit)) /\ ((@finite_set (tybit0 A) (@setT (tybit0 A))) /\ (@finite_set (tybit1 A) (@setT (tybit1 A)))).
Axiom thm_DIMINDEX_2 : (@dimindex (tybit0 unit) (@setT (tybit0 unit))) = ((BIT0 (BIT1 N0))).
Axiom thm_DIMINDEX_3 : (@dimindex (tybit1 unit) (@setT (tybit1 unit))) = ((BIT1 (BIT1 N0))).
Axiom thm_DIMINDEX_4 : (@dimindex (tybit0 (tybit0 unit)) (@setT (tybit0 (tybit0 unit)))) = ((BIT0 (BIT0 (BIT1 N0)))).
Axiom thm_FINITE_CART : forall {A N' : Type'}, forall P : N -> A -> Prop, (forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex N' (@setT N')))) -> @finite_set A (@GSPEC A (fun GEN_PVAR_360 : A => exists x : A, @SETSPEC A GEN_PVAR_360 (P i x) x))) -> @finite_set (cart A N') (@GSPEC (cart A N') (fun GEN_PVAR_361 : cart A N' => exists v : cart A N', @SETSPEC (cart A N') GEN_PVAR_361 (forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex N' (@setT N')))) -> P i (@dollar A N' v i)) v)).
Axiom thm_HAS_SIZE_CART_UNIV : forall {A N' : Type'}, forall m : N, (@HAS_SIZE A (@setT A) m) -> @HAS_SIZE (cart A N') (@setT (cart A N')) (N.pow m (@dimindex N' (@setT N'))).
Axiom thm_CARD_CART_UNIV : forall {A N' : Type'}, (@finite_set A (@setT A)) -> (@card (cart A N') (@setT (cart A N'))) = (N.pow (@card A (@setT A)) (@dimindex N' (@setT N'))).
Axiom thm_FINITE_CART_UNIV : forall {A N' : Type'}, (@finite_set A (@setT A)) -> @finite_set (cart A N') (@setT (cart A N')).
Axiom thm_vector : forall {A N' : Type'}, forall l : list A, (@vector A N' l) = (@lambda A N' (fun i : N => @Nth A (N.sub i ((BIT1 N0))) l)).
Axiom thm_IN_ELIM_PASTECART_THM : forall {A M N' : Type'}, forall P : (cart A M) -> (cart A N') -> Prop, forall a : cart A M, forall b : cart A N', (@IN (cart A (finite_sum M N')) (@pastecart A M N' a b) (@GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_362 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_362 (P x y) (@pastecart A M N' x y)))) = (P a b).
Axiom thm_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, (@PCROSS A M N' s t) = (@GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x s) /\ (@IN (cart A N') y t)) (@pastecart A M N' x y))).
Axiom thm_FORALL_IN_PCROSS : forall {A M N' : Type'} (s : (cart A M) -> Prop) (t : (cart A N') -> Prop) (P : (cart A (finite_sum M N')) -> Prop), (forall z : cart A (finite_sum M N'), (@IN (cart A (finite_sum M N')) z (@PCROSS A M N' s t)) -> P z) = (forall x : cart A M, forall y : cart A N', ((@IN (cart A M) x s) /\ (@IN (cart A N') y t)) -> P (@pastecart A M N' x y)).
Axiom thm_EXISTS_IN_PCROSS : forall {A M N' : Type'} (s : (cart A M) -> Prop) (t : (cart A N') -> Prop) (P : (cart A (finite_sum M N')) -> Prop), (exists z : cart A (finite_sum M N'), (@IN (cart A (finite_sum M N')) z (@PCROSS A M N' s t)) /\ (P z)) = (exists x : cart A M, exists y : cart A N', (@IN (cart A M) x s) /\ ((@IN (cart A N') y t) /\ (P (@pastecart A M N' x y)))).
Axiom thm_PASTECART_IN_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall x : cart A M, forall y : cart A N', (@IN (cart A (finite_sum M N')) (@pastecart A M N' x y) (@PCROSS A M N' s t)) = ((@IN (cart A M) x s) /\ (@IN (cart A N') y t)).
Axiom thm_PCROSS_EQ_EMPTY : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, ((@PCROSS A M N' s t) = (@set0 (cart A (finite_sum M N')))) = ((s = (@set0 (cart A M))) \/ (t = (@set0 (cart A N')))).
Axiom thm_PCROSS_EMPTY : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, (@PCROSS A M N' s (@set0 (cart A N'))) = (@set0 (cart A (finite_sum M N')))) /\ (forall t : (cart A N') -> Prop, (@PCROSS A M N' (@set0 (cart A M)) t) = (@set0 (cart A (finite_sum M N')))).
Axiom thm_PCROSS_SING : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', (@PCROSS A M N' (@INSERT (cart A M) x (@set0 (cart A M))) (@INSERT (cart A N') y (@set0 (cart A N')))) = (@INSERT (cart A (finite_sum M N')) (@pastecart A M N' x y) (@set0 (cart A (finite_sum M N')))).
Axiom thm_SUBSET_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall s' : (cart A M) -> Prop, forall t' : (cart A N') -> Prop, (@subset (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t')) = ((s = (@set0 (cart A M))) \/ ((t = (@set0 (cart A N'))) \/ ((@subset (cart A M) s s') /\ (@subset (cart A N') t t')))).
Axiom thm_PCROSS_MONO : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall s' : (cart A M) -> Prop, forall t' : (cart A N') -> Prop, ((@subset (cart A M) s s') /\ (@subset (cart A N') t t')) -> @subset (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t').
Axiom thm_PCROSS_EQ : forall {M N' : Type'}, forall s : (cart R M) -> Prop, forall s' : (cart R M) -> Prop, forall t : (cart R N') -> Prop, forall t' : (cart R N') -> Prop, ((@PCROSS R M N' s t) = (@PCROSS R M N' s' t')) = ((((s = (@set0 (cart R M))) \/ (t = (@set0 (cart R N')))) /\ ((s' = (@set0 (cart R M))) \/ (t' = (@set0 (cart R N'))))) \/ ((s = s') /\ (t = t'))).
Axiom thm_UNIV_PCROSS_UNIV : forall {A M N' : Type'}, (@PCROSS A M N' (@setT (cart A M)) (@setT (cart A N'))) = (@setT (cart A (finite_sum M N'))).
Axiom thm_HAS_SIZE_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall m : N, forall n : N, ((@HAS_SIZE (cart A M) s m) /\ (@HAS_SIZE (cart A N') t n)) -> @HAS_SIZE (cart A (finite_sum M N')) (@PCROSS A M N' s t) (N.mul m n).
Axiom thm_FINITE_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, ((@finite_set (cart A M) s) /\ (@finite_set (cart A N') t)) -> @finite_set (cart A (finite_sum M N')) (@PCROSS A M N' s t).
Axiom thm_FINITE_PCROSS_EQ : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, (@finite_set (cart A (finite_sum M N')) (@PCROSS A M N' s t)) = ((s = (@set0 (cart A M))) \/ ((t = (@set0 (cart A N'))) \/ ((@finite_set (cart A M) s) /\ (@finite_set (cart A N') t)))).
Axiom thm_IMAGE_FSTCART_PCROSS : forall {M N' : Type'}, forall s : (cart R M) -> Prop, forall t : (cart R N') -> Prop, (@IMAGE (cart R (finite_sum M N')) (cart R M) (@fstcart R M N') (@PCROSS R M N' s t)) = (@COND ((cart R M) -> Prop) (t = (@set0 (cart R N'))) (@set0 (cart R M)) s).
Axiom thm_IMAGE_SNDCART_PCROSS : forall {M N' : Type'}, forall s : (cart R M) -> Prop, forall t : (cart R N') -> Prop, (@IMAGE (cart R (finite_sum M N')) (cart R N') (@sndcart R M N') (@PCROSS R M N' s t)) = (@COND ((cart R N') -> Prop) (s = (@set0 (cart R M))) (@set0 (cart R N')) t).
Axiom thm_PCROSS_INTER : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' s (@setI (cart A N') t u)) = (@setI (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s u))) /\ (forall s : (cart A M) -> Prop, forall t : (cart A M) -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' (@setI (cart A M) s t) u) = (@setI (cart A (finite_sum M N')) (@PCROSS A M N' s u) (@PCROSS A M N' t u))).
Axiom thm_PCROSS_UNION : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' s (@setU (cart A N') t u)) = (@setU (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s u))) /\ (forall s : (cart A M) -> Prop, forall t : (cart A M) -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' (@setU (cart A M) s t) u) = (@setU (cart A (finite_sum M N')) (@PCROSS A M N' s u) (@PCROSS A M N' t u))).
Axiom thm_PCROSS_DIFF : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' s (@setD (cart A N') t u)) = (@setD (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s u))) /\ (forall s : (cart A M) -> Prop, forall t : (cart A M) -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' (@setD (cart A M) s t) u) = (@setD (cart A (finite_sum M N')) (@PCROSS A M N' s u) (@PCROSS A M N' t u))).
Axiom thm_INTER_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall s' : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall t' : (cart A N') -> Prop, (@setI (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t')) = (@PCROSS A M N' (@setI (cart A M) s s') (@setI (cart A N') t t')).
Axiom thm_PCROSS_UNIONS : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall f : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' s (@UNIONS (cart A N') f)) = (@UNIONS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_365 : (cart A (finite_sum M N')) -> Prop => exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_365 (@IN ((cart A N') -> Prop) t f) (@PCROSS A M N' s t))))) /\ (forall f : ((cart A M) -> Prop) -> Prop, forall t : (cart A N') -> Prop, (@PCROSS A M N' (@UNIONS (cart A M) f) t) = (@UNIONS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_366 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_366 (@IN ((cart A M) -> Prop) s f) (@PCROSS A M N' s t))))).
Axiom thm_PCROSS_UNIONS_UNIONS : forall {A M N' : Type'}, forall f : ((cart A M) -> Prop) -> Prop, forall g : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' (@UNIONS (cart A M) f) (@UNIONS (cart A N') g)) = (@UNIONS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_364 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_364 ((@IN ((cart A M) -> Prop) s f) /\ (@IN ((cart A N') -> Prop) t g)) (@PCROSS A M N' s t)))).
Axiom thm_PCROSS_INTERS : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall f : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' s (@INTERS (cart A N') f)) = (@COND ((cart A (finite_sum M N')) -> Prop) (f = (@set0 ((cart A N') -> Prop))) (@PCROSS A M N' s (@setT (cart A N'))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_370 : (cart A (finite_sum M N')) -> Prop => exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_370 (@IN ((cart A N') -> Prop) t f) (@PCROSS A M N' s t)))))) /\ (forall f : ((cart A M) -> Prop) -> Prop, forall t : (cart A N') -> Prop, (@PCROSS A M N' (@INTERS (cart A M) f) t) = (@COND ((cart A (finite_sum M N')) -> Prop) (f = (@set0 ((cart A M) -> Prop))) (@PCROSS A M N' (@setT (cart A M)) t) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_371 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_371 (@IN ((cart A M) -> Prop) s f) (@PCROSS A M N' s t)))))).
Axiom thm_PCROSS_INTERS_INTERS : forall {A M N' : Type'}, forall f : ((cart A M) -> Prop) -> Prop, forall g : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' (@INTERS (cart A M) f) (@INTERS (cart A N') g)) = (@COND ((cart A (finite_sum M N')) -> Prop) (f = (@set0 ((cart A M) -> Prop))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_367 : (cart A (finite_sum M N')) -> Prop => exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_367 (@IN ((cart A N') -> Prop) t g) (@PCROSS A M N' (@setT (cart A M)) t)))) (@COND ((cart A (finite_sum M N')) -> Prop) (g = (@set0 ((cart A N') -> Prop))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_368 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_368 (@IN ((cart A M) -> Prop) s f) (@PCROSS A M N' s (@setT (cart A N')))))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_369 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_369 ((@IN ((cart A M) -> Prop) s f) /\ (@IN ((cart A N') -> Prop) t g)) (@PCROSS A M N' s t)))))).
Axiom thm_DISJOINT_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall s' : (cart A M) -> Prop, forall t' : (cart A N') -> Prop, (@DISJOINT (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t')) = ((@DISJOINT (cart A M) s s') \/ (@DISJOINT (cart A N') t t')).
Axiom thm_CASEWISE_DEF : forall {_137244 _137280 _137284 _137285 : Type'} (h : prod (_137280 -> _137284) (_137285 -> _137280 -> _137244)) (t : list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) (f : _137285) (x : _137284), ((@CASEWISE _137244 _137280 _137284 _137285 (@nil (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) f x) = (@ε _137244 (fun y : _137244 => True))) /\ ((@CASEWISE _137244 _137280 _137284 _137285 (@cons (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244)) h t) f x) = (@COND _137244 (exists y : _137280, (@fst (_137280 -> _137284) (_137285 -> _137280 -> _137244) h y) = x) (@snd (_137280 -> _137284) (_137285 -> _137280 -> _137244) h f (@ε _137280 (fun y : _137280 => (@fst (_137280 -> _137284) (_137285 -> _137280 -> _137244) h y) = x))) (@CASEWISE _137244 _137280 _137284 _137285 t f x))).
Axiom thm_CASEWISE : forall {_137296 _137304 _137305 _137344 _137345 _137347 : Type'} (t : _137345 -> _137347 -> _137305) (s : _137347 -> _137344) (clauses : list (prod (_137347 -> _137344) (_137345 -> _137347 -> _137305))) (f : _137345) (x : _137344), ((@CASEWISE _137304 _137296 _137344 _137345 (@nil (prod (_137296 -> _137344) (_137345 -> _137296 -> _137304))) f x) = (@ε _137304 (fun y : _137304 => True))) /\ ((@CASEWISE _137305 _137347 _137344 _137345 (@cons (prod (_137347 -> _137344) (_137345 -> _137347 -> _137305)) (@pair (_137347 -> _137344) (_137345 -> _137347 -> _137305) s t) clauses) f x) = (@COND _137305 (exists y : _137347, (s y) = x) (t f (@ε _137347 (fun y : _137347 => (s y) = x))) (@CASEWISE _137305 _137347 _137344 _137345 clauses f x))).
Axiom thm_CASEWISE_CASES : forall {_137436 _137437 _137439 _137446 : Type'}, forall clauses : list (prod (_137439 -> _137436) (_137437 -> _137439 -> _137446)), forall c : _137437, forall x : _137436, (exists s : _137439 -> _137436, exists t : _137437 -> _137439 -> _137446, exists a : _137439, (@List.In (prod (_137439 -> _137436) (_137437 -> _137439 -> _137446)) (@pair (_137439 -> _137436) (_137437 -> _137439 -> _137446) s t) clauses) /\ (((s a) = x) /\ ((@CASEWISE _137446 _137439 _137436 _137437 clauses c x) = (t c a)))) \/ ((~ (exists s : _137439 -> _137436, exists t : _137437 -> _137439 -> _137446, exists a : _137439, (@List.In (prod (_137439 -> _137436) (_137437 -> _137439 -> _137446)) (@pair (_137439 -> _137436) (_137437 -> _137439 -> _137446) s t) clauses) /\ ((s a) = x))) /\ ((@CASEWISE _137446 _137439 _137436 _137437 clauses c x) = (@ε _137446 (fun y : _137446 => True)))).
Axiom thm_CASEWISE_WORKS : forall {A B C P : Type'}, forall clauses : list (prod (P -> A) (C -> P -> B)), forall c : C, (forall s : P -> A, forall t : C -> P -> B, forall s' : P -> A, forall t' : C -> P -> B, forall x : P, forall y : P, ((@List.In (prod (P -> A) (C -> P -> B)) (@pair (P -> A) (C -> P -> B) s t) clauses) /\ ((@List.In (prod (P -> A) (C -> P -> B)) (@pair (P -> A) (C -> P -> B) s' t') clauses) /\ ((s x) = (s' y)))) -> (t c x) = (t' c y)) -> @List.Forall (prod (P -> A) (C -> P -> B)) (@ε ((prod (P -> A) (C -> P -> B)) -> Prop) (fun f : (prod (P -> A) (C -> P -> B)) -> Prop => forall s : P -> A, forall t : C -> P -> B, @eq Prop (f (@pair (P -> A) (C -> P -> B) s t)) (forall x : P, (@CASEWISE B P A C clauses c (s x)) = (t c x)))) clauses.
Axiom thm_admissible : forall {_137575 _137578 _137582 _137583 _137588 : Type'}, forall p : (_137582 -> _137578) -> _137588 -> Prop, forall lt2 : _137582 -> _137575 -> Prop, forall s : _137588 -> _137575, forall t : (_137582 -> _137578) -> _137588 -> _137583, (@admissible _137575 _137578 _137582 _137583 _137588 lt2 p s t) = (forall f : _137582 -> _137578, forall g : _137582 -> _137578, forall a : _137588, ((p f a) /\ ((p g a) /\ (forall z : _137582, (lt2 z (s a)) -> (f z) = (g z)))) -> (t f a) = (t g a)).
Axiom thm_tailadmissible : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall s : P -> A, forall p : (A -> B) -> P -> Prop, forall t : (A -> B) -> P -> B, (@tailadmissible A B P lt2 p s t) = (exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (lt2 y (G f a))) -> lt2 y (s a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (lt2 z (s a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (p f a) -> (t f a) = (@COND B (P' f a) (f (G f a)) (H f a))))).
Axiom thm_superadmissible : forall {_137732 _137734 _137740 : Type'}, forall lt2 : _137732 -> _137732 -> Prop, forall p : (_137732 -> _137734) -> _137740 -> Prop, forall s : _137740 -> _137732, forall t : (_137732 -> _137734) -> _137740 -> _137734, (@superadmissible _137732 _137734 _137740 lt2 p s t) = ((@admissible _137732 _137734 _137732 Prop _137740 lt2 (fun f : _137732 -> _137734 => fun a : _137740 => True) s p) -> @tailadmissible _137732 _137734 _137740 lt2 p s t).
Axiom thm_MATCH_SEQPATTERN : forall {_137768 _137775 : Type'} (r : _137775 -> _137768 -> Prop) (x : _137775) (s : _137775 -> _137768 -> Prop), (@_MATCH _137775 _137768 x (@_SEQPATTERN _137775 _137768 r s)) = (@COND _137768 (exists y : _137768, r x y) (@_MATCH _137775 _137768 x r) (@_MATCH _137775 _137768 x s)).
Axiom thm_ADMISSIBLE_CONST : forall {_137795 _137796 _137797 _137798 _137799 : Type'} (lt2 : _137796 -> _137795 -> Prop), forall p : (_137796 -> _137797) -> _137798 -> Prop, forall s : _137798 -> _137795, forall c : _137798 -> _137799, @admissible _137795 _137797 _137796 _137799 _137798 lt2 p s (fun f : _137796 -> _137797 => c).
Axiom thm_ADMISSIBLE_BASE : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : P -> A, (forall f : A -> B, forall a : P, (p f a) -> lt2 (t a) (s a)) -> @admissible A B A B P lt2 p s (fun f : A -> B => fun x : P => f (t x)).
Axiom thm_ADMISSIBLE_COMB : forall {A B C D P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall g : (A -> B) -> P -> C -> D, forall y : (A -> B) -> P -> C, ((@admissible A B A (C -> D) P lt2 p s g) /\ (@admissible A B A C P lt2 p s y)) -> @admissible A B A D P lt2 p s (fun f : A -> B => fun x : P => g f x (y f x)).
Axiom thm_ADMISSIBLE_RAND : forall {A B C D P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall g : P -> C -> D, forall y : (A -> B) -> P -> C, (@admissible A B A C P lt2 p s y) -> @admissible A B A D P lt2 p s (fun f : A -> B => fun x : P => g x (y f x)).
Axiom thm_ADMISSIBLE_LAMBDA : forall {A B C P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> C -> P -> Prop, (@admissible A B A Prop (prod C P) lt2 (fun f : A -> B => @ε ((prod C P) -> Prop) (fun f' : (prod C P) -> Prop => forall u : C, forall x : P, @eq Prop (f' (@pair C P u x)) (p f x))) (@ε ((prod C P) -> A) (fun f : (prod C P) -> A => forall u : C, forall x : P, @eq A (f (@pair C P u x)) (s x))) (fun f : A -> B => @ε ((prod C P) -> Prop) (fun f' : (prod C P) -> Prop => forall u : C, forall x : P, @eq Prop (f' (@pair C P u x)) (t f u x)))) -> @admissible A B A (C -> Prop) P lt2 p s (fun f : A -> B => fun x : P => fun u : C => t f u x).
Axiom thm_ADMISSIBLE_NEST : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> A, ((@admissible A B A A P lt2 p s t) /\ (forall f : A -> B, forall a : P, (p f a) -> lt2 (t f a) (s a))) -> @admissible A B A B P lt2 p s (fun f : A -> B => fun x : P => f (t f x)).
Axiom thm_ADMISSIBLE_COND : forall {_138132 _138133 _138164 _138189 P : Type'}, forall lt2 : _138133 -> _138132 -> Prop, forall p : (_138133 -> _138164) -> P -> Prop, forall P' : (_138133 -> _138164) -> P -> Prop, forall s : P -> _138132, forall h : (_138133 -> _138164) -> P -> _138189, forall k : (_138133 -> _138164) -> P -> _138189, ((@admissible _138132 _138164 _138133 Prop P lt2 p s P') /\ ((@admissible _138132 _138164 _138133 _138189 P lt2 (fun f : _138133 -> _138164 => fun x : P => (p f x) /\ (P' f x)) s h) /\ (@admissible _138132 _138164 _138133 _138189 P lt2 (fun f : _138133 -> _138164 => fun x : P => (p f x) /\ (~ (P' f x))) s k))) -> @admissible _138132 _138164 _138133 _138189 P lt2 p s (fun f : _138133 -> _138164 => fun x : P => @COND _138189 (P' f x) (h f x) (k f x)).
Axiom thm_ADMISSIBLE_MATCH : forall {_138230 _138231 _138232 _138264 _138267 P : Type'}, forall lt2 : _138231 -> _138230 -> Prop, forall p : (_138231 -> _138232) -> P -> Prop, forall s : P -> _138230, forall e : (_138231 -> _138232) -> P -> _138267, forall c : (_138231 -> _138232) -> P -> _138267 -> _138264 -> Prop, ((@admissible _138230 _138232 _138231 _138267 P lt2 p s e) /\ (@admissible _138230 _138232 _138231 (_138264 -> Prop) P lt2 p s (fun f : _138231 -> _138232 => fun x : P => c f x (e f x)))) -> @admissible _138230 _138232 _138231 _138264 P lt2 p s (fun f : _138231 -> _138232 => fun x : P => @_MATCH _138267 _138264 (e f x) (c f x)).
Axiom thm_ADMISSIBLE_SEQPATTERN : forall {_138307 _138308 _138370 _138386 _138396 P : Type'}, forall lt2 : _138308 -> _138307 -> Prop, forall p : (_138308 -> _138370) -> P -> Prop, forall s : P -> _138307, forall c1 : (_138308 -> _138370) -> P -> _138396 -> _138386 -> Prop, forall c2 : (_138308 -> _138370) -> P -> _138396 -> _138386 -> Prop, forall e : (_138308 -> _138370) -> P -> _138396, ((@admissible _138307 _138370 _138308 Prop P lt2 p s (fun f : _138308 -> _138370 => fun x : P => exists y : _138386, c1 f x (e f x) y)) /\ ((@admissible _138307 _138370 _138308 (_138386 -> Prop) P lt2 (fun f : _138308 -> _138370 => fun x : P => (p f x) /\ (exists y : _138386, c1 f x (e f x) y)) s (fun f : _138308 -> _138370 => fun x : P => c1 f x (e f x))) /\ (@admissible _138307 _138370 _138308 (_138386 -> Prop) P lt2 (fun f : _138308 -> _138370 => fun x : P => (p f x) /\ (~ (exists y : _138386, c1 f x (e f x) y))) s (fun f : _138308 -> _138370 => fun x : P => c2 f x (e f x))))) -> @admissible _138307 _138370 _138308 (_138386 -> Prop) P lt2 p s (fun f : _138308 -> _138370 => fun x : P => @_SEQPATTERN _138396 _138386 (c1 f x) (c2 f x) (e f x)).
Axiom thm_ADMISSIBLE_UNGUARDED_PATTERN : forall {_138481 _138482 _138529 _138562 _138569 P : Type'}, forall lt2 : _138482 -> _138481 -> Prop, forall p : (_138482 -> _138529) -> P -> Prop, forall s : P -> _138481, forall pat : (_138482 -> _138529) -> P -> _138562, forall e : (_138482 -> _138529) -> P -> _138562, forall t : (_138482 -> _138529) -> P -> _138569, forall y : (_138482 -> _138529) -> P -> _138569, ((@admissible _138481 _138529 _138482 _138562 P lt2 p s pat) /\ ((@admissible _138481 _138529 _138482 _138562 P lt2 p s e) /\ ((@admissible _138481 _138529 _138482 _138569 P lt2 (fun f : _138482 -> _138529 => fun x : P => (p f x) /\ ((pat f x) = (e f x))) s t) /\ (@admissible _138481 _138529 _138482 _138569 P lt2 (fun f : _138482 -> _138529 => fun x : P => (p f x) /\ ((pat f x) = (e f x))) s y)))) -> @admissible _138481 _138529 _138482 Prop P lt2 p s (fun f : _138482 -> _138529 => fun x : P => and (@eq _138562 (pat f x) (e f x)) (@eq _138569 (t f x) (y f x))).
Axiom thm_ADMISSIBLE_GUARDED_PATTERN : forall {_138655 _138656 _138733 _138771 _138780 P : Type'}, forall lt2 : _138656 -> _138655 -> Prop, forall p : (_138656 -> _138733) -> P -> Prop, forall s : P -> _138655, forall pat : (_138656 -> _138733) -> P -> _138771, forall q : (_138656 -> _138733) -> P -> Prop, forall e : (_138656 -> _138733) -> P -> _138771, forall t : (_138656 -> _138733) -> P -> _138780, forall y : (_138656 -> _138733) -> P -> _138780, ((@admissible _138655 _138733 _138656 _138771 P lt2 p s pat) /\ ((@admissible _138655 _138733 _138656 _138771 P lt2 p s e) /\ ((@admissible _138655 _138733 _138656 _138780 P lt2 (fun f : _138656 -> _138733 => fun x : P => (p f x) /\ (((pat f x) = (e f x)) /\ (q f x))) s t) /\ ((@admissible _138655 _138733 _138656 Prop P lt2 (fun f : _138656 -> _138733 => fun x : P => (p f x) /\ ((pat f x) = (e f x))) s q) /\ (@admissible _138655 _138733 _138656 _138780 P lt2 (fun f : _138656 -> _138733 => fun x : P => (p f x) /\ (((pat f x) = (e f x)) /\ (q f x))) s y))))) -> @admissible _138655 _138733 _138656 Prop P lt2 p s (fun f : _138656 -> _138733 => fun x : P => _GUARDED_PATTERN (@eq _138771 (pat f x) (e f x)) (q f x) (@eq _138780 (t f x) (y f x))).
Axiom thm_ADMISSIBLE_NSUM : forall {A B C P : Type'}, forall lt2 : B -> A -> Prop, forall p : (B -> C) -> P -> Prop, forall s : P -> A, forall h : (B -> C) -> P -> N -> N, forall a : P -> N, forall b : P -> N, (@admissible A C B N (prod N P) lt2 (fun f : B -> C => @ε ((prod N P) -> Prop) (fun f' : (prod N P) -> Prop => forall k : N, forall x : P, @eq Prop (f' (@pair N P k x)) ((N.le (a x) k) /\ ((N.le k (b x)) /\ (p f x))))) (@ε ((prod N P) -> A) (fun f : (prod N P) -> A => forall k : N, forall x : P, @eq A (f (@pair N P k x)) (s x))) (fun f : B -> C => @ε ((prod N P) -> N) (fun f' : (prod N P) -> N => forall k : N, forall x : P, @eq N (f' (@pair N P k x)) (h f x k)))) -> @admissible A C B N P lt2 p s (fun f : B -> C => fun x : P => @nsum N (Ninterval (a x) (b x)) (h f x)).
Axiom thm_ADMISSIBLE_SUM : forall {A B C P : Type'}, forall lt2 : B -> A -> Prop, forall p : (B -> C) -> P -> Prop, forall s : P -> A, forall h : (B -> C) -> P -> N -> R, forall a : P -> N, forall b : P -> N, (@admissible A C B R (prod N P) lt2 (fun f : B -> C => @ε ((prod N P) -> Prop) (fun f' : (prod N P) -> Prop => forall k : N, forall x : P, @eq Prop (f' (@pair N P k x)) ((N.le (a x) k) /\ ((N.le k (b x)) /\ (p f x))))) (@ε ((prod N P) -> A) (fun f : (prod N P) -> A => forall k : N, forall x : P, @eq A (f (@pair N P k x)) (s x))) (fun f : B -> C => @ε ((prod N P) -> R) (fun f' : (prod N P) -> R => forall k : N, forall x : P, @eq R (f' (@pair N P k x)) (h f x k)))) -> @admissible A C B R P lt2 p s (fun f : B -> C => fun x : P => @sum N (Ninterval (a x) (b x)) (h f x)).
Axiom thm_ADMISSIBLE_MAP : forall {_139073 _139082 _139088 A B P : Type'}, forall lt2 : A -> _139073 -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> _139073, forall h : (A -> B) -> P -> _139088 -> _139082, forall l : (A -> B) -> P -> list _139088, ((@admissible _139073 B A (list _139088) P lt2 p s l) /\ (@admissible _139073 B A _139082 (prod _139088 P) lt2 (fun f : A -> B => @ε ((prod _139088 P) -> Prop) (fun f' : (prod _139088 P) -> Prop => forall y : _139088, forall x : P, @eq Prop (f' (@pair _139088 P y x)) ((p f x) /\ (@List.In _139088 y (l f x))))) (@ε ((prod _139088 P) -> _139073) (fun f : (prod _139088 P) -> _139073 => forall y : _139088, forall x : P, @eq _139073 (f (@pair _139088 P y x)) (s x))) (fun f : A -> B => @ε ((prod _139088 P) -> _139082) (fun f' : (prod _139088 P) -> _139082 => forall y : _139088, forall x : P, @eq _139082 (f' (@pair _139088 P y x)) (h f x y))))) -> @admissible _139073 B A (list _139082) P lt2 p s (fun f : A -> B => fun x : P => @List.map _139088 _139082 (h f x) (l f x)).
Axiom thm_ADMISSIBLE_MATCH_SEQPATTERN : forall {_139145 _139146 _139211 _139235 _139266 P : Type'}, forall lt2 : _139146 -> _139145 -> Prop, forall p : (_139146 -> _139211) -> P -> Prop, forall s : P -> _139145, forall c1 : (_139146 -> _139211) -> P -> _139266 -> _139235 -> Prop, forall c2 : (_139146 -> _139211) -> P -> _139266 -> _139235 -> Prop, forall e : (_139146 -> _139211) -> P -> _139266, ((@admissible _139145 _139211 _139146 Prop P lt2 p s (fun f : _139146 -> _139211 => fun x : P => exists y : _139235, c1 f x (e f x) y)) /\ ((@admissible _139145 _139211 _139146 _139235 P lt2 (fun f : _139146 -> _139211 => fun x : P => (p f x) /\ (exists y : _139235, c1 f x (e f x) y)) s (fun f : _139146 -> _139211 => fun x : P => @_MATCH _139266 _139235 (e f x) (c1 f x))) /\ (@admissible _139145 _139211 _139146 _139235 P lt2 (fun f : _139146 -> _139211 => fun x : P => (p f x) /\ (~ (exists y : _139235, c1 f x (e f x) y))) s (fun f : _139146 -> _139211 => fun x : P => @_MATCH _139266 _139235 (e f x) (c2 f x))))) -> @admissible _139145 _139211 _139146 _139235 P lt2 p s (fun f : _139146 -> _139211 => fun x : P => @_MATCH _139266 _139235 (e f x) (@_SEQPATTERN _139266 _139235 (c1 f x) (c2 f x))).
Axiom thm_ADMISSIBLE_IMP_SUPERADMISSIBLE : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> B, (@admissible A B A B P lt2 p s t) -> @superadmissible A B P lt2 p s t.
Axiom thm_SUPERADMISSIBLE_CONST : forall {_139345 _139346 _139347 : Type'} (lt2 : _139345 -> _139345 -> Prop), forall p : (_139345 -> _139347) -> _139346 -> Prop, forall s : _139346 -> _139345, forall c : _139346 -> _139347, @superadmissible _139345 _139347 _139346 lt2 p s (fun f : _139345 -> _139347 => c).
Axiom thm_SUPERADMISSIBLE_TAIL : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> A, ((@admissible A B A A P lt2 p s t) /\ (forall f : A -> B, forall a : P, (p f a) -> forall y : A, (lt2 y (t f a)) -> lt2 y (s a))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => f (t f x)).
Axiom thm_SUPERADMISSIBLE_COND : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall P' : (A -> B) -> P -> Prop, forall s : P -> A, forall h : (A -> B) -> P -> B, forall k : (A -> B) -> P -> B, ((@admissible A B A Prop P lt2 p s P') /\ ((@superadmissible A B P lt2 (fun f : A -> B => fun x : P => (p f x) /\ (P' f x)) s h) /\ (@superadmissible A B P lt2 (fun f : A -> B => fun x : P => (p f x) /\ (~ (P' f x))) s k))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @COND B (P' f x) (h f x) (k f x)).
Axiom thm_SUPERADMISSIBLE_MATCH_SEQPATTERN : forall {_139666 _139781 _139782 P : Type'}, forall lt2 : _139666 -> _139666 -> Prop, forall p : (_139666 -> _139782) -> P -> Prop, forall s : P -> _139666, forall c1 : (_139666 -> _139782) -> P -> _139781 -> _139782 -> Prop, forall c2 : (_139666 -> _139782) -> P -> _139781 -> _139782 -> Prop, forall e : (_139666 -> _139782) -> P -> _139781, ((@admissible _139666 _139782 _139666 Prop P lt2 p s (fun f : _139666 -> _139782 => fun x : P => exists y : _139782, c1 f x (e f x) y)) /\ ((@superadmissible _139666 _139782 P lt2 (fun f : _139666 -> _139782 => fun x : P => (p f x) /\ (exists y : _139782, c1 f x (e f x) y)) s (fun f : _139666 -> _139782 => fun x : P => @_MATCH _139781 _139782 (e f x) (c1 f x))) /\ (@superadmissible _139666 _139782 P lt2 (fun f : _139666 -> _139782 => fun x : P => (p f x) /\ (~ (exists y : _139782, c1 f x (e f x) y))) s (fun f : _139666 -> _139782 => fun x : P => @_MATCH _139781 _139782 (e f x) (c2 f x))))) -> @superadmissible _139666 _139782 P lt2 p s (fun f : _139666 -> _139782 => fun x : P => @_MATCH _139781 _139782 (e f x) (@_SEQPATTERN _139781 _139782 (c1 f x) (c2 f x))).
Axiom thm_SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN : forall {A B D P Q : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall e : P -> D, forall pat : Q -> D, forall arg : P -> Q -> A, ((forall f : A -> B, forall a : P, forall t : Q, forall u : Q, ((p f a) /\ (((pat t) = (e a)) /\ ((pat u) = (e a)))) -> (arg a t) = (arg a u)) /\ (forall f : A -> B, forall a : P, forall t : Q, ((p f a) /\ ((pat t) = (e a))) -> forall y : A, (lt2 y (arg a t)) -> lt2 y (s a))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @_MATCH D B (e x) (fun u : D => fun v : B => exists t : Q, and (@eq D (pat t) u) (@eq B (f (arg x t)) v))).
Axiom thm_SUPERADMISSIBLE_MATCH_GUARDED_PATTERN : forall {A B D P Q : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall e : P -> D, forall pat : Q -> D, forall q : P -> Q -> Prop, forall arg : P -> Q -> A, ((forall f : A -> B, forall a : P, forall t : Q, forall u : Q, ((p f a) /\ (((pat t) = (e a)) /\ ((q a t) /\ (((pat u) = (e a)) /\ (q a u))))) -> (arg a t) = (arg a u)) /\ (forall f : A -> B, forall a : P, forall t : Q, ((p f a) /\ ((q a t) /\ ((pat t) = (e a)))) -> forall y : A, (lt2 y (arg a t)) -> lt2 y (s a))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @_MATCH D B (e x) (fun u : D => fun v : B => exists t : Q, _GUARDED_PATTERN (@eq D (pat t) u) (q x t) (@eq B (f (arg x t)) v))).
Axiom thm_WF_REC_CASES : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall clauses : list (prod (P -> A) ((A -> B) -> P -> B)), ((@well_founded A lt2) /\ (@List.Forall (prod (P -> A) ((A -> B) -> P -> B)) (@ε ((prod (P -> A) ((A -> B) -> P -> B)) -> Prop) (fun f : (prod (P -> A) ((A -> B) -> P -> B)) -> Prop => forall s : P -> A, forall t : (A -> B) -> P -> B, @eq Prop (f (@pair (P -> A) ((A -> B) -> P -> B) s t)) (exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f' : A -> B, forall a : P, forall y : A, ((P' f' a) /\ (lt2 y (G f' a))) -> lt2 y (s a)) /\ ((forall f' : A -> B, forall g : A -> B, forall a : P, (forall z : A, (lt2 z (s a)) -> (f' z) = (g z)) -> ((P' f' a) = (P' g a)) /\ (((G f' a) = (G g a)) /\ ((H f' a) = (H g a)))) /\ (forall f' : A -> B, forall a : P, (t f' a) = (@COND B (P' f' a) (f' (G f' a)) (H f' a))))))) clauses)) -> exists f : A -> B, forall x : A, (f x) = (@CASEWISE B P A (A -> B) clauses f x).
Axiom thm_RECURSION_CASEWISE : forall {A B P : Type'}, forall clauses : list (prod (P -> A) ((A -> B) -> P -> B)), ((exists lt2 : A -> A -> Prop, (@well_founded A lt2) /\ (@List.Forall (prod (P -> A) ((A -> B) -> P -> B)) (@ε ((prod (P -> A) ((A -> B) -> P -> B)) -> Prop) (fun f : (prod (P -> A) ((A -> B) -> P -> B)) -> Prop => forall s : P -> A, forall t : (A -> B) -> P -> B, @eq Prop (f (@pair (P -> A) ((A -> B) -> P -> B) s t)) (@tailadmissible A B P lt2 (fun f' : A -> B => fun a : P => True) s t))) clauses)) /\ (forall s : P -> A, forall t : (A -> B) -> P -> B, forall s' : P -> A, forall t' : (A -> B) -> P -> B, forall f : A -> B, forall x : P, forall y : P, ((@List.In (prod (P -> A) ((A -> B) -> P -> B)) (@pair (P -> A) ((A -> B) -> P -> B) s t) clauses) /\ (@List.In (prod (P -> A) ((A -> B) -> P -> B)) (@pair (P -> A) ((A -> B) -> P -> B) s' t') clauses)) -> ((s x) = (s' y)) -> (t f x) = (t' f y))) -> exists f : A -> B, @List.Forall (prod (P -> A) ((A -> B) -> P -> B)) (@ε ((prod (P -> A) ((A -> B) -> P -> B)) -> Prop) (fun f' : (prod (P -> A) ((A -> B) -> P -> B)) -> Prop => forall s : P -> A, forall t : (A -> B) -> P -> B, @eq Prop (f' (@pair (P -> A) ((A -> B) -> P -> B) s t)) (forall x : P, (f (s x)) = (t f x)))) clauses.
Axiom thm_RECURSION_CASEWISE_PAIRWISE : forall {_141005 _141021 _141025 : Type'}, forall clauses : list (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)), ((exists lt2 : _141005 -> _141005 -> Prop, (@well_founded _141005 lt2) /\ (@List.Forall (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) (@ε ((prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop) (fun f : (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop => forall s : _141025 -> _141005, forall t : (_141005 -> _141021) -> _141025 -> _141021, @eq Prop (f (@pair (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021) s t)) (@tailadmissible _141005 _141021 _141025 lt2 (fun f' : _141005 -> _141021 => fun a : _141025 => True) s t))) clauses)) /\ ((@List.Forall (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) (@ε ((prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop) (fun f : (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop => forall s : _141025 -> _141005, forall t : (_141005 -> _141021) -> _141025 -> _141021, @eq Prop (f (@pair (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021) s t)) (forall f' : _141005 -> _141021, forall x : _141025, forall y : _141025, ((s x) = (s y)) -> (t f' x) = (t f' y)))) clauses) /\ (@List.ForallOrdPairs (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) (@ε ((prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop) (fun f : (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop => forall s : _141025 -> _141005, forall t : (_141005 -> _141021) -> _141025 -> _141021, @eq ((prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop) (f (@pair (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021) s t)) (@ε ((prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop) (fun f' : (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop => forall s' : _141025 -> _141005, forall t' : (_141005 -> _141021) -> _141025 -> _141021, @eq Prop (f' (@pair (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021) s' t')) (forall f'' : _141005 -> _141021, forall x : _141025, forall y : _141025, ((s x) = (s' y)) -> (t f'' x) = (t' f'' y)))))) clauses))) -> exists f : _141005 -> _141021, @List.Forall (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) (@ε ((prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop) (fun f' : (prod (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021)) -> Prop => forall s : _141025 -> _141005, forall t : (_141005 -> _141021) -> _141025 -> _141021, @eq Prop (f' (@pair (_141025 -> _141005) ((_141005 -> _141021) -> _141025 -> _141021) s t)) (forall x : _141025, (f (s x)) = (t f x)))) clauses.
Axiom thm_SUPERADMISSIBLE_T : forall {_141135 _141137 _141141 : Type'} (lt2 : _141135 -> _141135 -> Prop) (s : _141141 -> _141135) (t : (_141135 -> _141137) -> _141141 -> _141137), (@superadmissible _141135 _141137 _141141 lt2 (fun f : _141135 -> _141137 => fun x : _141141 => True) s t) = (@tailadmissible _141135 _141137 _141141 lt2 (fun f : _141135 -> _141137 => fun x : _141141 => True) s t).
Axiom thm_F_IMP : forall t : Prop, (~ t) -> t -> False.
Axiom thm_LEFT_AND_OVER_OR : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 /\ (t2 \/ t3)) = ((t1 /\ t2) \/ (t1 /\ t3)).
Axiom thm_RIGHT_AND_OVER_OR : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, ((t2 \/ t3) /\ t1) = ((t2 /\ t1) \/ (t3 /\ t1)).
Axiom thm_SUC_SUB1 : forall m : N, (N.sub (N.succ m) ((BIT1 N0))) = m.
Axiom thm_SUB_SUB : forall b : N, forall c : N, (N.le c b) -> forall a : N, (N.sub a (N.sub b c)) = (N.sub (N.add a c) b).
Axiom thm_SUB_OLD : (forall m : N, (N.sub N0 m) = N0) /\ (forall m : N, forall n : N, (N.sub (N.succ m) n) = (@COND N (N.lt m n) N0 (N.succ (N.sub m n)))).
Axiom thm_real_le : forall x : R, forall y : R, (Rle x y) = (~ (Rlt y x)).
Axiom thm_REAL_MUL_RID : forall x : R, (Rmult x (R_of_N ((BIT1 N0)))) = x.
Axiom thm_REAL_MUL_RINV : forall x : R, (~ (x = (R_of_N N0))) -> (Rmult x (Rinv x)) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_RDISTRIB : forall x : R, forall y : R, forall z : R, (Rmult (Rplus x y) z) = (Rplus (Rmult x z) (Rmult y z)).
Axiom thm_REAL_EQ_LADD : forall x : R, forall y : R, forall z : R, ((Rplus x y) = (Rplus x z)) = (y = z).
Axiom thm_REAL_EQ_RADD : forall x : R, forall y : R, forall z : R, ((Rplus x z) = (Rplus y z)) = (x = y).
Axiom thm_REAL_ADD_LID_UNIQ : forall x : R, forall y : R, ((Rplus x y) = y) = (x = (R_of_N N0)).
Axiom thm_REAL_ADD_RID_UNIQ : forall x : R, forall y : R, ((Rplus x y) = x) = (y = (R_of_N N0)).
Axiom thm_REAL_LNEG_UNIQ : forall x : R, forall y : R, ((Rplus x y) = (R_of_N N0)) = (x = (Ropp y)).
Axiom thm_REAL_RNEG_UNIQ : forall x : R, forall y : R, ((Rplus x y) = (R_of_N N0)) = (y = (Ropp x)).
Axiom thm_REAL_NEG_ADD : forall x : R, forall y : R, (Ropp (Rplus x y)) = (Rplus (Ropp x) (Ropp y)).
Axiom thm_REAL_MUL_LZERO : forall x : R, (Rmult (R_of_N N0) x) = (R_of_N N0).
Axiom thm_REAL_MUL_RZERO : forall x : R, (Rmult x (R_of_N N0)) = (R_of_N N0).
Axiom thm_REAL_NEG_LMUL : forall x : R, forall y : R, (Ropp (Rmult x y)) = (Rmult (Ropp x) y).
Axiom thm_REAL_NEG_RMUL : forall x : R, forall y : R, (Ropp (Rmult x y)) = (Rmult x (Ropp y)).
Axiom thm_REAL_NEG_NEG : forall x : R, (Ropp (Ropp x)) = x.
Axiom thm_REAL_NEG_MUL2 : forall x : R, forall y : R, (Rmult (Ropp x) (Ropp y)) = (Rmult x y).
Axiom thm_REAL_LT_LADD : forall x : R, forall y : R, forall z : R, (Rlt (Rplus x y) (Rplus x z)) = (Rlt y z).
Axiom thm_REAL_LT_RADD : forall x : R, forall y : R, forall z : R, (Rlt (Rplus x z) (Rplus y z)) = (Rlt x y).
Axiom thm_REAL_NOT_LT : forall x : R, forall y : R, (~ (Rlt x y)) = (Rle y x).
Axiom thm_REAL_LT_ANTISYM : forall x : R, forall y : R, ~ ((Rlt x y) /\ (Rlt y x)).
Axiom thm_REAL_LT_GT : forall x : R, forall y : R, (Rlt x y) -> ~ (Rlt y x).
Axiom thm_REAL_NOT_LE : forall x : R, forall y : R, (~ (Rle x y)) = (Rlt y x).
Axiom thm_REAL_LE_TOTAL : forall x : R, forall y : R, (Rle x y) \/ (Rle y x).
Axiom thm_REAL_LE_REFL : forall x : R, Rle x x.
Axiom thm_REAL_LE_LT : forall x : R, forall y : R, (Rle x y) = ((Rlt x y) \/ (x = y)).
Axiom thm_REAL_LT_LE : forall x : R, forall y : R, (Rlt x y) = ((Rle x y) /\ (~ (x = y))).
Axiom thm_REAL_LT_IMP_LE : forall x : R, forall y : R, (Rlt x y) -> Rle x y.
Axiom thm_REAL_LTE_TRANS : forall x : R, forall y : R, forall z : R, ((Rlt x y) /\ (Rle y z)) -> Rlt x z.
Axiom thm_REAL_LE_TRANS : forall x : R, forall y : R, forall z : R, ((Rle x y) /\ (Rle y z)) -> Rle x z.
Axiom thm_REAL_NEG_LT0 : forall x : R, (Rlt (Ropp x) (R_of_N N0)) = (Rlt (R_of_N N0) x).
Axiom thm_REAL_NEG_GT0 : forall x : R, (Rlt (R_of_N N0) (Ropp x)) = (Rlt x (R_of_N N0)).
Axiom thm_REAL_NEG_LE0 : forall x : R, (Rle (Ropp x) (R_of_N N0)) = (Rle (R_of_N N0) x).
Axiom thm_REAL_NEG_GE0 : forall x : R, (Rle (R_of_N N0) (Ropp x)) = (Rle x (R_of_N N0)).
Axiom thm_REAL_LT_NEGTOTAL : forall x : R, (x = (R_of_N N0)) \/ ((Rlt (R_of_N N0) x) \/ (Rlt (R_of_N N0) (Ropp x))).
Axiom thm_REAL_LE_NEGTOTAL : forall x : R, (Rle (R_of_N N0) x) \/ (Rle (R_of_N N0) (Ropp x)).
Axiom thm_REAL_LE_MUL : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rle (R_of_N N0) y)) -> Rle (R_of_N N0) (Rmult x y).
Axiom thm_REAL_LE_SQUARE : forall x : R, Rle (R_of_N N0) (Rmult x x).
Axiom thm_REAL_LT_01 : Rlt (R_of_N N0) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_LE_LADD : forall x : R, forall y : R, forall z : R, (Rle (Rplus x y) (Rplus x z)) = (Rle y z).
Axiom thm_REAL_LE_RADD : forall x : R, forall y : R, forall z : R, (Rle (Rplus x z) (Rplus y z)) = (Rle x y).
Axiom thm_REAL_LT_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((Rlt w x) /\ (Rlt y z)) -> Rlt (Rplus w y) (Rplus x z).
Axiom thm_REAL_LT_ADD : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rlt (R_of_N N0) y)) -> Rlt (R_of_N N0) (Rplus x y).
Axiom thm_REAL_LT_ADDNEG : forall x : R, forall y : R, forall z : R, (Rlt y (Rplus x (Ropp z))) = (Rlt (Rplus y z) x).
Axiom thm_REAL_LT_ADDNEG2 : forall x : R, forall y : R, forall z : R, (Rlt (Rplus x (Ropp y)) z) = (Rlt x (Rplus z y)).
Axiom thm_REAL_LT_ADD1 : forall x : R, forall y : R, (Rle x y) -> Rlt x (Rplus y (R_of_N ((BIT1 N0)))).
Axiom thm_REAL_SUB_ADD : forall x : R, forall y : R, (Rplus (Rminus x y) y) = x.
Axiom thm_REAL_SUB_ADD2 : forall x : R, forall y : R, (Rplus y (Rminus x y)) = x.
Axiom thm_REAL_SUB_REFL : forall x : R, (Rminus x x) = (R_of_N N0).
Axiom thm_REAL_SUB_0 : forall x : R, forall y : R, ((Rminus x y) = (R_of_N N0)) = (x = y).
Axiom thm_REAL_LE_DOUBLE : forall x : R, (Rle (R_of_N N0) (Rplus x x)) = (Rle (R_of_N N0) x).
Axiom thm_REAL_LE_NEGL : forall x : R, (Rle (Ropp x) x) = (Rle (R_of_N N0) x).
Axiom thm_REAL_LE_NEGR : forall x : R, (Rle x (Ropp x)) = (Rle x (R_of_N N0)).
Axiom thm_REAL_NEG_EQ0 : forall x : R, ((Ropp x) = (R_of_N N0)) = (x = (R_of_N N0)).
Axiom thm_REAL_NEG_0 : (Ropp (R_of_N N0)) = (R_of_N N0).
Axiom thm_REAL_NEG_SUB : forall x : R, forall y : R, (Ropp (Rminus x y)) = (Rminus y x).
Axiom thm_REAL_SUB_LT : forall x : R, forall y : R, (Rlt (R_of_N N0) (Rminus x y)) = (Rlt y x).
Axiom thm_REAL_SUB_LE : forall x : R, forall y : R, (Rle (R_of_N N0) (Rminus x y)) = (Rle y x).
Axiom thm_REAL_EQ_LMUL : forall x : R, forall y : R, forall z : R, ((Rmult x y) = (Rmult x z)) = ((x = (R_of_N N0)) \/ (y = z)).
Axiom thm_REAL_EQ_RMUL : forall x : R, forall y : R, forall z : R, ((Rmult x z) = (Rmult y z)) = ((z = (R_of_N N0)) \/ (x = y)).
Axiom thm_REAL_SUB_LDISTRIB : forall x : R, forall y : R, forall z : R, (Rmult x (Rminus y z)) = (Rminus (Rmult x y) (Rmult x z)).
Axiom thm_REAL_SUB_RDISTRIB : forall x : R, forall y : R, forall z : R, (Rmult (Rminus x y) z) = (Rminus (Rmult x z) (Rmult y z)).
Axiom thm_REAL_NEG_EQ : forall x : R, forall y : R, ((Ropp x) = y) = (x = (Ropp y)).
Axiom thm_REAL_NEG_MINUS1 : forall x : R, (Ropp x) = (Rmult (Ropp (R_of_N ((BIT1 N0)))) x).
Axiom thm_REAL_INV_NZ : forall x : R, (~ (x = (R_of_N N0))) -> ~ ((Rinv x) = (R_of_N N0)).
Axiom thm_REAL_INVINV : forall x : R, (~ (x = (R_of_N N0))) -> (Rinv (Rinv x)) = x.
Axiom thm_REAL_LT_IMP_NE : forall x : R, forall y : R, (Rlt x y) -> ~ (x = y).
Axiom thm_REAL_INV_POS : forall x : R, (Rlt (R_of_N N0) x) -> Rlt (R_of_N N0) (Rinv x).
Axiom thm_REAL_LT_LMUL_0 : forall x : R, forall y : R, (Rlt (R_of_N N0) x) -> (Rlt (R_of_N N0) (Rmult x y)) = (Rlt (R_of_N N0) y).
Axiom thm_REAL_LT_RMUL_0 : forall x : R, forall y : R, (Rlt (R_of_N N0) y) -> (Rlt (R_of_N N0) (Rmult x y)) = (Rlt (R_of_N N0) x).
Axiom thm_REAL_LT_LMUL_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) x) -> (Rlt (Rmult x y) (Rmult x z)) = (Rlt y z).
Axiom thm_REAL_LT_RMUL_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rlt (Rmult x z) (Rmult y z)) = (Rlt x y).
Axiom thm_REAL_LT_RMUL_IMP : forall x : R, forall y : R, forall z : R, ((Rlt x y) /\ (Rlt (R_of_N N0) z)) -> Rlt (Rmult x z) (Rmult y z).
Axiom thm_REAL_LT_LMUL_IMP : forall x : R, forall y : R, forall z : R, ((Rlt y z) /\ (Rlt (R_of_N N0) x)) -> Rlt (Rmult x y) (Rmult x z).
Axiom thm_REAL_LINV_UNIQ : forall x : R, forall y : R, ((Rmult x y) = (R_of_N ((BIT1 N0)))) -> x = (Rinv y).
Axiom thm_REAL_RINV_UNIQ : forall x : R, forall y : R, ((Rmult x y) = (R_of_N ((BIT1 N0)))) -> y = (Rinv x).
Axiom thm_REAL_NEG_INV : forall x : R, (~ (x = (R_of_N N0))) -> (Ropp (Rinv x)) = (Rinv (Ropp x)).
Axiom thm_REAL_INV_1OVER : forall x : R, (Rinv x) = (Rdiv (R_of_N ((BIT1 N0))) x).
Axiom thm_REAL : forall n : N, (R_of_N (N.succ n)) = (Rplus (R_of_N n) (R_of_N ((BIT1 N0)))).
Axiom thm_REAL_POS : forall n : N, Rle (R_of_N N0) (R_of_N n).
Axiom thm_REAL_LE : forall m : N, forall n : N, (Rle (R_of_N m) (R_of_N n)) = (N.le m n).
Axiom thm_REAL_LT : forall m : N, forall n : N, (Rlt (R_of_N m) (R_of_N n)) = (N.lt m n).
Axiom thm_REAL_INJ : forall m : N, forall n : N, ((R_of_N m) = (R_of_N n)) = (m = n).
Axiom thm_REAL_ADD : forall m : N, forall n : N, (Rplus (R_of_N m) (R_of_N n)) = (R_of_N (N.add m n)).
Axiom thm_REAL_MUL : forall m : N, forall n : N, (Rmult (R_of_N m) (R_of_N n)) = (R_of_N (N.mul m n)).
Axiom thm_REAL_INV1 : (Rinv (R_of_N ((BIT1 N0)))) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_DIV_LZERO : forall x : R, (Rdiv (R_of_N N0) x) = (R_of_N N0).
Axiom thm_REAL_LT_NZ : forall n : N, (~ ((R_of_N n) = (R_of_N N0))) = (Rlt (R_of_N N0) (R_of_N n)).
Axiom thm_REAL_NZ_IMP_LT : forall n : N, (~ (n = N0)) -> Rlt (R_of_N N0) (R_of_N n).
Axiom thm_REAL_LT_RDIV_0 : forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rlt (R_of_N N0) (Rdiv y z)) = (Rlt (R_of_N N0) y).
Axiom thm_REAL_LT_RDIV : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rlt (Rdiv x z) (Rdiv y z)) = (Rlt x y).
Axiom thm_REAL_LT_FRACTION_0 : forall n : N, forall d : R, (~ (n = N0)) -> (Rlt (R_of_N N0) (Rdiv d (R_of_N n))) = (Rlt (R_of_N N0) d).
Axiom thm_REAL_LT_MULTIPLE : forall n : N, forall d : R, (N.lt ((BIT1 N0)) n) -> (Rlt d (Rmult (R_of_N n) d)) = (Rlt (R_of_N N0) d).
Axiom thm_REAL_LT_FRACTION : forall n : N, forall d : R, (N.lt ((BIT1 N0)) n) -> (Rlt (Rdiv d (R_of_N n)) d) = (Rlt (R_of_N N0) d).
Axiom thm_REAL_LT_HALF1 : forall d : R, (Rlt (R_of_N N0) (Rdiv d (R_of_N ((BIT0 (BIT1 N0)))))) = (Rlt (R_of_N N0) d).
Axiom thm_REAL_LT_HALF2 : forall d : R, (Rlt (Rdiv d (R_of_N ((BIT0 (BIT1 N0))))) d) = (Rlt (R_of_N N0) d).
Axiom thm_REAL_DOUBLE : forall x : R, (Rplus x x) = (Rmult (R_of_N ((BIT0 (BIT1 N0)))) x).
Axiom thm_REAL_HALF_DOUBLE : forall x : R, (Rplus (Rdiv x (R_of_N ((BIT0 (BIT1 N0))))) (Rdiv x (R_of_N ((BIT0 (BIT1 N0)))))) = x.
Axiom thm_REAL_SUB_SUB : forall x : R, forall y : R, (Rminus (Rminus x y) x) = (Ropp y).
Axiom thm_REAL_LT_ADD_SUB : forall x : R, forall y : R, forall z : R, (Rlt (Rplus x y) z) = (Rlt x (Rminus z y)).
Axiom thm_REAL_LT_SUB_RADD : forall x : R, forall y : R, forall z : R, (Rlt (Rminus x y) z) = (Rlt x (Rplus z y)).
Axiom thm_REAL_LT_SUB_LADD : forall x : R, forall y : R, forall z : R, (Rlt x (Rminus y z)) = (Rlt (Rplus x z) y).
Axiom thm_REAL_LE_SUB_LADD : forall x : R, forall y : R, forall z : R, (Rle x (Rminus y z)) = (Rle (Rplus x z) y).
Axiom thm_REAL_LE_SUB_RADD : forall x : R, forall y : R, forall z : R, (Rle (Rminus x y) z) = (Rle x (Rplus z y)).
Axiom thm_REAL_LT_NEG2 : forall x : R, forall y : R, (Rlt (Ropp x) (Ropp y)) = (Rlt y x).
Axiom thm_REAL_LE_NEG2 : forall x : R, forall y : R, (Rle (Ropp x) (Ropp y)) = (Rle y x).
Axiom thm_REAL_SUB_LZERO : forall x : R, (Rminus (R_of_N N0) x) = (Ropp x).
Axiom thm_REAL_SUB_RZERO : forall x : R, (Rminus x (R_of_N N0)) = x.
Axiom thm_REAL_LTE_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((Rlt w x) /\ (Rle y z)) -> Rlt (Rplus w y) (Rplus x z).
Axiom thm_REAL_LTE_ADD : forall x : R, forall y : R, ((Rlt (R_of_N N0) x) /\ (Rle (R_of_N N0) y)) -> Rlt (R_of_N N0) (Rplus x y).
Axiom thm_REAL_LT_MUL2_ALT : forall x1 : R, forall x2 : R, forall y1 : R, forall y2 : R, ((Rle (R_of_N N0) x1) /\ ((Rle (R_of_N N0) y1) /\ ((Rlt x1 x2) /\ (Rlt y1 y2)))) -> Rlt (Rmult x1 y1) (Rmult x2 y2).
Axiom thm_REAL_SUB_LNEG : forall x : R, forall y : R, (Rminus (Ropp x) y) = (Ropp (Rplus x y)).
Axiom thm_REAL_SUB_RNEG : forall x : R, forall y : R, (Rminus x (Ropp y)) = (Rplus x y).
Axiom thm_REAL_SUB_NEG2 : forall x : R, forall y : R, (Rminus (Ropp x) (Ropp y)) = (Rminus y x).
Axiom thm_REAL_SUB_TRIANGLE : forall a : R, forall b : R, forall c : R, (Rplus (Rminus a b) (Rminus b c)) = (Rminus a c).
Axiom thm_REAL_INV_MUL_WEAK : forall x : R, forall y : R, ((~ (x = (R_of_N N0))) /\ (~ (y = (R_of_N N0)))) -> (Rinv (Rmult x y)) = (Rmult (Rinv x) (Rinv y)).
Axiom thm_REAL_LE_LMUL_LOCAL : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) x) -> (Rle (Rmult x y) (Rmult x z)) = (Rle y z).
Axiom thm_REAL_LE_RMUL_EQ : forall x : R, forall y : R, forall z : R, (Rlt (R_of_N N0) z) -> (Rle (Rmult x z) (Rmult y z)) = (Rle x y).
Axiom thm_REAL_SUB_INV2 : forall x : R, forall y : R, ((~ (x = (R_of_N N0))) /\ (~ (y = (R_of_N N0)))) -> (Rminus (Rinv x) (Rinv y)) = (Rdiv (Rminus y x) (Rmult x y)).
Axiom thm_REAL_SUB_SUB2 : forall x : R, forall y : R, (Rminus x (Rminus x y)) = y.
Axiom thm_REAL_MEAN : forall x : R, forall y : R, (Rlt x y) -> exists z : R, (Rlt x z) /\ (Rlt z y).
Axiom thm_REAL_EQ_LMUL2 : forall x : R, forall y : R, forall z : R, (~ (x = (R_of_N N0))) -> (y = z) = ((Rmult x y) = (Rmult x z)).
Axiom thm_REAL_LE_MUL2V : forall x1 : R, forall x2 : R, forall y1 : R, forall y2 : R, ((Rle (R_of_N N0) x1) /\ ((Rle (R_of_N N0) y1) /\ ((Rle x1 x2) /\ (Rle y1 y2)))) -> Rle (Rmult x1 y1) (Rmult x2 y2).
Axiom thm_REAL_LE_LDIV : forall x : R, forall y : R, forall z : R, ((Rlt (R_of_N N0) x) /\ (Rle y (Rmult z x))) -> Rle (Rdiv y x) z.
Axiom thm_REAL_LE_RDIV : forall x : R, forall y : R, forall z : R, ((Rlt (R_of_N N0) x) /\ (Rle (Rmult y x) z)) -> Rle y (Rdiv z x).
Axiom thm_REAL_LT_1 : forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rlt x y)) -> Rlt (Rdiv x y) (R_of_N ((BIT1 N0))).
Axiom thm_REAL_LE_LMUL_IMP : forall x : R, forall y : R, forall z : R, ((Rle (R_of_N N0) x) /\ (Rle y z)) -> Rle (Rmult x y) (Rmult x z).
Axiom thm_REAL_LE_RMUL_IMP : forall x : R, forall y : R, forall z : R, ((Rle (R_of_N N0) x) /\ (Rle y z)) -> Rle (Rmult y x) (Rmult z x).
Axiom thm_REAL_INV_LT1 : forall x : R, ((Rlt (R_of_N N0) x) /\ (Rlt x (R_of_N ((BIT1 N0))))) -> Rlt (R_of_N ((BIT1 N0))) (Rinv x).
Axiom thm_REAL_LT_IMP_NZ : forall x : R, (Rlt (R_of_N N0) x) -> ~ (x = (R_of_N N0)).
Axiom thm_REAL_EQ_RMUL_IMP : forall x : R, forall y : R, forall z : R, ((~ (z = (R_of_N N0))) /\ ((Rmult x z) = (Rmult y z))) -> x = y.
Axiom thm_REAL_EQ_LMUL_IMP : forall x : R, forall y : R, forall z : R, ((~ (x = (R_of_N N0))) /\ ((Rmult x y) = (Rmult x z))) -> y = z.
Axiom thm_REAL_FACT_NZ : forall n : N, ~ ((R_of_N (fact n)) = (R_of_N N0)).
Axiom thm_REAL_POSSQ : forall x : R, (Rlt (R_of_N N0) (Rmult x x)) = (~ (x = (R_of_N N0))).
Axiom thm_REAL_SUMSQ : forall x : R, forall y : R, ((Rplus (Rmult x x) (Rmult y y)) = (R_of_N N0)) = ((x = (R_of_N N0)) /\ (y = (R_of_N N0))).
Axiom thm_REAL_EQ_NEG : forall x : R, forall y : R, ((Ropp x) = (Ropp y)) = (x = y).
Axiom thm_REAL_DIV_MUL2 : forall x : R, forall z : R, ((~ (x = (R_of_N N0))) /\ (~ (z = (R_of_N N0)))) -> forall y : R, (Rdiv y z) = (Rdiv (Rmult x y) (Rmult x z)).
Axiom thm_REAL_MIDDLE1 : forall a : R, forall b : R, (Rle a b) -> Rle a (Rdiv (Rplus a b) (R_of_N ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_MIDDLE2 : forall a : R, forall b : R, (Rle a b) -> Rle (Rdiv (Rplus a b) (R_of_N ((BIT0 (BIT1 N0))))) b.
Axiom thm_ABS_ZERO : forall x : R, ((Rabs x) = (R_of_N N0)) = (x = (R_of_N N0)).
Axiom thm_ABS_0 : (Rabs (R_of_N N0)) = (R_of_N N0).
Axiom thm_ABS_1 : (Rabs (R_of_N ((BIT1 N0)))) = (R_of_N ((BIT1 N0))).
Axiom thm_ABS_NEG : forall x : R, (Rabs (Ropp x)) = (Rabs x).
Axiom thm_ABS_TRIANGLE : forall x : R, forall y : R, Rle (Rabs (Rplus x y)) (Rplus (Rabs x) (Rabs y)).
Axiom thm_ABS_POS : forall x : R, Rle (R_of_N N0) (Rabs x).
Axiom thm_ABS_MUL : forall x : R, forall y : R, (Rabs (Rmult x y)) = (Rmult (Rabs x) (Rabs y)).
Axiom thm_ABS_LT_MUL2 : forall w : R, forall x : R, forall y : R, forall z : R, ((Rlt (Rabs w) y) /\ (Rlt (Rabs x) z)) -> Rlt (Rabs (Rmult w x)) (Rmult y z).
Axiom thm_ABS_SUB : forall x : R, forall y : R, (Rabs (Rminus x y)) = (Rabs (Rminus y x)).
Axiom thm_ABS_NZ : forall x : R, (~ (x = (R_of_N N0))) = (Rlt (R_of_N N0) (Rabs x)).
Axiom thm_ABS_INV : forall x : R, (~ (x = (R_of_N N0))) -> (Rabs (Rinv x)) = (Rinv (Rabs x)).
Axiom thm_ABS_ABS : forall x : R, (Rabs (Rabs x)) = (Rabs x).
Axiom thm_ABS_LE : forall x : R, Rle x (Rabs x).
Axiom thm_ABS_REFL : forall x : R, ((Rabs x) = x) = (Rle (R_of_N N0) x).
Axiom thm_ABS_N : forall n : N, (Rabs (R_of_N n)) = (R_of_N n).
Axiom thm_ABS_BETWEEN : forall x : R, forall y : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((Rlt (Rminus x d) y) /\ (Rlt y (Rplus x d)))) = (Rlt (Rabs (Rminus y x)) d).
Axiom thm_ABS_BOUND : forall x : R, forall y : R, forall d : R, (Rlt (Rabs (Rminus x y)) d) -> Rlt y (Rplus x d).
Axiom thm_ABS_STILLNZ : forall x : R, forall y : R, (Rlt (Rabs (Rminus x y)) (Rabs y)) -> ~ (x = (R_of_N N0)).
Axiom thm_ABS_CASES : forall x : R, (x = (R_of_N N0)) \/ (Rlt (R_of_N N0) (Rabs x)).
Axiom thm_ABS_BETWEEN1 : forall x : R, forall y : R, forall z : R, ((Rlt x z) /\ (Rlt (Rabs (Rminus y x)) (Rminus z x))) -> Rlt y z.
Axiom thm_ABS_SIGN : forall x : R, forall y : R, (Rlt (Rabs (Rminus x y)) y) -> Rlt (R_of_N N0) x.
Axiom thm_ABS_SIGN2 : forall x : R, forall y : R, (Rlt (Rabs (Rminus x y)) (Ropp y)) -> Rlt x (R_of_N N0).
Axiom thm_ABS_DIV : forall y : R, (~ (y = (R_of_N N0))) -> forall x : R, (Rabs (Rdiv x y)) = (Rdiv (Rabs x) (Rabs y)).
Axiom thm_ABS_CIRCLE : forall x : R, forall y : R, forall h : R, (Rlt (Rabs h) (Rminus (Rabs y) (Rabs x))) -> Rlt (Rabs (Rplus x h)) (Rabs y).
Axiom thm_REAL_SUB_ABS : forall x : R, forall y : R, Rle (Rminus (Rabs x) (Rabs y)) (Rabs (Rminus x y)).
Axiom thm_ABS_SUB_ABS : forall x : R, forall y : R, Rle (Rabs (Rminus (Rabs x) (Rabs y))) (Rabs (Rminus x y)).
Axiom thm_ABS_BETWEEN2 : forall x0 : R, forall x : R, forall y0 : R, forall y : R, ((Rlt x0 y0) /\ ((Rlt (Rabs (Rminus x x0)) (Rdiv (Rminus y0 x0) (R_of_N ((BIT0 (BIT1 N0)))))) /\ (Rlt (Rabs (Rminus y y0)) (Rdiv (Rminus y0 x0) (R_of_N ((BIT0 (BIT1 N0)))))))) -> Rlt x y.
Axiom thm_ABS_BOUNDS : forall x : R, forall k : R, (Rle (Rabs x) k) = ((Rle (Ropp k) x) /\ (Rle x k)).
Axiom thm_POW_0 : forall n : N, (Rpow (R_of_N N0) (N.succ n)) = (R_of_N N0).
Axiom thm_POW_NZ : forall c : R, forall n : N, (~ (c = (R_of_N N0))) -> ~ ((Rpow c n) = (R_of_N N0)).
Axiom thm_POW_INV : forall c : R, forall n : N, (~ (c = (R_of_N N0))) -> (Rinv (Rpow c n)) = (Rpow (Rinv c) n).
Axiom thm_POW_ABS : forall c : R, forall n : N, (Rpow (Rabs c) n) = (Rabs (Rpow c n)).
Axiom thm_POW_PLUS1 : forall e : R, forall n : N, (Rlt (R_of_N N0) e) -> Rle (Rplus (R_of_N ((BIT1 N0))) (Rmult (R_of_N n) e)) (Rpow (Rplus (R_of_N ((BIT1 N0))) e) n).
Axiom thm_POW_ADD : forall c : R, forall m : N, forall n : N, (Rpow c (N.add m n)) = (Rmult (Rpow c m) (Rpow c n)).
Axiom thm_POW_1 : forall x : R, (Rpow x ((BIT1 N0))) = x.
Axiom thm_POW_2 : forall x : R, (Rpow x ((BIT0 (BIT1 N0)))) = (Rmult x x).
Axiom thm_POW_POS : forall x : R, forall n : N, (Rle (R_of_N N0) x) -> Rle (R_of_N N0) (Rpow x n).
Axiom thm_POW_LE : forall n : N, forall x : R, forall y : R, ((Rle (R_of_N N0) x) /\ (Rle x y)) -> Rle (Rpow x n) (Rpow y n).
Axiom thm_POW_M1 : forall n : N, (Rabs (Rpow (Ropp (R_of_N ((BIT1 N0)))) n)) = (R_of_N ((BIT1 N0))).
Axiom thm_POW_MUL : forall n : N, forall x : R, forall y : R, (Rpow (Rmult x y) n) = (Rmult (Rpow x n) (Rpow y n)).
Axiom thm_REAL_LE_SQUARE_POW : forall x : R, Rle (R_of_N N0) (Rpow x ((BIT0 (BIT1 N0)))).
Axiom thm_ABS_POW2 : forall x : R, (Rabs (Rpow x ((BIT0 (BIT1 N0))))) = (Rpow x ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_LE1_POW2 : forall x : R, (Rle (R_of_N ((BIT1 N0))) x) -> Rle (R_of_N ((BIT1 N0))) (Rpow x ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_LT1_POW2 : forall x : R, (Rlt (R_of_N ((BIT1 N0))) x) -> Rlt (R_of_N ((BIT1 N0))) (Rpow x ((BIT0 (BIT1 N0)))).
Axiom thm_POW_POS_LT : forall x : R, forall n : N, (Rlt (R_of_N N0) x) -> Rlt (R_of_N N0) (Rpow x (N.succ n)).
Axiom thm_POW_2_LE1 : forall n : N, Rle (R_of_N ((BIT1 N0))) (Rpow (R_of_N ((BIT0 (BIT1 N0)))) n).
Axiom thm_POW_2_LT : forall n : N, Rlt (R_of_N n) (Rpow (R_of_N ((BIT0 (BIT1 N0)))) n).
Axiom thm_POW_MINUS1 : forall n : N, (Rpow (Ropp (R_of_N ((BIT1 N0)))) (N.mul ((BIT0 (BIT1 N0))) n)) = (R_of_N ((BIT1 N0))).
Axiom thm_REAL_SUP_EXISTS : forall P : R -> Prop, ((exists x : R, P x) /\ (exists z : R, forall x : R, (P x) -> Rlt x z)) -> exists s : R, forall y : R, (exists x : R, (P x) /\ (Rlt y x)) = (Rlt y s).
Axiom thm_sup_def : forall s : R -> Prop, (sup s) = (@ε R (fun a : R => (forall x : R, (@IN R x s) -> Rle x a) /\ (forall b : R, (forall x : R, (@IN R x s) -> Rle x b) -> Rle a b))).
Axiom thm_sup : forall (P : R -> Prop), (sup P) = (@ε R (fun s : R => forall y : R, (exists x : R, (P x) /\ (Rlt y x)) = (Rlt y s))).
Axiom thm_REAL_SUP : forall P : R -> Prop, ((exists x : R, P x) /\ (exists z : R, forall x : R, (P x) -> Rlt x z)) -> forall y : R, (exists x : R, (P x) /\ (Rlt y x)) = (Rlt y (sup P)).
Axiom thm_REAL_SUP_UBOUND : forall P : R -> Prop, ((exists x : R, P x) /\ (exists z : R, forall x : R, (P x) -> Rlt x z)) -> forall y : R, (P y) -> Rle y (sup P).
Axiom thm_SETOK_LE_LT : forall P : R -> Prop, ((exists x : R, P x) /\ (exists z : R, forall x : R, (P x) -> Rle x z)) = ((exists x : R, P x) /\ (exists z : R, forall x : R, (P x) -> Rlt x z)).
Axiom thm_REAL_SUP_LE : forall P : R -> Prop, ((exists x : R, P x) /\ (exists z : R, forall x : R, (P x) -> Rle x z)) -> forall y : R, (exists x : R, (P x) /\ (Rlt y x)) = (Rlt y (sup P)).
Axiom thm_REAL_SUP_UBOUND_LE : forall P : R -> Prop, ((exists x : R, P x) /\ (exists z : R, forall x : R, (P x) -> Rle x z)) -> forall y : R, (P y) -> Rle y (sup P).
Axiom thm_REAL_ARCH_SIMPLE : forall x : R, exists n : N, Rle x (R_of_N n).
Axiom thm_REAL_ARCH : forall x : R, (Rlt (R_of_N N0) x) -> forall y : R, exists n : N, Rlt y (Rmult (R_of_N n) x).
Axiom thm_REAL_ARCH_LEAST : forall y : R, (Rlt (R_of_N N0) y) -> forall x : R, (Rle (R_of_N N0) x) -> exists n : N, (Rle (Rmult (R_of_N n) y) x) /\ (Rlt x (Rmult (R_of_N (N.succ n)) y)).
Axiom thm_REAL_POW_LBOUND : forall x : R, forall n : N, (Rle (R_of_N N0) x) -> Rle (Rplus (R_of_N ((BIT1 N0))) (Rmult (R_of_N n) x)) (Rpow (Rplus (R_of_N ((BIT1 N0))) x) n).
Axiom thm_REAL_ARCH_POW : forall x : R, forall y : R, (Rlt (R_of_N ((BIT1 N0))) x) -> exists n : N, Rlt y (Rpow x n).
Axiom thm_REAL_ARCH_POW2 : forall x : R, exists n : N, Rlt x (Rpow (R_of_N ((BIT0 (BIT1 N0)))) n).
Axiom thm_sum_EXISTS : exists sum' : (prod N N) -> (N -> R) -> R, (forall f : N -> R, forall n : N, (sum' (@pair N N n N0) f) = (R_of_N N0)) /\ (forall f : N -> R, forall m : N, forall n : N, (sum' (@pair N N n (N.succ m)) f) = (Rplus (sum' (@pair N N n m) f) (f (N.add n m)))).
Axiom thm_sum : forall (f : N -> R) (n : N) (m : N), ((psum (@pair N N n N0) f) = (R_of_N N0)) /\ ((psum (@pair N N n (N.succ m)) f) = (Rplus (psum (@pair N N n m) f) (f (N.add n m)))).
Axiom thm_PSUM_SUM : forall f : N -> R, forall m : N, forall n : N, (psum (@pair N N m n) f) = (@sum N (@GSPEC N (fun GEN_PVAR_376 : N => exists i : N, @SETSPEC N GEN_PVAR_376 ((N.le m i) /\ (N.lt i (N.add m n))) i)) f).
Axiom thm_PSUM_SUM_NUMSEG : forall f : N -> R, forall m : N, forall n : N, (~ ((m = N0) /\ (n = N0))) -> (psum (@pair N N m n) f) = (@sum N (Ninterval m (N.sub (N.add m n) ((BIT1 N0)))) f).
Axiom thm_SUM_TWO : forall f : N -> R, forall n : N, forall p : N, (Rplus (psum (@pair N N N0 n) f) (psum (@pair N N n p) f)) = (psum (@pair N N N0 (N.add n p)) f).
Axiom thm_SUM_DIFF : forall f : N -> R, forall m : N, forall n : N, (psum (@pair N N m n) f) = (Rminus (psum (@pair N N N0 (N.add m n)) f) (psum (@pair N N N0 m) f)).
Axiom thm_ABS_SUM : forall f : N -> R, forall m : N, forall n : N, Rle (Rabs (psum (@pair N N m n) f)) (psum (@pair N N m n) (fun n' : N => Rabs (f n'))).
Axiom thm_SUM_LE : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (forall r : N, ((N.le m r) /\ (N.lt r (N.add n m))) -> Rle (f r) (g r)) -> Rle (psum (@pair N N m n) f) (psum (@pair N N m n) g).
Axiom thm_SUM_EQ : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (forall r : N, ((N.le m r) /\ (N.lt r (N.add n m))) -> (f r) = (g r)) -> (psum (@pair N N m n) f) = (psum (@pair N N m n) g).
Axiom thm_SUM_POS : forall f : N -> R, (forall n : N, Rle (R_of_N N0) (f n)) -> forall m : N, forall n : N, Rle (R_of_N N0) (psum (@pair N N m n) f).
Axiom thm_SUM_POS_GEN : forall f : N -> R, forall m : N, forall n : N, (forall n' : N, (N.le m n') -> Rle (R_of_N N0) (f n')) -> Rle (R_of_N N0) (psum (@pair N N m n) f).
Axiom thm_SUM_ABS : forall f : N -> R, forall m : N, forall n : N, (Rabs (psum (@pair N N m n) (fun m' : N => Rabs (f m')))) = (psum (@pair N N m n) (fun m' : N => Rabs (f m'))).
Axiom thm_SUM_ABS_LE : forall f : N -> R, forall m : N, forall n : N, Rle (Rabs (psum (@pair N N m n) f)) (psum (@pair N N m n) (fun n' : N => Rabs (f n'))).
Axiom thm_SUM_ZERO : forall f : N -> R, forall N' : N, (forall n : N, (N.ge n N') -> (f n) = (R_of_N N0)) -> forall m : N, forall n : N, (N.ge m N') -> (psum (@pair N N m n) f) = (R_of_N N0).
Axiom thm_SUM_ADD : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (psum (@pair N N m n) (fun n' : N => Rplus (f n') (g n'))) = (Rplus (psum (@pair N N m n) f) (psum (@pair N N m n) g)).
Axiom thm_SUM_CMUL : forall f : N -> R, forall c : R, forall m : N, forall n : N, (psum (@pair N N m n) (fun n' : N => Rmult c (f n'))) = (Rmult c (psum (@pair N N m n) f)).
Axiom thm_SUM_NEG : forall f : N -> R, forall n : N, forall d : N, (psum (@pair N N n d) (fun n' : N => Ropp (f n'))) = (Ropp (psum (@pair N N n d) f)).
Axiom thm_SUM_SUB : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (psum (@pair N N m n) (fun n' : N => Rminus (f n') (g n'))) = (Rminus (psum (@pair N N m n) f) (psum (@pair N N m n) g)).
Axiom thm_SUM_SUBST : forall f : N -> R, forall g : N -> R, forall m : N, forall n : N, (forall p : N, ((N.le m p) /\ (N.lt p (N.add m n))) -> (f p) = (g p)) -> (psum (@pair N N m n) f) = (psum (@pair N N m n) g).
Axiom thm_SUM_NSUB : forall n : N, forall f : N -> R, forall c : R, (Rminus (psum (@pair N N N0 n) f) (Rmult (R_of_N n) c)) = (psum (@pair N N N0 n) (fun p : N => Rminus (f p) c)).
Axiom thm_SUM_BOUND : forall f : N -> R, forall K : R, forall m : N, forall n : N, (forall p : N, ((N.le m p) /\ (N.lt p (N.add m n))) -> Rle (f p) K) -> Rle (psum (@pair N N m n) f) (Rmult (R_of_N n) K).
Axiom thm_SUM_GROUP : forall n : N, forall k : N, forall f : N -> R, (psum (@pair N N N0 n) (fun m : N => psum (@pair N N (N.mul m k) k) f)) = (psum (@pair N N N0 (N.mul n k)) f).
Axiom thm_SUM_1 : forall f : N -> R, forall n : N, (psum (@pair N N n ((BIT1 N0))) f) = (f n).
Axiom thm_SUM_2 : forall f : N -> R, forall n : N, (psum (@pair N N n ((BIT0 (BIT1 N0)))) f) = (Rplus (f n) (f (N.add n ((BIT1 N0))))).
Axiom thm_SUM_OFFSET : forall f : N -> R, forall n : N, forall k : N, (psum (@pair N N N0 n) (fun m : N => f (N.add m k))) = (Rminus (psum (@pair N N N0 (N.add n k)) f) (psum (@pair N N N0 k) f)).
Axiom thm_SUM_REINDEX : forall f : N -> R, forall m : N, forall k : N, forall n : N, (psum (@pair N N (N.add m k) n) f) = (psum (@pair N N m n) (fun r : N => f (N.add r k))).
Axiom thm_SUM_0 : forall m : N, forall n : N, (psum (@pair N N m n) (fun r : N => R_of_N N0)) = (R_of_N N0).
Axiom thm_SUM_CANCEL : forall f : N -> R, forall n : N, forall d : N, (psum (@pair N N n d) (fun n' : N => Rminus (f (N.succ n')) (f n'))) = (Rminus (f (N.add n d)) (f n)).
Axiom thm_SUM_HORNER : forall f : N -> R, forall n : N, forall x : R, (psum (@pair N N N0 (N.succ n)) (fun i : N => Rmult (f i) (Rpow x i))) = (Rplus (f N0) (Rmult x (psum (@pair N N N0 n) (fun i : N => Rmult (f (N.succ i)) (Rpow x i))))).
Axiom thm_SUM_CONST : forall c : R, forall n : N, (psum (@pair N N N0 n) (fun m : N => c)) = (Rmult (R_of_N n) c).
Axiom thm_SUM_SPLIT : forall (m : N), forall f : N -> R, forall n : N, forall p : N, (Rplus (psum (@pair N N m n) f) (psum (@pair N N (N.add m n) p) f)) = (psum (@pair N N m (N.add n p)) f).
Axiom thm_SUM_SWAP : forall f : N -> N -> R, forall m1 : N, forall n1 : N, forall m2 : N, forall n2 : N, (psum (@pair N N m1 n1) (fun a : N => psum (@pair N N m2 n2) (fun b : N => f a b))) = (psum (@pair N N m2 n2) (fun b : N => psum (@pair N N m1 n1) (fun a : N => f a b))).
Axiom thm_SUM_EQ_0 : forall (m : N) (n : N) (f : N -> R), (forall r : N, ((N.le m r) /\ (N.lt r (N.add m n))) -> (f r) = (R_of_N N0)) -> (psum (@pair N N m n) f) = (R_of_N N0).
Axiom thm_SUM_MORETERMS_EQ : forall (f : N -> R), forall m : N, forall n : N, forall p : N, ((N.le n p) /\ (forall r : N, ((N.le (N.add m n) r) /\ (N.lt r (N.add m p))) -> (f r) = (R_of_N N0))) -> (psum (@pair N N m p) f) = (psum (@pair N N m n) f).
Axiom thm_SUM_DIFFERENCES_EQ : forall (f : N -> R) (g : N -> R), forall m : N, forall n : N, forall p : N, ((N.le n p) /\ (forall r : N, ((N.le (N.add m n) r) /\ (N.lt r (N.add m p))) -> (f r) = (g r))) -> (Rminus (psum (@pair N N m p) f) (psum (@pair N N m n) f)) = (Rminus (psum (@pair N N m p) g) (psum (@pair N N m n) g)).
Axiom thm_re_Union : forall {A : Type'}, forall S' : (A -> Prop) -> Prop, (@re_Union A S') = (fun x : A => exists s : A -> Prop, (S' s) /\ (s x)).
Axiom thm_re_union : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (@re_union A P Q) = (fun x : A => (P x) \/ (Q x)).
Axiom thm_re_intersect : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (@re_intersect A P Q) = (fun x : A => (P x) /\ (Q x)).
Axiom thm_re_null : forall {A : Type'}, (@re_null A) = (fun x : A => False).
Axiom thm_re_universe : forall {A : Type'}, (@re_universe A) = (fun x : A => True).
Axiom thm_re_subset : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (@re_subset A P Q) = (forall x : A, (P x) -> Q x).
Axiom thm_re_compl : forall {A : Type'}, forall S' : A -> Prop, (@re_compl A S') = (fun x : A => ~ (S' x)).
Axiom thm_SUBSETA_REFL : forall {A : Type'}, forall S' : A -> Prop, @re_subset A S' S'.
Axiom thm_COMPL_MEM : forall {A : Type'}, forall S' : A -> Prop, forall x : A, (S' x) = (~ (@re_compl A S' x)).
Axiom thm_SUBSETA_ANTISYM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, ((@re_subset A P Q) /\ (@re_subset A Q P)) = (P = Q).
Axiom thm_SUBSETA_TRANS : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall R' : A -> Prop, ((@re_subset A P Q) /\ (@re_subset A Q R')) -> @re_subset A P R'.
Axiom thm_istopology : forall {A : Type'}, forall L : (A -> Prop) -> Prop, (@istopology A L) = ((L (@re_null A)) /\ ((L (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((L a) /\ (L b)) -> L (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P L) -> L (@re_Union A P))))).
Axiom thm_TOPOLOGY : forall {A : Type'}, forall L : Topology A, (@open A L (@re_null A)) /\ ((@open A L (@re_universe A)) /\ ((forall x : A -> Prop, forall y : A -> Prop, ((@open A L x) /\ (@open A L y)) -> @open A L (@re_intersect A x y)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P (@open A L)) -> @open A L (@re_Union A P)))).
Axiom thm_TOPOLOGY_UNION : forall {A : Type'}, forall L : Topology A, forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P (@open A L)) -> @open A L (@re_Union A P).
Axiom thm_neigh : forall {A : Type'}, forall top : Topology A, forall N' : A -> Prop, forall x : A, (@neigh A top (@pair (A -> Prop) A N' x)) = (exists P : A -> Prop, (@open A top P) /\ ((@re_subset A P N') /\ (P x))).
Axiom thm_OPEN_OWN_NEIGH : forall {A : Type'}, forall S' : A -> Prop, forall top : Topology A, forall x : A, ((@open A top S') /\ (S' x)) -> @neigh A top (@pair (A -> Prop) A S' x).
Axiom thm_OPEN_UNOPEN : forall {A : Type'}, forall S' : A -> Prop, forall top : Topology A, (@open A top S') = ((@re_Union A (fun P : A -> Prop => (@open A top P) /\ (@re_subset A P S'))) = S').
Axiom thm_OPEN_SUBOPEN : forall {A : Type'}, forall S' : A -> Prop, forall top : Topology A, (@open A top S') = (forall x : A, (S' x) -> exists P : A -> Prop, (P x) /\ ((@open A top P) /\ (@re_subset A P S'))).
Axiom thm_OPEN_NEIGH : forall {A : Type'}, forall S' : A -> Prop, forall top : Topology A, (@open A top S') = (forall x : A, (S' x) -> exists N' : A -> Prop, (@neigh A top (@pair (A -> Prop) A N' x)) /\ (@re_subset A N' S')).
Axiom thm_closed : forall {A : Type'}, forall L : Topology A, forall S' : A -> Prop, (@closed A L S') = (@open A L (@re_compl A S')).
Axiom thm_limpt : forall {A : Type'}, forall top : Topology A, forall x : A, forall S' : A -> Prop, (@limpt A top x S') = (forall N' : A -> Prop, (@neigh A top (@pair (A -> Prop) A N' x)) -> exists y : A, (~ (x = y)) /\ ((S' y) /\ (N' y))).
Axiom thm_CLOSED_LIMPT : forall {A : Type'}, forall top : Topology A, forall S' : A -> Prop, (@closed A top S') = (forall x : A, (@limpt A top x S') -> S' x).
Axiom thm_ismet : forall {A : Type'}, forall m : (prod A A) -> R, (@ismet A m) = ((forall x : A, forall y : A, ((m (@pair A A x y)) = (R_of_N N0)) = (x = y)) /\ (forall x : A, forall y : A, forall z : A, Rle (m (@pair A A y z)) (Rplus (m (@pair A A x y)) (m (@pair A A x z))))).
Axiom thm_METRIC_ISMET : forall {A : Type'}, forall m : Metric A, @ismet A (@mdist A m).
Axiom thm_METRIC_ZERO : forall {A : Type'}, forall m : Metric A, forall x : A, forall y : A, ((@mdist A m (@pair A A x y)) = (R_of_N N0)) = (x = y).
Axiom thm_METRIC_SAME : forall {A : Type'}, forall m : Metric A, forall x : A, (@mdist A m (@pair A A x x)) = (R_of_N N0).
Axiom thm_METRIC_POS : forall {A : Type'}, forall m : Metric A, forall x : A, forall y : A, Rle (R_of_N N0) (@mdist A m (@pair A A x y)).
Axiom thm_METRIC_SYM : forall {A : Type'}, forall m : Metric A, forall x : A, forall y : A, (@mdist A m (@pair A A x y)) = (@mdist A m (@pair A A y x)).
Axiom thm_METRIC_TRIANGLE : forall {A : Type'}, forall m : Metric A, forall x : A, forall y : A, forall z : A, Rle (@mdist A m (@pair A A x z)) (Rplus (@mdist A m (@pair A A x y)) (@mdist A m (@pair A A y z))).
Axiom thm_METRIC_NZ : forall {A : Type'}, forall m : Metric A, forall x : A, forall y : A, (~ (x = y)) -> Rlt (R_of_N N0) (@mdist A m (@pair A A x y)).
Axiom thm_mtop : forall {A : Type'}, forall m : Metric A, (@mtop A m) = (@topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N N0) e) /\ (forall y : A, (Rlt (@mdist A m (@pair A A x y)) e) -> S' y))).
Axiom thm_mtop_istopology : forall {A : Type'}, forall m : Metric A, @istopology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N N0) e) /\ (forall y : A, (Rlt (@mdist A m (@pair A A x y)) e) -> S' y)).
Axiom thm_MTOP_OPEN : forall {A : Type'} (S' : A -> Prop), forall m : Metric A, (@open A (@mtop A m) S') = (forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N N0) e) /\ (forall y : A, (Rlt (@mdist A m (@pair A A x y)) e) -> S' y)).
Axiom thm_ball : forall {A : Type'}, forall m : Metric A, forall x : A, forall e : R, (@ball A m (@pair A R x e)) = (fun y : A => Rlt (@mdist A m (@pair A A x y)) e).
Axiom thm_BALL_OPEN : forall {A : Type'}, forall m : Metric A, forall x : A, forall e : R, (Rlt (R_of_N N0) e) -> @open A (@mtop A m) (@ball A m (@pair A R x e)).
Axiom thm_BALL_NEIGH : forall {A : Type'}, forall m : Metric A, forall x : A, forall e : R, (Rlt (R_of_N N0) e) -> @neigh A (@mtop A m) (@pair (A -> Prop) A (@ball A m (@pair A R x e)) x).
Axiom thm_MTOP_LIMPT : forall {A : Type'}, forall m : Metric A, forall x : A, forall S' : A -> Prop, (@limpt A (@mtop A m) x S') = (forall e : R, (Rlt (R_of_N N0) e) -> exists y : A, (~ (x = y)) /\ ((S' y) /\ (Rlt (@mdist A m (@pair A A x y)) e))).
Axiom thm_ISMET_R1 : @ismet R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x)))).
Axiom thm_mr1 : mr1 = (@metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x))))).
Axiom thm_MR1_DEF : forall x : R, forall y : R, (@mdist R mr1 (@pair R R x y)) = (Rabs (Rminus y x)).
Axiom thm_MR1_ADD : forall x : R, forall d : R, (@mdist R mr1 (@pair R R x (Rplus x d))) = (Rabs d).
Axiom thm_MR1_SUB : forall x : R, forall d : R, (@mdist R mr1 (@pair R R x (Rminus x d))) = (Rabs d).
Axiom thm_MR1_ADD_LE : forall x : R, forall d : R, (Rle (R_of_N N0) d) -> (@mdist R mr1 (@pair R R x (Rplus x d))) = d.
Axiom thm_MR1_SUB_LE : forall x : R, forall d : R, (Rle (R_of_N N0) d) -> (@mdist R mr1 (@pair R R x (Rminus x d))) = d.
Axiom thm_MR1_ADD_LT : forall x : R, forall d : R, (Rlt (R_of_N N0) d) -> (@mdist R mr1 (@pair R R x (Rplus x d))) = d.
Axiom thm_MR1_SUB_LT : forall x : R, forall d : R, (Rlt (R_of_N N0) d) -> (@mdist R mr1 (@pair R R x (Rminus x d))) = d.
Axiom thm_MR1_BETWEEN1 : forall x : R, forall y : R, forall z : R, ((Rlt x z) /\ (Rlt (@mdist R mr1 (@pair R R x y)) (Rminus z x))) -> Rlt y z.
Axiom thm_MR1_LIMPT : forall x : R, @limpt R (@mtop R mr1) x (@re_universe R).
Axiom thm_dorder : forall {A : Type'}, forall g : A -> A -> Prop, (@dorder A g) = (forall x : A, forall y : A, ((g x x) /\ (g y y)) -> exists z : A, (g z z) /\ (forall w : A, (g w z) -> (g w x) /\ (g w y))).
Axiom thm_tends : forall {A B : Type'}, forall top : Topology A, forall l : A, forall g : B -> B -> Prop, forall s : B -> A, (@tends A B s l (@pair (Topology A) (B -> B -> Prop) top g)) = (forall N' : A -> Prop, (@neigh A top (@pair (A -> Prop) A N' l)) -> exists n : B, (g n n) /\ (forall m : B, (g m n) -> N' (s m))).
Axiom thm_bounded : forall {A B : Type'}, forall g : B -> B -> Prop, forall m : Metric A, forall f : B -> A, (@bounded A B (@pair (Metric A) (B -> B -> Prop) m g) f) = (exists k : R, exists x : A, exists N' : B, (g N' N') /\ (forall n : B, (g n N') -> Rlt (@mdist A m (@pair A A (f n) x)) k)).
Axiom thm_tendsto : forall {A : Type'}, forall y : A, forall m : Metric A, forall x : A, forall z : A, (@tendsto A (@pair (Metric A) A m x) y z) = ((Rlt (R_of_N N0) (@mdist A m (@pair A A x y))) /\ (Rle (@mdist A m (@pair A A x y)) (@mdist A m (@pair A A x z)))).
Axiom thm_DORDER_LEMMA : forall {A : Type'}, forall g : A -> A -> Prop, (@dorder A g) -> forall P : A -> Prop, forall Q : A -> Prop, ((exists n : A, (g n n) /\ (forall m : A, (g m n) -> P m)) /\ (exists n : A, (g n n) /\ (forall m : A, (g m n) -> Q m))) -> exists n : A, (g n n) /\ (forall m : A, (g m n) -> (P m) /\ (Q m)).
Axiom thm_DORDER_NGE : @dorder N N.ge.
Axiom thm_DORDER_TENDSTO : forall {A : Type'}, forall m : Metric A, forall x : A, @dorder A (@tendsto A (@pair (Metric A) A m x)).
Axiom thm_MTOP_TENDS : forall {A B : Type'}, forall d : Metric A, forall g : B -> B -> Prop, forall x : B -> A, forall x0 : A, (@tends A B x x0 (@pair (Topology A) (B -> B -> Prop) (@mtop A d) g)) = (forall e : R, (Rlt (R_of_N N0) e) -> exists n : B, (g n n) /\ (forall m : B, (g m n) -> Rlt (@mdist A d (@pair A A (x m) x0)) e)).
Axiom thm_MTOP_TENDS_UNIQ : forall {A B : Type'} (x : B -> A) (x0 : A) (x1 : A), forall g : B -> B -> Prop, forall d : Metric A, (@dorder B g) -> ((@tends A B x x0 (@pair (Topology A) (B -> B -> Prop) (@mtop A d) g)) /\ (@tends A B x x1 (@pair (Topology A) (B -> B -> Prop) (@mtop A d) g))) -> x0 = x1.
Axiom thm_SEQ_TENDS : forall {A : Type'}, forall d : Metric A, forall x : N -> A, forall x0 : A, (@tends A N x x0 (@pair (Topology A) (N -> N -> Prop) (@mtop A d) N.ge)) = (forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, forall n : N, (N.ge n N') -> Rlt (@mdist A d (@pair A A (x n) x0)) e).
Axiom thm_LIM_TENDS : forall {A B : Type'}, forall m1 : Metric A, forall m2 : Metric B, forall f : A -> B, forall x0 : A, forall y0 : B, (@limpt A (@mtop A m1) x0 (@re_universe A)) -> (@tends B A f y0 (@pair (Topology B) (A -> A -> Prop) (@mtop B m2) (@tendsto A (@pair (Metric A) A m1 x0)))) = (forall e : R, (Rlt (R_of_N N0) e) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall x : A, ((Rlt (R_of_N N0) (@mdist A m1 (@pair A A x x0))) /\ (Rle (@mdist A m1 (@pair A A x x0)) d)) -> Rlt (@mdist B m2 (@pair B B (f x) y0)) e)).
Axiom thm_LIM_TENDS2 : forall {A B : Type'}, forall m1 : Metric A, forall m2 : Metric B, forall f : A -> B, forall x0 : A, forall y0 : B, (@limpt A (@mtop A m1) x0 (@re_universe A)) -> (@tends B A f y0 (@pair (Topology B) (A -> A -> Prop) (@mtop B m2) (@tendsto A (@pair (Metric A) A m1 x0)))) = (forall e : R, (Rlt (R_of_N N0) e) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall x : A, ((Rlt (R_of_N N0) (@mdist A m1 (@pair A A x x0))) /\ (Rlt (@mdist A m1 (@pair A A x x0)) d)) -> Rlt (@mdist B m2 (@pair B B (f x) y0)) e)).
Axiom thm_MR1_BOUNDED : forall {A : Type'}, forall g : A -> A -> Prop, forall f : A -> R, (@bounded R A (@pair (Metric R) (A -> A -> Prop) mr1 g) f) = (exists k : R, exists N' : A, (g N' N') /\ (forall n : A, (g n N') -> Rlt (Rabs (f n)) k)).
Axiom thm_NET_NULL : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, (@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) = (@tends R A (fun n : A => Rminus (x n) x0) (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)).
Axiom thm_NET_CONV_BOUNDED : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, (@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) -> @bounded R A (@pair (Metric R) (A -> A -> Prop) mr1 g) x.
Axiom thm_NET_CONV_NZ : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (~ (x0 = (R_of_N N0)))) -> exists N' : A, (g N' N') /\ (forall n : A, (g n N') -> ~ ((x n) = (R_of_N N0))).
Axiom thm_NET_CONV_IBOUNDED : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (~ (x0 = (R_of_N N0)))) -> @bounded R A (@pair (Metric R) (A -> A -> Prop) mr1 g) (fun n : A => Rinv (x n)).
Axiom thm_NET_NULL_ADD : forall {A : Type'}, forall g : A -> A -> Prop, (@dorder A g) -> forall x : A -> R, forall y : A -> R, ((@tends R A x (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (@tends R A y (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g))) -> @tends R A (fun n : A => Rplus (x n) (y n)) (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_NULL_MUL : forall {A : Type'}, forall g : A -> A -> Prop, (@dorder A g) -> forall x : A -> R, forall y : A -> R, ((@bounded R A (@pair (Metric R) (A -> A -> Prop) mr1 g) x) /\ (@tends R A y (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g))) -> @tends R A (fun n : A => Rmult (x n) (y n)) (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_NULL_CMUL : forall {A : Type'}, forall g : A -> A -> Prop, forall k : R, forall x : A -> R, (@tends R A x (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) -> @tends R A (fun n : A => Rmult k (x n)) (R_of_N N0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_ADD : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, forall y : A -> R, forall y0 : R, (@dorder A g) -> ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (@tends R A y y0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g))) -> @tends R A (fun n : A => Rplus (x n) (y n)) (Rplus x0 y0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_NEG : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, (@dorder A g) -> (@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) = (@tends R A (fun n : A => Ropp (x n)) (Ropp x0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)).
Axiom thm_NET_SUB : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, forall y : A -> R, forall y0 : R, (@dorder A g) -> ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (@tends R A y y0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g))) -> @tends R A (fun n : A => Rminus (x n) (y n)) (Rminus x0 y0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_MUL : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall y : A -> R, forall x0 : R, forall y0 : R, (@dorder A g) -> ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (@tends R A y y0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g))) -> @tends R A (fun n : A => Rmult (x n) (y n)) (Rmult x0 y0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_INV : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, (@dorder A g) -> ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (~ (x0 = (R_of_N N0)))) -> @tends R A (fun n : A => Rinv (x n)) (Rinv x0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_DIV : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, forall y : A -> R, forall y0 : R, (@dorder A g) -> ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ ((@tends R A y y0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (~ (y0 = (R_of_N N0))))) -> @tends R A (fun n : A => Rdiv (x n) (y n)) (Rdiv x0 y0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_ABS : forall {A : Type'} (g : A -> A -> Prop), forall x : A -> R, forall x0 : R, (@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) -> @tends R A (fun n : A => Rabs (x n)) (Rabs x0) (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g).
Axiom thm_NET_SUM : forall {_154662 : Type'} (f : N -> _154662 -> R) (l : N -> R), forall g : _154662 -> _154662 -> Prop, ((@dorder _154662 g) /\ (@tends R _154662 (fun x : _154662 => R_of_N N0) (R_of_N N0) (@pair (Topology R) (_154662 -> _154662 -> Prop) (@mtop R mr1) g))) -> forall m : N, forall n : N, (forall r : N, ((N.le m r) /\ (N.lt r (N.add m n))) -> @tends R _154662 (f r) (l r) (@pair (Topology R) (_154662 -> _154662 -> Prop) (@mtop R mr1) g)) -> @tends R _154662 (fun x : _154662 => psum (@pair N N m n) (fun r : N => f r x)) (psum (@pair N N m n) l) (@pair (Topology R) (_154662 -> _154662 -> Prop) (@mtop R mr1) g).
Axiom thm_NET_LE : forall {A : Type'}, forall g : A -> A -> Prop, forall x : A -> R, forall x0 : R, forall y : A -> R, forall y0 : R, (@dorder A g) -> ((@tends R A x x0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ ((@tends R A y y0 (@pair (Topology R) (A -> A -> Prop) (@mtop R mr1) g)) /\ (exists N' : A, (g N' N') /\ (forall n : A, (g n N') -> Rle (x n) (y n))))) -> Rle x0 y0.
Axiom thm_tends_num_real : forall x : N -> R, forall x0 : R, (tends_num_real x x0) = (@tends R N x x0 (@pair (Topology R) (N -> N -> Prop) (@mtop R mr1) N.ge)).
Axiom thm_SEQ : forall x : N -> R, forall x0 : R, (tends_num_real x x0) = (forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, forall n : N, (N.ge n N') -> Rlt (Rabs (Rminus (x n) x0)) e).
Axiom thm_SEQ_CONST : forall k : R, tends_num_real (fun x : N => k) k.
Axiom thm_SEQ_ADD : forall x : N -> R, forall x0 : R, forall y : N -> R, forall y0 : R, ((tends_num_real x x0) /\ (tends_num_real y y0)) -> tends_num_real (fun n : N => Rplus (x n) (y n)) (Rplus x0 y0).
Axiom thm_SEQ_MUL : forall x : N -> R, forall x0 : R, forall y : N -> R, forall y0 : R, ((tends_num_real x x0) /\ (tends_num_real y y0)) -> tends_num_real (fun n : N => Rmult (x n) (y n)) (Rmult x0 y0).
Axiom thm_SEQ_NEG : forall x : N -> R, forall x0 : R, (tends_num_real x x0) = (tends_num_real (fun n : N => Ropp (x n)) (Ropp x0)).
Axiom thm_SEQ_INV : forall x : N -> R, forall x0 : R, ((tends_num_real x x0) /\ (~ (x0 = (R_of_N N0)))) -> tends_num_real (fun n : N => Rinv (x n)) (Rinv x0).
Axiom thm_SEQ_SUB : forall x : N -> R, forall x0 : R, forall y : N -> R, forall y0 : R, ((tends_num_real x x0) /\ (tends_num_real y y0)) -> tends_num_real (fun n : N => Rminus (x n) (y n)) (Rminus x0 y0).
Axiom thm_SEQ_DIV : forall x : N -> R, forall x0 : R, forall y : N -> R, forall y0 : R, ((tends_num_real x x0) /\ ((tends_num_real y y0) /\ (~ (y0 = (R_of_N N0))))) -> tends_num_real (fun n : N => Rdiv (x n) (y n)) (Rdiv x0 y0).
Axiom thm_SEQ_UNIQ : forall x : N -> R, forall x1 : R, forall x2 : R, ((tends_num_real x x1) /\ (tends_num_real x x2)) -> x1 = x2.
Axiom thm_SEQ_NULL : forall s : N -> R, forall l : R, (tends_num_real s l) = (tends_num_real (fun n : N => Rminus (s n) l) (R_of_N N0)).
Axiom thm_SEQ_SUM : forall f : N -> N -> R, forall l : N -> R, forall m : N, forall n : N, (forall r : N, ((N.le m r) /\ (N.lt r (N.add m n))) -> tends_num_real (f r) (l r)) -> tends_num_real (fun k : N => psum (@pair N N m n) (fun r : N => f r k)) (psum (@pair N N m n) l).
Axiom thm_SEQ_TRANSFORM : forall s : N -> R, forall t : N -> R, forall l : R, forall N' : N, ((forall n : N, (N.le N' n) -> (s n) = (t n)) /\ (tends_num_real s l)) -> tends_num_real t l.
Axiom thm_convergent : forall f : N -> R, (convergent f) = (exists l : R, tends_num_real f l).
Axiom thm_cauchy : forall f : N -> R, (cauchy f) = (forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, forall m : N, forall n : N, ((N.ge m N') /\ (N.ge n N')) -> Rlt (Rabs (Rminus (f m) (f n))) e).
Axiom thm_lim : forall f : N -> R, (lim f) = (@ε R (fun l : R => tends_num_real f l)).
Axiom thm_SEQ_LIM : forall f : N -> R, (convergent f) = (tends_num_real f (lim f)).
Axiom thm_subseq : forall f : N -> N, (subseq f) = (forall m : N, forall n : N, (N.lt m n) -> N.lt (f m) (f n)).
Axiom thm_SUBSEQ_SUC : forall f : N -> N, (subseq f) = (forall n : N, N.lt (f n) (f (N.succ n))).
Axiom thm_mono : forall f : N -> R, (mono f) = ((forall m : N, forall n : N, (N.le m n) -> Rle (f m) (f n)) \/ (forall m : N, forall n : N, (N.le m n) -> Rge (f m) (f n))).
Axiom thm_MONO_SUC : forall f : N -> R, (mono f) = ((forall n : N, Rge (f (N.succ n)) (f n)) \/ (forall n : N, Rle (f (N.succ n)) (f n))).
Axiom thm_MAX_LEMMA : forall s : N -> R, forall N' : N, exists k : R, forall n : N, (N.lt n N') -> Rlt (Rabs (s n)) k.
Axiom thm_SEQ_BOUNDED : forall s : N -> R, (@bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) s) = (exists k : R, forall n : N, Rlt (Rabs (s n)) k).
Axiom thm_SEQ_BOUNDED_2 : forall f : N -> R, forall k : R, forall K : R, (forall n : N, (Rle k (f n)) /\ (Rle (f n) K)) -> @bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) f.
Axiom thm_SEQ_CBOUNDED : forall f : N -> R, (cauchy f) -> @bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) f.
Axiom thm_SEQ_ICONV : forall f : N -> R, ((@bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) f) /\ (forall m : N, forall n : N, (N.ge m n) -> Rge (f m) (f n))) -> convergent f.
Axiom thm_SEQ_NEG_CONV : forall f : N -> R, (convergent f) = (convergent (fun n : N => Ropp (f n))).
Axiom thm_SEQ_NEG_BOUNDED : forall f : N -> R, (@bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) (fun n : N => Ropp (f n))) = (@bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) f).
Axiom thm_SEQ_BCONV : forall f : N -> R, ((@bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) f) /\ (mono f)) -> convergent f.
Axiom thm_SEQ_MONOSUB : forall s : N -> R, exists f : N -> N, (subseq f) /\ (mono (fun n : N => s (f n))).
Axiom thm_SEQ_SBOUNDED : forall s : N -> R, forall f : N -> N, (@bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) s) -> @bounded R N (@pair (Metric R) (N -> N -> Prop) mr1 N.ge) (fun n : N => s (f n)).
Axiom thm_SEQ_SUBLE : forall f : N -> N, forall n : N, (subseq f) -> N.le n (f n).
Axiom thm_SEQ_DIRECT : forall f : N -> N, (subseq f) -> forall N1 : N, forall N2 : N, exists n : N, (N.ge n N1) /\ (N.ge (f n) N2).
Axiom thm_SEQ_CAUCHY : forall f : N -> R, (cauchy f) = (convergent f).
Axiom thm_SEQ_LE : forall f : N -> R, forall g : N -> R, forall l : R, forall m : R, ((tends_num_real f l) /\ ((tends_num_real g m) /\ (exists N' : N, forall n : N, (N.ge n N') -> Rle (f n) (g n)))) -> Rle l m.
Axiom thm_SEQ_LE_0 : forall f : N -> R, forall g : N -> R, ((tends_num_real f (R_of_N N0)) /\ (exists N' : N, forall n : N, (N.ge n N') -> Rle (Rabs (g n)) (Rabs (f n)))) -> tends_num_real g (R_of_N N0).
Axiom thm_SEQ_SUC : forall f : N -> R, forall l : R, (tends_num_real f l) = (tends_num_real (fun n : N => f (N.succ n)) l).
Axiom thm_SEQ_ABS : forall f : N -> R, (tends_num_real (fun n : N => Rabs (f n)) (R_of_N N0)) = (tends_num_real f (R_of_N N0)).
Axiom thm_SEQ_ABS_IMP : forall f : N -> R, forall l : R, (tends_num_real f l) -> tends_num_real (fun n : N => Rabs (f n)) (Rabs l).
Axiom thm_SEQ_INV0 : forall f : N -> R, (forall y : R, exists N' : N, forall n : N, (N.ge n N') -> Rgt (f n) y) -> tends_num_real (fun n : N => Rinv (f n)) (R_of_N N0).
Axiom thm_SEQ_POWER_ABS : forall c : R, (Rlt (Rabs c) (R_of_N ((BIT1 N0)))) -> tends_num_real (fun n : N => Rpow (Rabs c) n) (R_of_N N0).
Axiom thm_SEQ_POWER : forall c : R, (Rlt (Rabs c) (R_of_N ((BIT1 N0)))) -> tends_num_real (fun n : N => Rpow c n) (R_of_N N0).
Axiom thm_SEQ_HARMONIC : forall a : R, tends_num_real (fun n : N => Rdiv a (R_of_N n)) (R_of_N N0).
Axiom thm_SEQ_SUBSEQ : forall f : N -> R, forall l : R, (tends_num_real f l) -> forall a : N, forall b : N, (~ (a = N0)) -> tends_num_real (fun n : N => f (N.add (N.mul a n) b)) l.
Axiom thm_SEQ_POW : forall f : N -> R, forall l : R, (tends_num_real f l) -> forall n : N, tends_num_real (fun i : N => Rpow (f i) n) (Rpow l n).
Axiom thm_NEST_LEMMA : forall f : N -> R, forall g : N -> R, ((forall n : N, Rge (f (N.succ n)) (f n)) /\ ((forall n : N, Rle (g (N.succ n)) (g n)) /\ (forall n : N, Rle (f n) (g n)))) -> exists l : R, exists m : R, (Rle l m) /\ (((forall n : N, Rle (f n) l) /\ (tends_num_real f l)) /\ ((forall n : N, Rle m (g n)) /\ (tends_num_real g m))).
Axiom thm_NEST_LEMMA_UNIQ : forall f : N -> R, forall g : N -> R, ((forall n : N, Rge (f (N.succ n)) (f n)) /\ ((forall n : N, Rle (g (N.succ n)) (g n)) /\ ((forall n : N, Rle (f n) (g n)) /\ (tends_num_real (fun n : N => Rminus (f n) (g n)) (R_of_N N0))))) -> exists l : R, ((forall n : N, Rle (f n) l) /\ (tends_num_real f l)) /\ ((forall n : N, Rle l (g n)) /\ (tends_num_real g l)).
Axiom thm_BOLZANO_LEMMA : forall P : (prod R R) -> Prop, ((forall a : R, forall b : R, forall c : R, ((Rle a b) /\ ((Rle b c) /\ ((P (@pair R R a b)) /\ (P (@pair R R b c))))) -> P (@pair R R a c)) /\ (forall x : R, exists d : R, (Rlt (R_of_N N0) d) /\ (forall a : R, forall b : R, ((Rle a x) /\ ((Rle x b) /\ (Rlt (Rminus b a) d))) -> P (@pair R R a b)))) -> forall a : R, forall b : R, (Rle a b) -> P (@pair R R a b).
Axiom thm_BOLZANO_LEMMA_ALT : forall P : R -> R -> Prop, ((forall a : R, forall b : R, forall c : R, ((Rle a b) /\ ((Rle b c) /\ ((P a b) /\ (P b c)))) -> P a c) /\ (forall x : R, exists d : R, (Rlt (R_of_N N0) d) /\ (forall a : R, forall b : R, ((Rle a x) /\ ((Rle x b) /\ (Rlt (Rminus b a) d))) -> P a b))) -> forall a : R, forall b : R, (Rle a b) -> P a b.
Axiom thm_sums : forall f : N -> R, forall s : R, (sums f s) = (tends_num_real (fun n : N => psum (@pair N N N0 n) f) s).
Axiom thm_summable : forall f : N -> R, (summable f) = (exists s : R, sums f s).
Axiom thm_suminf : forall f : N -> R, (suminf f) = (@ε R (fun s : R => sums f s)).
Axiom thm_SUM_SUMMABLE : forall f : N -> R, forall l : R, (sums f l) -> summable f.
Axiom thm_SUMMABLE_SUM : forall f : N -> R, (summable f) -> sums f (suminf f).
Axiom thm_SUM_UNIQ : forall f : N -> R, forall x : R, (sums f x) -> x = (suminf f).
Axiom thm_SER_UNIQ : forall f : N -> R, forall x : R, forall y : R, ((sums f x) /\ (sums f y)) -> x = y.
Axiom thm_SER_0 : forall f : N -> R, forall n : N, (forall m : N, (N.le n m) -> (f m) = (R_of_N N0)) -> sums f (psum (@pair N N N0 n) f).
Axiom thm_SER_POS_LE : forall f : N -> R, forall n : N, ((summable f) /\ (forall m : N, (N.le n m) -> Rle (R_of_N N0) (f m))) -> Rle (psum (@pair N N N0 n) f) (suminf f).
Axiom thm_SER_POS_LT : forall f : N -> R, forall n : N, ((summable f) /\ (forall m : N, (N.le n m) -> Rlt (R_of_N N0) (f m))) -> Rlt (psum (@pair N N N0 n) f) (suminf f).
Axiom thm_SER_GROUP : forall f : N -> R, forall k : N, ((summable f) /\ (N.lt N0 k)) -> sums (fun n : N => psum (@pair N N (N.mul n k) k) f) (suminf f).
Axiom thm_SER_PAIR : forall f : N -> R, (summable f) -> sums (fun n : N => psum (@pair N N (N.mul ((BIT0 (BIT1 N0))) n) ((BIT0 (BIT1 N0)))) f) (suminf f).
Axiom thm_SER_OFFSET : forall f : N -> R, (summable f) -> forall k : N, sums (fun n : N => f (N.add n k)) (Rminus (suminf f) (psum (@pair N N N0 k) f)).
Axiom thm_SER_OFFSET_REV : forall f : N -> R, forall k : N, (summable (fun n : N => f (N.add n k))) -> sums f (Rplus (psum (@pair N N N0 k) f) (suminf (fun n : N => f (N.add n k)))).
Axiom thm_SER_POS_LT_PAIR : forall f : N -> R, forall n : N, ((summable f) /\ (forall d : N, Rlt (R_of_N N0) (Rplus (f (N.add n (N.mul ((BIT0 (BIT1 N0))) d))) (f (N.add n (N.add (N.mul ((BIT0 (BIT1 N0))) d) ((BIT1 N0)))))))) -> Rlt (psum (@pair N N N0 n) f) (suminf f).
Axiom thm_SER_ADD : forall x : N -> R, forall x0 : R, forall y : N -> R, forall y0 : R, ((sums x x0) /\ (sums y y0)) -> sums (fun n : N => Rplus (x n) (y n)) (Rplus x0 y0).
Axiom thm_SER_CMUL : forall x : N -> R, forall x0 : R, forall c : R, (sums x x0) -> sums (fun n : N => Rmult c (x n)) (Rmult c x0).
Axiom thm_SER_NEG : forall x : N -> R, forall x0 : R, (sums x x0) -> sums (fun n : N => Ropp (x n)) (Ropp x0).
Axiom thm_SER_SUB : forall x : N -> R, forall x0 : R, forall y : N -> R, forall y0 : R, ((sums x x0) /\ (sums y y0)) -> sums (fun n : N => Rminus (x n) (y n)) (Rminus x0 y0).
Axiom thm_SER_CDIV : forall x : N -> R, forall x0 : R, forall c : R, (sums x x0) -> sums (fun n : N => Rdiv (x n) c) (Rdiv x0 c).
Axiom thm_SER_CAUCHY : forall f : N -> R, (summable f) = (forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, forall m : N, forall n : N, (N.ge m N') -> Rlt (Rabs (psum (@pair N N m n) f)) e).
Axiom thm_SER_ZERO : forall f : N -> R, (summable f) -> tends_num_real f (R_of_N N0).
Axiom thm_SER_COMPAR : forall f : N -> R, forall g : N -> R, ((exists N' : N, forall n : N, (N.ge n N') -> Rle (Rabs (f n)) (g n)) /\ (summable g)) -> summable f.
Axiom thm_SER_COMPARA : forall f : N -> R, forall g : N -> R, ((exists N' : N, forall n : N, (N.ge n N') -> Rle (Rabs (f n)) (g n)) /\ (summable g)) -> summable (fun k : N => Rabs (f k)).
Axiom thm_SER_LE : forall f : N -> R, forall g : N -> R, ((forall n : N, Rle (f n) (g n)) /\ ((summable f) /\ (summable g))) -> Rle (suminf f) (suminf g).
Axiom thm_SER_LE2 : forall f : N -> R, forall g : N -> R, ((forall n : N, Rle (Rabs (f n)) (g n)) /\ (summable g)) -> (summable f) /\ (Rle (suminf f) (suminf g)).
Axiom thm_SER_ACONV : forall f : N -> R, (summable (fun n : N => Rabs (f n))) -> summable f.
Axiom thm_SER_ABS : forall f : N -> R, (summable (fun n : N => Rabs (f n))) -> Rle (Rabs (suminf f)) (suminf (fun n : N => Rabs (f n))).
Axiom thm_GP_FINITE : forall x : R, (~ (x = (R_of_N ((BIT1 N0))))) -> forall n : N, (psum (@pair N N N0 n) (fun n' : N => Rpow x n')) = (Rdiv (Rminus (Rpow x n) (R_of_N ((BIT1 N0)))) (Rminus x (R_of_N ((BIT1 N0))))).
Axiom thm_GP : forall x : R, (Rlt (Rabs x) (R_of_N ((BIT1 N0)))) -> sums (fun n : N => Rpow x n) (Rinv (Rminus (R_of_N ((BIT1 N0))) x)).
Axiom thm_ABS_NEG_LEMMA : forall c : R, forall x : R, forall y : R, (Rle c (R_of_N N0)) -> (Rle (Rabs x) (Rmult c (Rabs y))) -> x = (R_of_N N0).
Axiom thm_SER_RATIO : forall f : N -> R, forall c : R, forall N' : N, ((Rlt c (R_of_N ((BIT1 N0)))) /\ (forall n : N, (N.ge n N') -> Rle (Rabs (f (N.succ n))) (Rmult c (Rabs (f n))))) -> summable f.
Axiom thm_SEQ_TRUNCATION : forall f : N -> R, forall l : R, forall n : N, forall b : R, ((sums f l) /\ (forall m : N, Rle (Rabs (psum (@pair N N n m) f)) b)) -> Rle (Rabs (Rminus l (psum (@pair N N N0 n) f))) b.
Axiom thm_tends_real_real : forall f : R -> R, forall l : R, forall x0 : R, (tends_real_real f l x0) = (@tends R R f l (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 x0)))).
Axiom thm_LIM : forall f : R -> R, forall y0 : R, forall x0 : R, (tends_real_real f y0 x0) = (forall e : R, (Rlt (R_of_N N0) e) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall x : R, ((Rlt (R_of_N N0) (Rabs (Rminus x x0))) /\ (Rlt (Rabs (Rminus x x0)) d)) -> Rlt (Rabs (Rminus (f x) y0)) e)).
Axiom thm_LIM_CONST : forall k : R, forall x : R, tends_real_real (fun x' : R => k) k x.
Axiom thm_LIM_ADD : forall (x : R), forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, ((tends_real_real f l x) /\ (tends_real_real g m x)) -> tends_real_real (fun x' : R => Rplus (f x') (g x')) (Rplus l m) x.
Axiom thm_LIM_MUL : forall (x : R), forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, ((tends_real_real f l x) /\ (tends_real_real g m x)) -> tends_real_real (fun x' : R => Rmult (f x') (g x')) (Rmult l m) x.
Axiom thm_LIM_NEG : forall (x : R), forall f : R -> R, forall l : R, (tends_real_real f l x) = (tends_real_real (fun x' : R => Ropp (f x')) (Ropp l) x).
Axiom thm_LIM_INV : forall (x : R), forall f : R -> R, forall l : R, ((tends_real_real f l x) /\ (~ (l = (R_of_N N0)))) -> tends_real_real (fun x' : R => Rinv (f x')) (Rinv l) x.
Axiom thm_LIM_SUB : forall (x : R), forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, ((tends_real_real f l x) /\ (tends_real_real g m x)) -> tends_real_real (fun x' : R => Rminus (f x') (g x')) (Rminus l m) x.
Axiom thm_LIM_DIV : forall (x : R), forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, ((tends_real_real f l x) /\ ((tends_real_real g m x) /\ (~ (m = (R_of_N N0))))) -> tends_real_real (fun x' : R => Rdiv (f x') (g x')) (Rdiv l m) x.
Axiom thm_LIM_NULL : forall f : R -> R, forall l : R, forall x : R, (tends_real_real f l x) = (tends_real_real (fun x' : R => Rminus (f x') l) (R_of_N N0) x).
Axiom thm_LIM_SUM : forall f : N -> R -> R, forall l : N -> R, forall m : N, forall n : N, forall x : R, (forall r : N, ((N.le m r) /\ (N.lt r (N.add m n))) -> tends_real_real (f r) (l r) x) -> tends_real_real (fun x' : R => psum (@pair N N m n) (fun r : N => f r x')) (psum (@pair N N m n) l) x.
Axiom thm_LIM_X : forall x0 : R, tends_real_real (fun x : R => x) x0 x0.
Axiom thm_LIM_UNIQ : forall f : R -> R, forall l : R, forall m : R, forall x : R, ((tends_real_real f l x) /\ (tends_real_real f m x)) -> l = m.
Axiom thm_LIM_EQUAL : forall f : R -> R, forall g : R -> R, forall l : R, forall x0 : R, (forall x : R, (~ (x = x0)) -> (f x) = (g x)) -> (tends_real_real f l x0) = (tends_real_real g l x0).
Axiom thm_LIM_TRANSFORM : forall f : R -> R, forall g : R -> R, forall x0 : R, forall l : R, ((tends_real_real (fun x : R => Rminus (f x) (g x)) (R_of_N N0) x0) /\ (tends_real_real g l x0)) -> tends_real_real f l x0.
Axiom thm_diffl : forall f : R -> R, forall x : R, forall l : R, (diffl f l x) = (tends_real_real (fun h : R => Rdiv (Rminus (f (Rplus x h)) (f x)) h) l (R_of_N N0)).
Axiom thm_contl : forall f : R -> R, forall x : R, (contl f x) = (tends_real_real (fun h : R => f (Rplus x h)) (f x) (R_of_N N0)).
Axiom thm_differentiable : forall f : R -> R, forall x : R, (differentiable f x) = (exists l : R, diffl f l x).
Axiom thm_DIFF_UNIQ : forall f : R -> R, forall l : R, forall m : R, forall x : R, ((diffl f l x) /\ (diffl f m x)) -> l = m.
Axiom thm_DIFF_CONT : forall f : R -> R, forall l : R, forall x : R, (diffl f l x) -> contl f x.
Axiom thm_CONTL_LIM : forall f : R -> R, forall x : R, (contl f x) = (tends_real_real f (f x) x).
Axiom thm_CONT_X : forall x : R, contl (fun x' : R => x') x.
Axiom thm_CONT_CONST : forall (k : R), forall x : R, contl (fun x' : R => k) x.
Axiom thm_CONT_ADD : forall (f : R -> R) (g : R -> R), forall x : R, ((contl f x) /\ (contl g x)) -> contl (fun x' : R => Rplus (f x') (g x')) x.
Axiom thm_CONT_MUL : forall (f : R -> R) (g : R -> R), forall x : R, ((contl f x) /\ (contl g x)) -> contl (fun x' : R => Rmult (f x') (g x')) x.
Axiom thm_CONT_NEG : forall (f : R -> R), forall x : R, (contl f x) -> contl (fun x' : R => Ropp (f x')) x.
Axiom thm_CONT_INV : forall (f : R -> R), forall x : R, ((contl f x) /\ (~ ((f x) = (R_of_N N0)))) -> contl (fun x' : R => Rinv (f x')) x.
Axiom thm_CONT_SUB : forall (f : R -> R) (g : R -> R), forall x : R, ((contl f x) /\ (contl g x)) -> contl (fun x' : R => Rminus (f x') (g x')) x.
Axiom thm_CONT_DIV : forall (f : R -> R) (g : R -> R), forall x : R, ((contl f x) /\ ((contl g x) /\ (~ ((g x) = (R_of_N N0))))) -> contl (fun x' : R => Rdiv (f x') (g x')) x.
Axiom thm_CONT_ABS : forall f : R -> R, forall x : R, (contl f x) -> contl (fun x' : R => Rabs (f x')) x.
Axiom thm_CONT_COMPOSE : forall f : R -> R, forall g : R -> R, forall x : R, ((contl f x) /\ (contl g (f x))) -> contl (fun x' : R => g (f x')) x.
Axiom thm_IVT : forall f : R -> R, forall a : R, forall b : R, forall y : R, ((Rle a b) /\ (((Rle (f a) y) /\ (Rle y (f b))) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x))) -> exists x : R, (Rle a x) /\ ((Rle x b) /\ ((f x) = y)).
Axiom thm_IVT2 : forall f : R -> R, forall a : R, forall b : R, forall y : R, ((Rle a b) /\ (((Rle (f b) y) /\ (Rle y (f a))) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x))) -> exists x : R, (Rle a x) /\ ((Rle x b) /\ ((f x) = y)).
Axiom thm_DIFF_CONST : forall k : R, forall x : R, diffl (fun x' : R => k) (R_of_N N0) x.
Axiom thm_DIFF_ADD : forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, forall x : R, ((diffl f l x) /\ (diffl g m x)) -> diffl (fun x' : R => Rplus (f x') (g x')) (Rplus l m) x.
Axiom thm_DIFF_MUL : forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, forall x : R, ((diffl f l x) /\ (diffl g m x)) -> diffl (fun x' : R => Rmult (f x') (g x')) (Rplus (Rmult l (g x)) (Rmult m (f x))) x.
Axiom thm_DIFF_CMUL : forall f : R -> R, forall c : R, forall l : R, forall x : R, (diffl f l x) -> diffl (fun x' : R => Rmult c (f x')) (Rmult c l) x.
Axiom thm_DIFF_NEG : forall f : R -> R, forall l : R, forall x : R, (diffl f l x) -> diffl (fun x' : R => Ropp (f x')) (Ropp l) x.
Axiom thm_DIFF_SUB : forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, forall x : R, ((diffl f l x) /\ (diffl g m x)) -> diffl (fun x' : R => Rminus (f x') (g x')) (Rminus l m) x.
Axiom thm_DIFF_CARAT : forall f : R -> R, forall l : R, forall x : R, (diffl f l x) = (exists g : R -> R, (forall z : R, (Rminus (f z) (f x)) = (Rmult (g z) (Rminus z x))) /\ ((contl g x) /\ ((g x) = l))).
Axiom thm_DIFF_CHAIN : forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, forall x : R, ((diffl f l (g x)) /\ (diffl g m x)) -> diffl (fun x' : R => f (g x')) (Rmult l m) x.
Axiom thm_DIFF_X : forall x : R, diffl (fun x' : R => x') (R_of_N ((BIT1 N0))) x.
Axiom thm_DIFF_POW : forall n : N, forall x : R, diffl (fun x' : R => Rpow x' n) (Rmult (R_of_N n) (Rpow x (N.sub n ((BIT1 N0))))) x.
Axiom thm_DIFF_XM1 : forall x : R, (~ (x = (R_of_N N0))) -> diffl (fun x' : R => Rinv x') (Ropp (Rpow (Rinv x) ((BIT0 (BIT1 N0))))) x.
Axiom thm_DIFF_INV : forall f : R -> R, forall l : R, forall x : R, ((diffl f l x) /\ (~ ((f x) = (R_of_N N0)))) -> diffl (fun x' : R => Rinv (f x')) (Ropp (Rdiv l (Rpow (f x) ((BIT0 (BIT1 N0)))))) x.
Axiom thm_DIFF_DIV : forall (x : R), forall f : R -> R, forall g : R -> R, forall l : R, forall m : R, ((diffl f l x) /\ ((diffl g m x) /\ (~ ((g x) = (R_of_N N0))))) -> diffl (fun x' : R => Rdiv (f x') (g x')) (Rdiv (Rminus (Rmult l (g x)) (Rmult m (f x))) (Rpow (g x) ((BIT0 (BIT1 N0))))) x.
Axiom thm_DIFF_SUM : forall f : N -> R -> R, forall f' : N -> R -> R, forall m : N, forall n : N, forall x : R, (forall r : N, ((N.le m r) /\ (N.lt r (N.add m n))) -> diffl (fun x' : R => f r x') (f' r x) x) -> diffl (fun x' : R => psum (@pair N N m n) (fun n' : N => f n' x')) (psum (@pair N N m n) (fun r : N => f' r x)) x.
Axiom thm_CONT_BOUNDED : forall f : R -> R, forall a : R, forall b : R, ((Rle a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x)) -> exists M : R, forall x : R, ((Rle a x) /\ (Rle x b)) -> Rle (f x) M.
Axiom thm_CONT_BOUNDED_ABS : forall f : R -> R, forall a : R, forall b : R, (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x) -> exists M : R, forall x : R, ((Rle a x) /\ (Rle x b)) -> Rle (Rabs (f x)) M.
Axiom thm_CONT_HASSUP : forall f : R -> R, forall a : R, forall b : R, ((Rle a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x)) -> exists M : R, (forall x : R, ((Rle a x) /\ (Rle x b)) -> Rle (f x) M) /\ (forall N' : R, (Rlt N' M) -> exists x : R, (Rle a x) /\ ((Rle x b) /\ (Rlt N' (f x)))).
Axiom thm_CONT_ATTAINS : forall f : R -> R, forall a : R, forall b : R, ((Rle a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x)) -> exists M : R, (forall x : R, ((Rle a x) /\ (Rle x b)) -> Rle (f x) M) /\ (exists x : R, (Rle a x) /\ ((Rle x b) /\ ((f x) = M))).
Axiom thm_CONT_ATTAINS2 : forall f : R -> R, forall a : R, forall b : R, ((Rle a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x)) -> exists M : R, (forall x : R, ((Rle a x) /\ (Rle x b)) -> Rle M (f x)) /\ (exists x : R, (Rle a x) /\ ((Rle x b) /\ ((f x) = M))).
Axiom thm_CONT_ATTAINS_ALL : forall f : R -> R, forall a : R, forall b : R, ((Rle a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x)) -> exists L : R, exists M : R, (forall x : R, ((Rle a x) /\ (Rle x b)) -> (Rle L (f x)) /\ (Rle (f x) M)) /\ (forall y : R, ((Rle L y) /\ (Rle y M)) -> exists x : R, (Rle a x) /\ ((Rle x b) /\ ((f x) = y))).
Axiom thm_DIFF_LINC : forall f : R -> R, forall x : R, forall l : R, ((diffl f l x) /\ (Rlt (R_of_N N0) l)) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall h : R, ((Rlt (R_of_N N0) h) /\ (Rlt h d)) -> Rlt (f x) (f (Rplus x h))).
Axiom thm_DIFF_LDEC : forall f : R -> R, forall x : R, forall l : R, ((diffl f l x) /\ (Rlt l (R_of_N N0))) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall h : R, ((Rlt (R_of_N N0) h) /\ (Rlt h d)) -> Rlt (f x) (f (Rminus x h))).
Axiom thm_DIFF_LMAX : forall f : R -> R, forall x : R, forall l : R, ((diffl f l x) /\ (exists d : R, (Rlt (R_of_N N0) d) /\ (forall y : R, (Rlt (Rabs (Rminus x y)) d) -> Rle (f y) (f x)))) -> l = (R_of_N N0).
Axiom thm_DIFF_LMIN : forall f : R -> R, forall x : R, forall l : R, ((diffl f l x) /\ (exists d : R, (Rlt (R_of_N N0) d) /\ (forall y : R, (Rlt (Rabs (Rminus x y)) d) -> Rle (f x) (f y)))) -> l = (R_of_N N0).
Axiom thm_DIFF_LCONST : forall f : R -> R, forall x : R, forall l : R, ((diffl f l x) /\ (exists d : R, (Rlt (R_of_N N0) d) /\ (forall y : R, (Rlt (Rabs (Rminus x y)) d) -> (f y) = (f x)))) -> l = (R_of_N N0).
Axiom thm_INTERVAL_LEMMA_LT : forall a : R, forall b : R, forall x : R, ((Rlt a x) /\ (Rlt x b)) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall y : R, (Rlt (Rabs (Rminus x y)) d) -> (Rlt a y) /\ (Rlt y b)).
Axiom thm_INTERVAL_LEMMA : forall a : R, forall b : R, forall x : R, ((Rlt a x) /\ (Rlt x b)) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall y : R, (Rlt (Rabs (Rminus x y)) d) -> (Rle a y) /\ (Rle y b)).
Axiom thm_ROLLE : forall f : R -> R, forall a : R, forall b : R, ((Rlt a b) /\ (((f a) = (f b)) /\ ((forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x) /\ (forall x : R, ((Rlt a x) /\ (Rlt x b)) -> differentiable f x)))) -> exists z : R, (Rlt a z) /\ ((Rlt z b) /\ (diffl f (R_of_N N0) z)).
Axiom thm_MVT_LEMMA : forall f : R -> R, forall a : R, forall b : R, ((fun x : R => Rminus (f x) (Rmult (Rdiv (Rminus (f b) (f a)) (Rminus b a)) x)) a) = ((fun x : R => Rminus (f x) (Rmult (Rdiv (Rminus (f b) (f a)) (Rminus b a)) x)) b).
Axiom thm_MVT : forall f : R -> R, forall a : R, forall b : R, ((Rlt a b) /\ ((forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x) /\ (forall x : R, ((Rlt a x) /\ (Rlt x b)) -> differentiable f x))) -> exists l : R, exists z : R, (Rlt a z) /\ ((Rlt z b) /\ ((diffl f l z) /\ ((Rminus (f b) (f a)) = (Rmult (Rminus b a) l)))).
Axiom thm_MVT_ALT : forall f : R -> R, forall f' : R -> R, forall a : R, forall b : R, ((Rlt a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> diffl f (f' x) x)) -> exists z : R, (Rlt a z) /\ ((Rlt z b) /\ ((Rminus (f b) (f a)) = (Rmult (Rminus b a) (f' z)))).
Axiom thm_DIFF_ISCONST_END : forall f : R -> R, forall a : R, forall b : R, ((Rlt a b) /\ ((forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x) /\ (forall x : R, ((Rlt a x) /\ (Rlt x b)) -> diffl f (R_of_N N0) x))) -> (f b) = (f a).
Axiom thm_DIFF_ISCONST : forall f : R -> R, forall a : R, forall b : R, ((Rlt a b) /\ ((forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x) /\ (forall x : R, ((Rlt a x) /\ (Rlt x b)) -> diffl f (R_of_N N0) x))) -> forall x : R, ((Rle a x) /\ (Rle x b)) -> (f x) = (f a).
Axiom thm_DIFF_ISCONST_END_SIMPLE : forall f : R -> R, forall a : R, forall b : R, ((Rlt a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> diffl f (R_of_N N0) x)) -> (f b) = (f a).
Axiom thm_DIFF_ISCONST_ALL : forall f : R -> R, forall x : R, forall y : R, (forall x' : R, diffl f (R_of_N N0) x') -> (f x) = (f y).
Axiom thm_CONT_INJ_LEMMA : forall f : R -> R, forall g : R -> R, forall x : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((forall z : R, (Rle (Rabs (Rminus z x)) d) -> (g (f z)) = z) /\ (forall z : R, (Rle (Rabs (Rminus z x)) d) -> contl f z))) -> ~ (forall z : R, (Rle (Rabs (Rminus z x)) d) -> Rle (f z) (f x)).
Axiom thm_CONT_INJ_LEMMA2 : forall f : R -> R, forall g : R -> R, forall x : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((forall z : R, (Rle (Rabs (Rminus z x)) d) -> (g (f z)) = z) /\ (forall z : R, (Rle (Rabs (Rminus z x)) d) -> contl f z))) -> ~ (forall z : R, (Rle (Rabs (Rminus z x)) d) -> Rle (f x) (f z)).
Axiom thm_CONT_INJ_RANGE : forall f : R -> R, forall g : R -> R, forall x : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((forall z : R, (Rle (Rabs (Rminus z x)) d) -> (g (f z)) = z) /\ (forall z : R, (Rle (Rabs (Rminus z x)) d) -> contl f z))) -> exists e : R, (Rlt (R_of_N N0) e) /\ (forall y : R, (Rle (Rabs (Rminus y (f x))) e) -> exists z : R, (Rle (Rabs (Rminus z x)) d) /\ ((f z) = y)).
Axiom thm_CONT_INVERSE : forall f : R -> R, forall g : R -> R, forall x : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((forall z : R, (Rle (Rabs (Rminus z x)) d) -> (g (f z)) = z) /\ (forall z : R, (Rle (Rabs (Rminus z x)) d) -> contl f z))) -> contl g (f x).
Axiom thm_DIFF_INVERSE : forall f : R -> R, forall g : R -> R, forall l : R, forall x : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((forall z : R, (Rle (Rabs (Rminus z x)) d) -> (g (f z)) = z) /\ ((forall z : R, (Rle (Rabs (Rminus z x)) d) -> contl f z) /\ ((diffl f l x) /\ (~ (l = (R_of_N N0))))))) -> diffl g (Rinv l) (f x).
Axiom thm_DIFF_INVERSE_LT : forall f : R -> R, forall g : R -> R, forall l : R, forall x : R, forall d : R, ((Rlt (R_of_N N0) d) /\ ((forall z : R, (Rlt (Rabs (Rminus z x)) d) -> (g (f z)) = z) /\ ((forall z : R, (Rlt (Rabs (Rminus z x)) d) -> contl f z) /\ ((diffl f l x) /\ (~ (l = (R_of_N N0))))))) -> diffl g (Rinv l) (f x).
Axiom thm_IVT_DERIVATIVE_0 : forall f : R -> R, forall f' : R -> R, forall a : R, forall b : R, ((Rle a b) /\ ((forall x : R, ((Rle a x) /\ (Rle x b)) -> diffl f (f' x) x) /\ ((Rgt (f' a) (R_of_N N0)) /\ (Rlt (f' b) (R_of_N N0))))) -> exists z : R, (Rlt a z) /\ ((Rlt z b) /\ ((f' z) = (R_of_N N0))).
Axiom thm_IVT_DERIVATIVE_POS : forall f : R -> R, forall f' : R -> R, forall a : R, forall b : R, forall y : R, ((Rle a b) /\ ((forall x : R, ((Rle a x) /\ (Rle x b)) -> diffl f (f' x) x) /\ ((Rgt (f' a) y) /\ (Rlt (f' b) y)))) -> exists z : R, (Rlt a z) /\ ((Rlt z b) /\ ((f' z) = y)).
Axiom thm_IVT_DERIVATIVE_NEG : forall f : R -> R, forall f' : R -> R, forall a : R, forall b : R, forall y : R, ((Rle a b) /\ ((forall x : R, ((Rle a x) /\ (Rle x b)) -> diffl f (f' x) x) /\ ((Rlt (f' a) y) /\ (Rgt (f' b) y)))) -> exists z : R, (Rlt a z) /\ ((Rlt z b) /\ ((f' z) = y)).
Axiom thm_SEQ_CONT_UNIFORM : forall s : N -> R -> R, forall f : R -> R, forall x0 : R, ((forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, exists d : R, (Rlt (R_of_N N0) d) /\ (forall x : R, forall n : N, ((Rlt (Rabs (Rminus x x0)) d) /\ (N.ge n N')) -> Rlt (Rabs (Rminus (s n x) (f x))) e)) /\ (exists N' : N, forall n : N, (N.ge n N') -> contl (s n) x0)) -> contl f x0.
Axiom thm_SER_COMPARA_UNIFORM : forall s : R -> N -> R, forall x0 : R, forall g : N -> R, ((exists N' : N, exists d : R, (Rlt (R_of_N N0) d) /\ (forall n : N, forall x : R, ((Rlt (Rabs (Rminus x x0)) d) /\ (N.ge n N')) -> Rle (Rabs (s x n)) (g n))) /\ (summable g)) -> exists f : R -> R, exists d : R, (Rlt (R_of_N N0) d) /\ (forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, forall x : R, forall n : N, ((Rlt (Rabs (Rminus x x0)) d) /\ (N.ge n N')) -> Rlt (Rabs (Rminus (psum (@pair N N N0 n) (s x)) (f x))) e).
Axiom thm_SER_COMPARA_UNIFORM_WEAK : forall s : R -> N -> R, forall x0 : R, forall g : N -> R, ((exists N' : N, exists d : R, (Rlt (R_of_N N0) d) /\ (forall n : N, forall x : R, ((Rlt (Rabs (Rminus x x0)) d) /\ (N.ge n N')) -> Rle (Rabs (s x n)) (g n))) /\ (summable g)) -> exists f : R -> R, forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, exists d : R, (Rlt (R_of_N N0) d) /\ (forall x : R, forall n : N, ((Rlt (Rabs (Rminus x x0)) d) /\ (N.ge n N')) -> Rlt (Rabs (Rminus (psum (@pair N N N0 n) (s x)) (f x))) e).
Axiom thm_CONTL : forall f : R -> R, forall x : R, (contl f x) = (forall e : R, (Rlt (R_of_N N0) e) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall x' : R, (Rlt (Rabs (Rminus x' x)) d) -> Rlt (Rabs (Rminus (f x') (f x))) e)).
Axiom thm_CONTL_SEQ : forall f : R -> R, forall x : N -> R, forall l : R, ((contl f l) /\ (tends_num_real x l)) -> tends_num_real (fun n : N => f (x n)) (f l).
Axiom thm_SUP_INTERVAL : forall P : R -> Prop, forall a : R, forall b : R, (exists x : R, (Rle a x) /\ ((Rle x b) /\ (P x))) -> exists s : R, (Rle a s) /\ ((Rle s b) /\ (forall y : R, (Rlt y s) = (exists x : R, (Rle a x) /\ ((Rle x b) /\ ((P x) /\ (Rlt y x)))))).
Axiom thm_CONT_UNIFORM : forall f : R -> R, forall a : R, forall b : R, ((Rle a b) /\ (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x)) -> forall e : R, (Rlt (R_of_N N0) e) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall x : R, forall y : R, ((Rle a x) /\ ((Rle x b) /\ ((Rle a y) /\ ((Rle y b) /\ (Rlt (Rabs (Rminus x y)) d))))) -> Rlt (Rabs (Rminus (f x) (f y))) e).
Axiom thm_CONT_UNIFORM_STRONG : forall f : R -> R, forall a : R, forall b : R, (forall x : R, ((Rle a x) /\ (Rle x b)) -> contl f x) -> forall e : R, (Rlt (R_of_N N0) e) -> exists d : R, (Rlt (R_of_N N0) d) /\ (forall x : R, forall y : R, ((((Rle a x) /\ (Rle x b)) \/ ((Rle a y) /\ (Rle y b))) /\ (Rlt (Rabs (Rminus x y)) d)) -> Rlt (Rabs (Rminus (f x) (f y))) e).
Axiom thm_SUBSET_PRED : forall {_168468 : Type'}, forall P : _168468 -> Prop, forall Q : _168468 -> Prop, (@subset _168468 P Q) = (forall x : _168468, (P x) -> Q x).
Axiom thm_UNIONS_PRED : forall {_168484 : Type'} (P : (_168484 -> Prop) -> Prop), (@UNIONS _168484 P) = (fun x : _168484 => exists p : _168484 -> Prop, (P p) /\ (p x)).
Axiom thm_IN_FLD : forall {A : Type'}, forall l : A -> A -> Prop, forall x : A, (@IN A x (@fld A l)) = (exists y : A, (l x y) \/ (l y x)).
Axiom thm_FLD_EQ_EMPTY : forall {A : Type'}, forall R' : A -> A -> Prop, ((@fld A R') = (@set0 A)) = (R' = (fun x : A => fun y : A => False)).
Axiom thm_FLD_SUBSET : forall {_168589 : Type'}, forall l : _168589 -> _168589 -> Prop, forall r : _168589 -> _168589 -> Prop, (forall x : _168589, forall y : _168589, (l x y) -> r x y) -> @subset _168589 (@fld _168589 l) (@fld _168589 r).
Axiom thm_FINITE_FLD : forall {A : Type'}, forall l : A -> A -> Prop, (@finite_set A (@fld A l)) = (@finite_set (prod A A) (@GSPEC (prod A A) (fun GEN_PVAR_378 : prod A A => exists x : A, exists y : A, @SETSPEC (prod A A) GEN_PVAR_378 (l x y) (@pair A A x y)))).
Axiom thm_qoset : forall {A : Type'}, forall l : A -> A -> Prop, (@qoset A l) = ((forall x : A, (@IN A x (@fld A l)) -> l x x) /\ (forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z)).
Axiom thm_poset : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) = ((forall x : A, (@IN A x (@fld A l)) -> l x x) /\ ((forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z) /\ (forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y))).
Axiom thm_toset : forall {A : Type'}, forall l : A -> A -> Prop, (@toset A l) = ((forall x : A, (@IN A x (@fld A l)) -> l x x) /\ ((forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z) /\ ((forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A l)) /\ (@IN A y (@fld A l))) -> (l x y) \/ (l y x))))).
Axiom thm_woset : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) = ((forall x : A, (@IN A x (@fld A l)) -> l x x) /\ ((forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z) /\ ((forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y) /\ ((forall x : A, forall y : A, ((@IN A x (@fld A l)) /\ (@IN A y (@fld A l))) -> (l x y) \/ (l y x)) /\ (forall s : A -> Prop, ((@subset A s (@fld A l)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> l x y)))))).
Axiom thm_wqoset : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) = ((forall x : A, (@IN A x (@fld A l)) -> l x x) /\ ((forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z) /\ (forall s : A -> Prop, (@subset A s (@fld A l)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (l x y)))))).
Axiom thm_chain : forall {A : Type'}, forall s : A -> Prop, forall l : A -> A -> Prop, (@chain A l s) = (forall x : A, forall y : A, ((@IN A x s) /\ (@IN A y s)) -> (l x y) \/ (l y x)).
Axiom thm_antichain : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, (@antichain A l s) = ((@subset A s (@fld A l)) /\ (@pairwise A (fun x : A => fun y : A => ~ (l x y)) s)).
Axiom thm_CHAIN : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, (@chain A l s) = ((@subset A s (@fld A l)) /\ (forall x : A, forall y : A, ((@IN A x s) /\ (@IN A y s)) -> (l x y) \/ (l y x))).
Axiom thm_ANTICHAIN : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, (@antichain A l s) = ((@subset A s (@fld A l)) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ (~ (x = y)))) -> ~ (l x y))).
Axiom thm_CHAIN_SUBSET : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@chain A l s) /\ (@subset A t s)) -> @chain A l t.
Axiom thm_ANTICHAIN_SUBSET : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@antichain A l s) /\ (@subset A t s)) -> @antichain A l t.
Axiom thm_QOSET_REFL : forall {A : Type'}, forall l : A -> A -> Prop, (@qoset A l) -> forall x : A, (@fld A l x) -> l x x.
Axiom thm_QOSET_TRANS : forall {A : Type'}, forall l : A -> A -> Prop, (@qoset A l) -> forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z.
Axiom thm_QOSET_REFL_EQ : forall {A : Type'}, forall l : A -> A -> Prop, forall x : A, (@qoset A l) -> (l x x) = (@IN A x (@fld A l)).
Axiom thm_QOSET_FLDEQ : forall {A : Type'}, forall l : A -> A -> Prop, (@qoset A l) -> forall x : A, (@fld A l x) = (l x x).
Axiom thm_QOSET_FLD : forall {A : Type'}, forall l : A -> A -> Prop, (@qoset A l) -> (@fld A l) = (@GSPEC A (fun GEN_PVAR_379 : A => exists x : A, @SETSPEC A GEN_PVAR_379 (l x x) x)).
Axiom thm_WOSET_IMP_TOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> @toset A l.
Axiom thm_WOSET_IMP_POSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> @poset A l.
Axiom thm_WOSET_IMP_QOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> @qoset A l.
Axiom thm_TOSET_IMP_POSET : forall {A : Type'}, forall l : A -> A -> Prop, (@toset A l) -> @poset A l.
Axiom thm_TOSET_IMP_QOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@toset A l) -> @qoset A l.
Axiom thm_POSET_IMP_QOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> @qoset A l.
Axiom thm_WQOSET_IMP_QOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) -> @qoset A l.
Axiom thm_strictly : forall {A : Type'}, forall R' : A -> A -> Prop, (@strictly A R') = (fun x : A => fun y : A => (R' x y) /\ (~ (R' y x))).
Axiom thm_properly : forall {A : Type'}, forall R' : A -> A -> Prop, (@properly A R') = (fun x : A => fun y : A => (R' x y) /\ (~ (x = y))).
Axiom thm_PROPERLY_EQ_STRICTLY : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> (@properly A l) = (@strictly A l).
Axiom thm_STRICTLY_EQ_PROPERLY : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> (@strictly A l) = (@properly A l).
Axiom thm_STRICTLY_IMP_PROPERLY : forall {A : Type'}, forall l : A -> A -> Prop, forall x : A, forall y : A, ((@qoset A l) /\ (@strictly A l x y)) -> @properly A l x y.
Axiom thm_STRICTLY_STRICTLY : forall {A : Type'}, forall R' : A -> A -> Prop, (@strictly A (@strictly A R')) = (@strictly A R').
Axiom thm_PROPERLY_PROPERLY : forall {A : Type'}, forall R' : A -> A -> Prop, (@properly A (@properly A R')) = (@properly A R').
Axiom thm_STRICTLY_PROPERLY : forall {A : Type'}, forall R' : A -> A -> Prop, (@strictly A (@properly A R')) = (@strictly A R').
Axiom thm_PROPERLY_STRICTLY : forall {A : Type'}, forall R' : A -> A -> Prop, (@properly A (@strictly A R')) = (@strictly A R').
Axiom thm_PROPERLY_MONO : forall {_169610 : Type'}, forall R' : _169610 -> _169610 -> Prop, forall S' : _169610 -> _169610 -> Prop, (forall x : _169610, forall y : _169610, (R' x y) -> S' x y) -> forall x : _169610, forall y : _169610, (@properly _169610 R' x y) -> @properly _169610 S' x y.
Axiom thm_POSET_QOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) = ((@qoset A l) /\ (forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y)).
Axiom thm_TOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@toset A l) = ((forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z) /\ ((forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A l)) /\ (@IN A y (@fld A l))) -> (l x y) \/ (l y x)))).
Axiom thm_TOSET_POSET : forall {A : Type'}, forall l : A -> A -> Prop, (@toset A l) = ((@poset A l) /\ (forall x : A, forall y : A, ((@IN A x (@fld A l)) /\ (@IN A y (@fld A l))) -> (l x y) \/ (l y x))).
Axiom thm_WOSET_TOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) = ((@toset A l) /\ (forall s : A -> Prop, ((@subset A s (@fld A l)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> l x y))).
Axiom thm_WQOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) = ((forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z) /\ (forall s : A -> Prop, (@subset A s (@fld A l)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (l x y))))).
Axiom thm_WQOSET_QOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) = ((@qoset A l) /\ (forall s : A -> Prop, (@subset A s (@fld A l)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (l x y))))).
Axiom thm_WOSET_POSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) = ((@poset A l) /\ (forall s : A -> Prop, ((@subset A s (@fld A l)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> l x y))).
Axiom thm_WOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) = ((forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y) /\ (forall s : A -> Prop, ((@subset A s (@fld A l)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> l x y))).
Axiom thm_WOSET_WF : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) = ((forall x : A, forall y : A, ((@IN A x (@fld A l)) /\ (@IN A y (@fld A l))) -> (l x y) \/ (l y x)) /\ (@well_founded A (@properly A l))).
Axiom thm_WOSET_IMP_WQOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> @wqoset A l.
Axiom thm_WQOSET_SUPERSET : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@wqoset A l) /\ ((@qoset A m) /\ ((@subset A (@fld A m) (@fld A l)) /\ (forall x : A, forall y : A, (l x y) -> m x y)))) -> @wqoset A m.
Axiom thm_WQOSET_NOBAD : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) = ((@qoset A l) /\ (forall x : N -> A, (forall n : N, @IN A (x n) (@fld A l)) -> exists i : N, exists j : N, (N.lt i j) /\ (l (x i) (x j)))).
Axiom thm_WQOSET_ANTICHAIN : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) = ((@qoset A l) /\ ((@well_founded A (@strictly A l)) /\ (forall s : A -> Prop, (@antichain A l s) -> @finite_set A s))).
Axiom thm_WQOSET_NOBAD_SUBSEQ : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) = ((@qoset A l) /\ (forall x : N -> A, (forall n : N, @IN A (x n) (@fld A l)) -> exists r : N -> N, (forall m : N, forall n : N, (N.lt m n) -> N.lt (r m) (r n)) /\ (forall i : N, forall j : N, (N.le i j) -> l (x (r i)) (x (r j))))).
Axiom thm_WQOSET_IMP_WF : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) -> @well_founded A (@strictly A l).
Axiom thm_WQOSET_WF_SUPERSET : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@wqoset A l) /\ ((@qoset A m) /\ ((@subset A (@fld A m) (@fld A l)) /\ (forall x : A, forall y : A, (l x y) -> m x y)))) -> @well_founded A (@strictly A m).
Axiom thm_WQOSET_WF_SUPERSET_EQ : forall {A : Type'}, forall l : A -> A -> Prop, (@wqoset A l) = ((@qoset A l) /\ (forall m : A -> A -> Prop, ((@qoset A m) /\ (((@fld A m) = (@fld A l)) /\ (forall x : A, forall y : A, (l x y) -> m x y))) -> @well_founded A (@strictly A m))).
Axiom thm_WOSET_WQOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) = ((@toset A l) /\ (@wqoset A l)).
Axiom thm_FLD_RESTRICT_QOSET : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@qoset A l) -> (@fld A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y)))) = (@GSPEC A (fun GEN_PVAR_389 : A => exists x : A, @SETSPEC A GEN_PVAR_389 ((@IN A x (@fld A l)) /\ (P x)) x)).
Axiom thm_FLD_RESTRICT_POSET : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@poset A l) -> (@fld A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y)))) = (@GSPEC A (fun GEN_PVAR_390 : A => exists x : A, @SETSPEC A GEN_PVAR_390 ((@IN A x (@fld A l)) /\ (P x)) x)).
Axiom thm_FLD_RESTRICT_TOSET : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@toset A l) -> (@fld A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y)))) = (@GSPEC A (fun GEN_PVAR_391 : A => exists x : A, @SETSPEC A GEN_PVAR_391 ((@IN A x (@fld A l)) /\ (P x)) x)).
Axiom thm_FLD_RESTRICT_WOSET : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@woset A l) -> (@fld A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y)))) = (@GSPEC A (fun GEN_PVAR_392 : A => exists x : A, @SETSPEC A GEN_PVAR_392 ((@IN A x (@fld A l)) /\ (P x)) x)).
Axiom thm_FLD_RESTRICT_WQOSET : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@wqoset A l) -> (@fld A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y)))) = (@GSPEC A (fun GEN_PVAR_393 : A => exists x : A, @SETSPEC A GEN_PVAR_393 ((@IN A x (@fld A l)) /\ (P x)) x)).
Axiom thm_QOSET_RESTRICT : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@qoset A l) -> @qoset A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y))).
Axiom thm_POSET_RESTRICT : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@poset A l) -> @poset A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y))).
Axiom thm_TOSET_RESTRICT : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@toset A l) -> @toset A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y))).
Axiom thm_WOSET_RESTRICT : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@woset A l) -> @woset A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y))).
Axiom thm_WQOSET_RESTRICT : forall {A : Type'}, forall l : A -> A -> Prop, forall P : A -> Prop, (@wqoset A l) -> @wqoset A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (l x y))).
Axiom thm_QOSET_MAX : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, ((@qoset A l) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (@subset A s (@fld A l))))) -> exists a : A, (@IN A a s) /\ (forall x : A, (@IN A x s) -> ~ (@strictly A l a x)).
Axiom thm_QOSET_MIN : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, ((@qoset A l) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (@subset A s (@fld A l))))) -> exists a : A, (@IN A a s) /\ (forall x : A, (@IN A x s) -> ~ (@strictly A l x a)).
Axiom thm_POSET_MAX : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, ((@poset A l) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (@subset A s (@fld A l))))) -> exists a : A, (@IN A a s) /\ (forall x : A, (@IN A x s) -> ~ (@properly A l a x)).
Axiom thm_POSET_MIN : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, ((@poset A l) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (@subset A s (@fld A l))))) -> exists a : A, (@IN A a s) /\ (forall x : A, (@IN A x s) -> ~ (@properly A l x a)).
Axiom thm_TOSET_MAX : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, ((@toset A l) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (@subset A s (@fld A l))))) -> exists a : A, (@IN A a s) /\ (forall x : A, (@IN A x s) -> l x a).
Axiom thm_TOSET_MIN : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, ((@toset A l) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (@subset A s (@fld A l))))) -> exists a : A, (@IN A a s) /\ (forall x : A, (@IN A x s) -> l a x).
Axiom thm_FLD_TRIVIAL : forall {A : Type'}, (@fld A (fun x : A => fun y : A => False)) = (@set0 A).
Axiom thm_WOSET_TRIVIAL : forall {A : Type'}, @woset A (fun x : A => fun y : A => False).
Axiom thm_WQOSET_TRIVIAL : forall {A : Type'}, @wqoset A (fun x : A => fun y : A => False).
Axiom thm_TOSET_TRIVIAL : forall {A : Type'}, @toset A (fun x : A => fun y : A => False).
Axiom thm_POSET_TRIVIAL : forall {A : Type'}, @poset A (fun x : A => fun y : A => False).
Axiom thm_QOSET_TRIVIAL : forall {A : Type'}, @qoset A (fun x : A => fun y : A => False).
Axiom thm_FLD_num : (@fld N N.le) = (@setT N).
Axiom thm_WOSET_num : @woset N N.le.
Axiom thm_WQOSET_num : @wqoset N N.le.
Axiom thm_TOSET_num : @toset N N.le.
Axiom thm_POSET_num : @poset N N.le.
Axiom thm_QOSET_num : @qoset N N.le.
Axiom thm_QOSET_POINTWISE : forall {A K : Type'}, forall l : A -> A -> Prop, forall s : K -> Prop, (@qoset (K -> A) (fun x : K -> A => fun y : K -> A => forall i : K, (@IN K i s) -> l (x i) (y i))) = ((s = (@set0 K)) \/ (@qoset A l)).
Axiom thm_FLD_POINTWISE : forall {A K : Type'}, forall l : A -> A -> Prop, forall s : K -> Prop, (@qoset A l) -> (@fld (K -> A) (fun x : K -> A => fun y : K -> A => forall i : K, (@IN K i s) -> l (x i) (y i))) = (@GSPEC (K -> A) (fun GEN_PVAR_394 : K -> A => exists x : K -> A, @SETSPEC (K -> A) GEN_PVAR_394 (forall i : K, (@IN K i s) -> @IN A (x i) (@fld A l)) x)).
Axiom thm_WQOSET_POINTWISE : forall {A K : Type'}, forall l : A -> A -> Prop, forall s : K -> Prop, ((@wqoset A l) /\ (@finite_set K s)) -> @wqoset (K -> A) (fun x : K -> A => fun y : K -> A => forall i : K, (@IN K i s) -> l (x i) (y i)).
Axiom thm_DICKSON : forall n : N, forall x : N -> N -> N, exists i : N, exists j : N, (N.lt i j) /\ (forall k : N, (N.lt k n) -> N.le (x i k) (x j k)).
Axiom thm_inseg : forall {A : Type'}, forall m : A -> A -> Prop, forall l : A -> A -> Prop, (@inseg A l m) = (forall x : A, forall y : A, (l x y) = ((m x y) /\ (@fld A l y))).
Axiom thm_INSEG_ANTISYM : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@inseg A l m) /\ (@inseg A m l)) -> l = m.
Axiom thm_INSEG_REFL : forall {A : Type'}, forall l : A -> A -> Prop, @inseg A l l.
Axiom thm_INSEG_TRANS : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, forall n : A -> A -> Prop, ((@inseg A l m) /\ (@inseg A m n)) -> @inseg A l n.
Axiom thm_linseg : forall {A : Type'}, forall l : A -> A -> Prop, forall a : A, (@linseg A l a) = (fun x : A => fun y : A => (l x y) /\ (@properly A l y a)).
Axiom thm_ordinal : forall {A : Type'}, forall l : A -> A -> Prop, (@ordinal A l) = ((@woset A l) /\ (forall x : A, (@fld A l x) -> x = (@ε A (fun y : A => ~ (@properly A l y x))))).
Axiom thm_POSET_REFL : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> forall x : A, (@fld A l x) -> l x x.
Axiom thm_POSET_TRANS : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z.
Axiom thm_POSET_ANTISYM : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y.
Axiom thm_POSET_FLDEQ : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> forall x : A, (@fld A l x) = (l x x).
Axiom thm_WOSET_REFL : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, (@fld A l x) -> l x x.
Axiom thm_WOSET_TRANS : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, forall y : A, forall z : A, ((l x y) /\ (l y z)) -> l x z.
Axiom thm_WOSET_ANTISYM : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, forall y : A, ((l x y) /\ (l y x)) -> x = y.
Axiom thm_WOSET_TOTAL : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, forall y : A, ((@fld A l x) /\ (@fld A l y)) -> (l x y) \/ (l y x).
Axiom thm_WOSET_WELL : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall s : A -> Prop, ((forall x : A, (s x) -> @fld A l x) /\ (exists x : A, s x)) -> exists x : A, (s x) /\ (forall y : A, (s y) -> l x y).
Axiom thm_WOSET_FLDEQ : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, (@fld A l x) = (l x x).
Axiom thm_WOSET_TRANS_LESS : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, forall y : A, forall z : A, ((@properly A l x y) /\ (l y z)) -> @properly A l x z.
Axiom thm_PAIRED_EXT : forall {A B C : Type'}, forall l : A -> B -> C, forall m : A -> B -> C, (forall x : A, forall y : B, (l x y) = (m x y)) = (l = m).
Axiom thm_WOSET_TRANS_LE : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, forall y : A, forall z : A, ((l x y) /\ (@properly A l y z)) -> @properly A l x z.
Axiom thm_WOSET_WELL_CONTRAPOS : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall P : A -> Prop, ((forall x : A, (P x) -> @fld A l x) /\ (exists x : A, P x)) -> exists y : A, (P y) /\ (forall z : A, (@properly A l z y) -> ~ (P z)).
Axiom thm_WOSET_TOTAL_LE : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, forall y : A, ((@fld A l x) /\ (@fld A l y)) -> (l x y) \/ (@properly A l y x).
Axiom thm_WOSET_TOTAL_LT : forall {A : Type'}, forall l : A -> A -> Prop, (@woset A l) -> forall x : A, forall y : A, ((@fld A l x) /\ (@fld A l y)) -> (x = y) \/ ((@properly A l x y) \/ (@properly A l y x)).
Axiom thm_ORDINAL_IMP_WOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@ordinal A l) -> @woset A l.
Axiom thm_WOSET_FINITE_TOSET : forall {A : Type'}, forall l : A -> A -> Prop, ((@toset A l) /\ (@finite_set (prod A A) (@GSPEC (prod A A) (fun GEN_PVAR_396 : prod A A => exists x : A, exists y : A, @SETSPEC (prod A A) GEN_PVAR_396 (l x y) (@pair A A x y))))) -> @woset A l.
Axiom thm_UNION_FLD : forall {A : Type'} (x : A), forall P : (A -> A -> Prop) -> Prop, (@fld A (fun x' : A => fun y : A => exists l : A -> A -> Prop, (P l) /\ (l x' y)) x) = (exists l : A -> A -> Prop, (P l) /\ (@fld A l x)).
Axiom thm_UNION_INSEG : forall {A : Type'}, forall P : (A -> A -> Prop) -> Prop, forall l : A -> A -> Prop, (forall m : A -> A -> Prop, (P m) -> @inseg A m l) -> @inseg A (fun x : A => fun y : A => exists l' : A -> A -> Prop, (P l') /\ (l' x y)) l.
Axiom thm_INSEG_SUBSET : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, (@inseg A m l) -> forall x : A, forall y : A, (m x y) -> l x y.
Axiom thm_INSEG_SUBSET_FLD : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, (@inseg A m l) -> forall x : A, (@fld A m x) -> @fld A l x.
Axiom thm_INSEG_FLD_SUBSET : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, (@inseg A l m) -> @subset A (@fld A l) (@fld A m).
Axiom thm_INSEG_WOSET : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@inseg A m l) /\ (@woset A l)) -> @woset A m.
Axiom thm_INSEG_ORDINAL : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@inseg A m l) /\ (@ordinal A l)) -> @ordinal A m.
Axiom thm_LINSEG_INSEG : forall {A : Type'}, forall l : A -> A -> Prop, forall a : A, (@woset A l) -> @inseg A (@linseg A l a) l.
Axiom thm_LINSEG_WOSET : forall {A : Type'}, forall l : A -> A -> Prop, forall a : A, (@woset A l) -> @woset A (@linseg A l a).
Axiom thm_LINSEG_FLD : forall {A : Type'}, forall l : A -> A -> Prop, forall a : A, forall x : A, (@woset A l) -> (@fld A (@linseg A l a) x) = (@properly A l x a).
Axiom thm_INSEG_PROPER_SUBSET : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@inseg A m l) /\ (~ (l = m))) -> exists x : A, exists y : A, (l x y) /\ (~ (m x y)).
Axiom thm_INSEG_PROPER_SUBSET_FLD : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@inseg A m l) /\ (~ (l = m))) -> exists a : A, (@fld A l a) /\ (~ (@fld A m a)).
Axiom thm_INSEG_LINSEG : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, (@woset A l) -> (@inseg A m l) = ((m = l) \/ (exists a : A, (@fld A l a) /\ (m = (@linseg A l a)))).
Axiom thm_EXTEND_FLD : forall {A : Type'} (a : A), forall l : A -> A -> Prop, forall x : A, (@woset A l) -> (@fld A (fun x' : A => fun y : A => (l x' y) /\ (l y a)) x) = (l x a).
Axiom thm_EXTEND_INSEG : forall {A : Type'}, forall l : A -> A -> Prop, forall a : A, ((@woset A l) /\ (@fld A l a)) -> @inseg A (fun x : A => fun y : A => (l x y) /\ (l y a)) l.
Axiom thm_EXTEND_LINSEG : forall {A : Type'}, forall l : A -> A -> Prop, forall a : A, ((@woset A l) /\ (@fld A l a)) -> @inseg A (fun x : A => fun y : A => (@linseg A l a x y) \/ ((y = a) /\ ((@fld A (@linseg A l a) x) \/ (x = a)))) l.
Axiom thm_ORDINAL_CHAINED_LEMMA : forall {A : Type'}, forall k : A -> A -> Prop, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@ordinal A l) /\ (@ordinal A m)) -> ((@inseg A k l) /\ (@inseg A k m)) -> (k = l) \/ ((k = m) \/ (exists a : A, (@fld A l a) /\ ((@fld A m a) /\ ((k = (@linseg A l a)) /\ (k = (@linseg A m a)))))).
Axiom thm_ORDINAL_CHAINED : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@ordinal A l) /\ (@ordinal A m)) -> (@inseg A m l) \/ (@inseg A l m).
Axiom thm_ORDINAL_FLD_UNIQUE : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@ordinal A l) /\ ((@ordinal A m) /\ ((@fld A l) = (@fld A m)))) -> l = m.
Axiom thm_ORDINAL_FLD_SUBSET : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@ordinal A l) /\ ((@ordinal A m) /\ (@subset A (@fld A l) (@fld A m)))) -> @inseg A l m.
Axiom thm_ORDINAL_FLD_SUBSET_EQ : forall {A : Type'}, forall l : A -> A -> Prop, forall m : A -> A -> Prop, ((@ordinal A l) /\ (@ordinal A m)) -> (@subset A (@fld A l) (@fld A m)) = (@inseg A l m).
Axiom thm_FLD_SUC : forall {A : Type'} (x : A), forall l : A -> A -> Prop, forall a : A, (@fld A (fun x' : A => fun y : A => (l x' y) \/ ((y = a) /\ ((@fld A l x') \/ (x' = a)))) x) = ((@fld A l x) \/ (x = a)).
Axiom thm_ORDINAL_SUC : forall {A : Type'}, forall l : A -> A -> Prop, ((@ordinal A l) /\ (exists x : A, ~ (@fld A l x))) -> @ordinal A (fun x : A => fun y : A => (l x y) \/ ((y = (@ε A (fun y' : A => ~ (@fld A l y')))) /\ ((@fld A l x) \/ (x = (@ε A (fun y' : A => ~ (@fld A l y'))))))).
Axiom thm_ORDINAL_UNION : forall {A : Type'}, forall P : (A -> A -> Prop) -> Prop, (forall l : A -> A -> Prop, (P l) -> @ordinal A l) -> @ordinal A (fun x : A => fun y : A => exists l : A -> A -> Prop, (P l) /\ (l x y)).
Axiom thm_ORDINAL_UNION_LEMMA : forall {A : Type'}, forall l : A -> A -> Prop, forall x : A, (@ordinal A l) -> (@fld A l x) -> @fld A (fun a : A => fun b : A => exists l' : A -> A -> Prop, (@ordinal A l') /\ (l' a b)) x.
Axiom thm_ORDINAL_UP : forall {A : Type'}, forall l : A -> A -> Prop, (@ordinal A l) -> (forall x : A, @fld A l x) \/ (exists m : A -> A -> Prop, exists x : A, (@ordinal A m) /\ ((@fld A m x) /\ (~ (@fld A l x)))).
Axiom thm_WO_ORDINAL : forall {A : Type'}, exists l : A -> A -> Prop, (@ordinal A l) /\ (forall x : A, @fld A l x).
Axiom thm_FLD_RESTRICT : forall {A : Type'} (x : A), forall l : A -> A -> Prop, (@woset A l) -> forall P : A -> Prop, (@fld A (fun x' : A => fun y : A => (P x') /\ ((P y) /\ (l x' y))) x) = ((P x) /\ (@fld A l x)).
Axiom thm_WO : forall {A : Type'}, forall P : A -> Prop, exists l : A -> A -> Prop, (@woset A l) /\ ((@fld A l) = P).
Axiom thm_WF_INSEG_WOSET : forall {A : Type'}, @well_founded (A -> A -> Prop) (fun x : A -> A -> Prop => fun y : A -> A -> Prop => (@woset A x) /\ ((@woset A y) /\ ((@inseg A x y) /\ (~ (x = y))))).
Axiom thm_WOSET_INSEG_ORDINAL : forall {A : Type'}, @woset (A -> A -> Prop) (fun x : A -> A -> Prop => fun y : A -> A -> Prop => (@ordinal A x) /\ ((@ordinal A y) /\ (@inseg A x y))).
Axiom thm_SUBWOSET_ISO_INSEG : forall {A : Type'}, forall l : A -> A -> Prop, forall s : A -> Prop, ((@woset A l) /\ ((@fld A l) = (@setT A))) -> exists f : A -> A, (forall x : A, forall y : A, ((@IN A x s) /\ (@IN A y s)) -> (l (f x) (f y)) = (l x y)) /\ (forall x : A, forall y : A, ((@IN A y (@IMAGE A A f s)) /\ (l x y)) -> @IN A x (@IMAGE A A f s)).
Axiom thm_HP : forall {A : Type'}, forall l : A -> A -> Prop, (@qoset A l) -> exists P : A -> Prop, (@chain A l P) /\ (forall Q : A -> Prop, ((@chain A l Q) /\ (@subset A P Q)) -> Q = P).
Axiom thm_ZL_STRONG : forall {A : Type'}, forall l : A -> A -> Prop, ((@qoset A l) /\ (forall c : A -> Prop, (@chain A l c) -> exists y : A, (@IN A y (@fld A l)) /\ (forall x : A, (@IN A x c) -> l x y))) -> exists y : A, (@IN A y (@fld A l)) /\ (forall x : A, (l y x) -> l x y).
Axiom thm_ZL : forall {A : Type'}, forall l : A -> A -> Prop, ((@poset A l) /\ (forall P : A -> Prop, (@chain A l P) -> exists y : A, (@fld A l y) /\ (forall x : A, (P x) -> l x y))) -> exists y : A, (@fld A l y) /\ (forall x : A, (l y x) -> y = x).
Axiom thm_KL_POSET_LEMMA : forall {A : Type'} (C : A -> Prop) (l : A -> A -> Prop), @poset (A -> Prop) (fun c1 : A -> Prop => fun c2 : A -> Prop => (@subset A C c1) /\ ((@subset A c1 c2) /\ (@chain A l c2))).
Axiom thm_KL : forall {A : Type'}, forall l : A -> A -> Prop, (@poset A l) -> forall C : A -> Prop, (@chain A l C) -> exists P : A -> Prop, ((@chain A l P) /\ (@subset A C P)) /\ (forall R' : A -> Prop, ((@chain A l R') /\ (@subset A P R')) -> R' = P).
Axiom thm_POSET_RESTRICTED_SUBSET : forall {_175789 : Type'}, forall P : (_175789 -> Prop) -> Prop, @poset (_175789 -> Prop) (fun x : _175789 -> Prop => fun y : _175789 -> Prop => (P x) /\ ((P y) /\ (@subset _175789 x y))).
Axiom thm_FLD_RESTRICTED_SUBSET : forall {_175812 : Type'}, forall P : (_175812 -> Prop) -> Prop, (@fld (_175812 -> Prop) (fun x : _175812 -> Prop => fun y : _175812 -> Prop => (P x) /\ ((P y) /\ (@subset _175812 x y)))) = P.
Axiom thm_ZL_SUBSETS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall c : (A -> Prop) -> Prop, ((forall x : A -> Prop, (@IN (A -> Prop) x c) -> P x) /\ (forall x : A -> Prop, forall y : A -> Prop, ((@IN (A -> Prop) x c) /\ (@IN (A -> Prop) y c)) -> (@subset A x y) \/ (@subset A y x))) -> exists z : A -> Prop, (P z) /\ (forall x : A -> Prop, (@IN (A -> Prop) x c) -> @subset A x z)) -> exists a : A -> Prop, (P a) /\ (forall x : A -> Prop, ((P x) /\ (@subset A a x)) -> a = x).
Axiom thm_ZL_SUBSETS_UNIONS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall c : (A -> Prop) -> Prop, ((forall x : A -> Prop, (@IN (A -> Prop) x c) -> P x) /\ (forall x : A -> Prop, forall y : A -> Prop, ((@IN (A -> Prop) x c) /\ (@IN (A -> Prop) y c)) -> (@subset A x y) \/ (@subset A y x))) -> P (@UNIONS A c)) -> exists a : A -> Prop, (P a) /\ (forall x : A -> Prop, ((P x) /\ (@subset A a x)) -> a = x).
Axiom thm_ZL_SUBSETS_UNIONS_NONEMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((exists x : A -> Prop, P x) /\ (forall c : (A -> Prop) -> Prop, ((exists x : A -> Prop, @IN (A -> Prop) x c) /\ ((forall x : A -> Prop, (@IN (A -> Prop) x c) -> P x) /\ (forall x : A -> Prop, forall y : A -> Prop, ((@IN (A -> Prop) x c) /\ (@IN (A -> Prop) y c)) -> (@subset A x y) \/ (@subset A y x)))) -> P (@UNIONS A c))) -> exists a : A -> Prop, (P a) /\ (forall x : A -> Prop, ((P x) /\ (@subset A a x)) -> a = x).
Axiom thm_TUKEY : forall {A : Type'}, forall s : (A -> Prop) -> Prop, ((~ (s = (@set0 (A -> Prop)))) /\ (forall t : A -> Prop, (forall c : A -> Prop, ((@finite_set A c) /\ (@subset A c t)) -> @IN (A -> Prop) c s) = (@IN (A -> Prop) t s))) -> exists u : A -> Prop, (@IN (A -> Prop) u s) /\ (forall v : A -> Prop, ((@IN (A -> Prop) v s) /\ (@subset A u v)) -> u = v).
Axiom thm_OEP : forall {A : Type'}, forall p : A -> A -> Prop, (@poset A p) -> exists t : A -> A -> Prop, (@toset A t) /\ (((@fld A t) = (@fld A p)) /\ (forall x : A, forall y : A, (p x y) -> t x y)).
Axiom thm_TOSET_COFINAL_WOSET : forall {A : Type'}, forall l : A -> A -> Prop, (@toset A l) -> exists w : A -> A -> Prop, (forall x : A, forall y : A, (w x y) -> l x y) /\ ((@woset A w) /\ (forall x : A, (@IN A x (@fld A l)) -> exists y : A, (@IN A y (@fld A w)) /\ (l x y))).
Axiom thm_SYM_ALT : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> R' y x) = (forall x : A, forall y : A, (R' x y) = (R' y x)).
Axiom thm_TRANS_ALT : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, forall U : A -> A -> Prop, (forall x : A, forall z : A, (exists y : A, (R' x y) /\ (S' y z)) -> U x z) = (forall x : A, forall y : A, forall z : A, ((R' x y) /\ (S' y z)) -> U x z).
Axiom thm_RC_CASES : forall {A : Type'}, forall R' : A -> A -> Prop, forall a0 : A, forall a1 : A, (@RC A R' a0 a1) = ((R' a0 a1) \/ (a1 = a0)).
Axiom thm_RC_INDUCT : forall {A : Type'}, forall R' : A -> A -> Prop, forall RC' : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> RC' x y) /\ (forall x : A, RC' x x)) -> forall a0 : A, forall a1 : A, (@RC A R' a0 a1) -> RC' a0 a1.
Axiom thm_RC_RULES : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> @RC A R' x y) /\ (forall x : A, @RC A R' x x).
Axiom thm_RC_INC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (R' x y) -> @RC A R' x y.
Axiom thm_RC_REFL : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, @RC A R' x x.
Axiom thm_RC_EXPLICIT : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RC A R' x y) = ((R' x y) \/ (x = y)).
Axiom thm_RC_MONO : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> S' x y) -> forall x : A, forall y : A, (@RC A R' x y) -> @RC A S' x y.
Axiom thm_RC_CLOSED : forall {A : Type'}, forall R' : A -> A -> Prop, ((@RC A R') = R') = (forall x : A, R' x x).
Axiom thm_RC_IDEMP : forall {A : Type'}, forall R' : A -> A -> Prop, (@RC A (@RC A R')) = (@RC A R').
Axiom thm_RC_SYM : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> R' y x) -> forall x : A, forall y : A, (@RC A R' x y) -> @RC A R' y x.
Axiom thm_RC_TRANS : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, forall z : A, ((R' x y) /\ (R' y z)) -> R' x z) -> forall x : A, forall y : A, forall z : A, ((@RC A R' x y) /\ (@RC A R' y z)) -> @RC A R' x z.
Axiom thm_SC_CASES : forall {A : Type'}, forall R' : A -> A -> Prop, forall a0 : A, forall a1 : A, (@SC A R' a0 a1) = ((R' a0 a1) \/ (@SC A R' a1 a0)).
Axiom thm_SC_INDUCT : forall {A : Type'}, forall R' : A -> A -> Prop, forall SC' : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> SC' x y) /\ (forall x : A, forall y : A, (SC' x y) -> SC' y x)) -> forall a0 : A, forall a1 : A, (@SC A R' a0 a1) -> SC' a0 a1.
Axiom thm_SC_RULES : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> @SC A R' x y) /\ (forall x : A, forall y : A, (@SC A R' x y) -> @SC A R' y x).
Axiom thm_SC_INC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (R' x y) -> @SC A R' x y.
Axiom thm_SC_SYM : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@SC A R' x y) -> @SC A R' y x.
Axiom thm_SC_EXPLICIT : forall {A : Type'} (y : A) (x : A), forall R' : A -> A -> Prop, (@SC A R' x y) = ((R' x y) \/ (R' y x)).
Axiom thm_SC_MONO : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> S' x y) -> forall x : A, forall y : A, (@SC A R' x y) -> @SC A S' x y.
Axiom thm_SC_CLOSED : forall {A : Type'}, forall R' : A -> A -> Prop, ((@SC A R') = R') = (forall x : A, forall y : A, (R' x y) -> R' y x).
Axiom thm_SC_IDEMP : forall {A : Type'}, forall R' : A -> A -> Prop, (@SC A (@SC A R')) = (@SC A R').
Axiom thm_SC_REFL : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, R' x x) -> forall x : A, @SC A R' x x.
Axiom thm_TC_CASES : forall {A : Type'}, forall R' : A -> A -> Prop, forall a0 : A, forall a1 : A, (@Relation_Operators.clos_trans A R' a0 a1) = ((R' a0 a1) \/ (exists y : A, (@Relation_Operators.clos_trans A R' a0 y) /\ (@Relation_Operators.clos_trans A R' y a1))).
Axiom thm_TC_INDUCT : forall {A : Type'}, forall R' : A -> A -> Prop, forall TC' : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> TC' x y) /\ (forall x : A, forall y : A, forall z : A, ((TC' x y) /\ (TC' y z)) -> TC' x z)) -> forall a0 : A, forall a1 : A, (@Relation_Operators.clos_trans A R' a0 a1) -> TC' a0 a1.
Axiom thm_TC_RULES : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> @Relation_Operators.clos_trans A R' x y) /\ (forall x : A, forall y : A, forall z : A, ((@Relation_Operators.clos_trans A R' x y) /\ (@Relation_Operators.clos_trans A R' y z)) -> @Relation_Operators.clos_trans A R' x z).
Axiom thm_TC_INC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (R' x y) -> @Relation_Operators.clos_trans A R' x y.
Axiom thm_TC_TRANS : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@Relation_Operators.clos_trans A R' x y) /\ (@Relation_Operators.clos_trans A R' y z)) -> @Relation_Operators.clos_trans A R' x z.
Axiom thm_TC_MONO : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> S' x y) -> forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) -> @Relation_Operators.clos_trans A S' x y.
Axiom thm_TC_CLOSED : forall {A : Type'}, forall R' : A -> A -> Prop, ((@Relation_Operators.clos_trans A R') = R') = (forall x : A, forall y : A, forall z : A, ((R' x y) /\ (R' y z)) -> R' x z).
Axiom thm_TC_IDEMP : forall {A : Type'}, forall R' : A -> A -> Prop, (@Relation_Operators.clos_trans A (@Relation_Operators.clos_trans A R')) = (@Relation_Operators.clos_trans A R').
Axiom thm_TC_REFL : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, R' x x) -> forall x : A, @Relation_Operators.clos_trans A R' x x.
Axiom thm_TC_SYM : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> R' y x) -> forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) -> @Relation_Operators.clos_trans A R' y x.
Axiom thm_RC_SC : forall {A : Type'}, forall R' : A -> A -> Prop, (@RC A (@SC A R')) = (@SC A (@RC A R')).
Axiom thm_SC_RC : forall {A : Type'}, forall R' : A -> A -> Prop, (@SC A (@RC A R')) = (@RC A (@SC A R')).
Axiom thm_RC_TC : forall {A : Type'}, forall R' : A -> A -> Prop, (@RC A (@Relation_Operators.clos_trans A R')) = (@Relation_Operators.clos_trans A (@RC A R')).
Axiom thm_TC_RC : forall {A : Type'}, forall R' : A -> A -> Prop, (@Relation_Operators.clos_trans A (@RC A R')) = (@RC A (@Relation_Operators.clos_trans A R')).
Axiom thm_TC_SC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@SC A (@Relation_Operators.clos_trans A R') x y) -> @Relation_Operators.clos_trans A (@SC A R') x y.
Axiom thm_SC_TC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@SC A (@Relation_Operators.clos_trans A R') x y) -> @Relation_Operators.clos_trans A (@SC A R') x y.
Axiom thm_TC_TRANS_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@Relation_Operators.clos_trans A R' x y) /\ (R' y z)) -> @Relation_Operators.clos_trans A R' x z.
Axiom thm_TC_TRANS_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((R' x y) /\ (@Relation_Operators.clos_trans A R' y z)) -> @Relation_Operators.clos_trans A R' x z.
Axiom thm_TC_CASES_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@Relation_Operators.clos_trans A R' x z) = ((R' x z) \/ (exists y : A, (@Relation_Operators.clos_trans A R' x y) /\ (R' y z))).
Axiom thm_TC_CASES_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@Relation_Operators.clos_trans A R' x z) = ((R' x z) \/ (exists y : A, (R' x y) /\ (@Relation_Operators.clos_trans A R' y z))).
Axiom thm_TC_INDUCT_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> P x y) /\ (forall x : A, forall y : A, forall z : A, ((P x y) /\ (R' y z)) -> P x z)) -> forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) -> P x y.
Axiom thm_TC_INDUCT_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> P x y) /\ (forall x : A, forall z : A, (exists y : A, (R' x y) /\ (P y z)) -> P x z)) -> forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) -> P x y.
Axiom thm_WF_TC : forall {A : Type'}, forall R' : A -> A -> Prop, (@well_founded A (@Relation_Operators.clos_trans A R')) = (@well_founded A R').
Axiom thm_RSC : forall {A : Type'}, forall R' : A -> A -> Prop, (@RSC A R') = (@RC A (@SC A R')).
Axiom thm_RSC_INC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (R' x y) -> @RSC A R' x y.
Axiom thm_RSC_REFL : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, @RSC A R' x x.
Axiom thm_RSC_SYM : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RSC A R' x y) -> @RSC A R' y x.
Axiom thm_RSC_CASES : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RSC A R' x y) = ((x = y) \/ ((R' x y) \/ (R' y x))).
Axiom thm_RSC_INDUCT : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> P x y) /\ ((forall x : A, P x x) /\ (forall x : A, forall y : A, (P x y) -> P y x))) -> forall x : A, forall y : A, (@RSC A R' x y) -> P x y.
Axiom thm_RSC_MONO : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> S' x y) -> forall x : A, forall y : A, (@RSC A R' x y) -> @RSC A S' x y.
Axiom thm_RSC_CLOSED : forall {A : Type'}, forall R' : A -> A -> Prop, ((@RSC A R') = R') = ((forall x : A, R' x x) /\ (forall x : A, forall y : A, (R' x y) -> R' y x)).
Axiom thm_RSC_IDEMP : forall {A : Type'}, forall R' : A -> A -> Prop, (@RSC A (@RSC A R')) = (@RSC A R').
Axiom thm_RTC : forall {A : Type'}, forall R' : A -> A -> Prop, (@RTC A R') = (@RC A (@Relation_Operators.clos_trans A R')).
Axiom thm_RTC_INC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (R' x y) -> @RTC A R' x y.
Axiom thm_RTC_REFL : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, @RTC A R' x x.
Axiom thm_RTC_TRANS : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@RTC A R' x y) /\ (@RTC A R' y z)) -> @RTC A R' x z.
Axiom thm_RTC_RULES : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> @RTC A R' x y) /\ ((forall x : A, @RTC A R' x x) /\ (forall x : A, forall y : A, forall z : A, ((@RTC A R' x y) /\ (@RTC A R' y z)) -> @RTC A R' x z)).
Axiom thm_RTC_TRANS_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@RTC A R' x y) /\ (R' y z)) -> @RTC A R' x z.
Axiom thm_RTC_TRANS_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((R' x y) /\ (@RTC A R' y z)) -> @RTC A R' x z.
Axiom thm_RTC_CASES : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@RTC A R' x z) = ((x = z) \/ (exists y : A, (@RTC A R' x y) /\ (@RTC A R' y z))).
Axiom thm_RTC_CASES_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@RTC A R' x z) = ((x = z) \/ (exists y : A, (@RTC A R' x y) /\ (R' y z))).
Axiom thm_RTC_CASES_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@RTC A R' x z) = ((x = z) \/ (exists y : A, (R' x y) /\ (@RTC A R' y z))).
Axiom thm_RTC_INDUCT : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> P x y) /\ ((forall x : A, P x x) /\ (forall x : A, forall y : A, forall z : A, ((P x y) /\ (P y z)) -> P x z))) -> forall x : A, forall y : A, (@RTC A R' x y) -> P x y.
Axiom thm_RTC_INDUCT_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, P x x) /\ (forall x : A, forall y : A, forall z : A, ((P x y) /\ (R' y z)) -> P x z)) -> forall x : A, forall y : A, (@RTC A R' x y) -> P x y.
Axiom thm_RTC_INDUCT_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, P x x) /\ (forall x : A, forall y : A, forall z : A, ((R' x y) /\ (P y z)) -> P x z)) -> forall x : A, forall y : A, (@RTC A R' x y) -> P x y.
Axiom thm_RTC_MONO : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> S' x y) -> forall x : A, forall y : A, (@RTC A R' x y) -> @RTC A S' x y.
Axiom thm_RTC_CLOSED : forall {A : Type'}, forall R' : A -> A -> Prop, ((@RTC A R') = R') = ((forall x : A, R' x x) /\ (forall x : A, forall y : A, forall z : A, ((R' x y) /\ (R' y z)) -> R' x z)).
Axiom thm_RTC_IDEMP : forall {A : Type'}, forall R' : A -> A -> Prop, (@RTC A (@RTC A R')) = (@RTC A R').
Axiom thm_RTC_SYM : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> R' y x) -> forall x : A, forall y : A, (@RTC A R' x y) -> @RTC A R' y x.
Axiom thm_RTC_STUTTER : forall {_179314 : Type'} (R' : _179314 -> _179314 -> Prop), (@RTC _179314 R') = (@RTC _179314 (fun x : _179314 => fun y : _179314 => (R' x y) /\ (~ (x = y)))).
Axiom thm_TC_RTC_CASES_L : forall {_179334 : Type'} (x : _179334) (R' : _179334 -> _179334 -> Prop) (z : _179334), (@Relation_Operators.clos_trans _179334 R' x z) = (exists y : _179334, (@RTC _179334 R' x y) /\ (R' y z)).
Axiom thm_TC_RTC_CASES_R : forall {_179361 : Type'}, forall R' : _179361 -> _179361 -> Prop, forall x : _179361, forall z : _179361, (@Relation_Operators.clos_trans _179361 R' x z) = (exists y : _179361, (R' x y) /\ (@RTC _179361 R' y z)).
Axiom thm_TC_TC_RTC_CASES : forall {_179382 : Type'}, forall R' : _179382 -> _179382 -> Prop, forall x : _179382, forall z : _179382, (@Relation_Operators.clos_trans _179382 R' x z) = (exists y : _179382, (@Relation_Operators.clos_trans _179382 R' x y) /\ (@RTC _179382 R' y z)).
Axiom thm_TC_RTC_TC_CASES : forall {_179415 : Type'}, forall R' : _179415 -> _179415 -> Prop, forall x : _179415, forall z : _179415, (@Relation_Operators.clos_trans _179415 R' x z) = (exists y : _179415, (@RTC _179415 R' x y) /\ (@Relation_Operators.clos_trans _179415 R' y z)).
Axiom thm_RTC_NE_IMP_TC : forall {_179455 : Type'}, forall R' : _179455 -> _179455 -> Prop, forall x : _179455, forall y : _179455, ((@RTC _179455 R' x y) /\ (~ (x = y))) -> @Relation_Operators.clos_trans _179455 R' x y.
Axiom thm_STC : forall {A : Type'}, forall R' : A -> A -> Prop, (@STC A R') = (@Relation_Operators.clos_trans A (@SC A R')).
Axiom thm_STC_INC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (R' x y) -> @STC A R' x y.
Axiom thm_STC_SYM : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@STC A R' x y) -> @STC A R' y x.
Axiom thm_STC_TRANS : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@STC A R' x y) /\ (@STC A R' y z)) -> @STC A R' x z.
Axiom thm_STC_TRANS_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@STC A R' x y) /\ (R' y z)) -> @STC A R' x z.
Axiom thm_STC_TRANS_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((R' x y) /\ (@STC A R' y z)) -> @STC A R' x z.
Axiom thm_STC_CASES : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@STC A R' x z) = ((R' x z) \/ ((@STC A R' z x) \/ (exists y : A, (@STC A R' x y) /\ (@STC A R' y z)))).
Axiom thm_STC_CASES_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@STC A R' x z) = ((R' x z) \/ ((@STC A R' z x) \/ (exists y : A, (@STC A R' x y) /\ (R' y z)))).
Axiom thm_STC_CASES_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@STC A R' x z) = ((R' x z) \/ ((@STC A R' z x) \/ (exists y : A, (R' x y) /\ (@STC A R' y z)))).
Axiom thm_STC_INDUCT : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> P x y) /\ ((forall x : A, forall y : A, (P x y) -> P y x) /\ (forall x : A, forall y : A, forall z : A, ((P x y) /\ (P y z)) -> P x z))) -> forall x : A, forall y : A, (@STC A R' x y) -> P x y.
Axiom thm_STC_MONO : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> S' x y) -> forall x : A, forall y : A, (@STC A R' x y) -> @STC A S' x y.
Axiom thm_STC_CLOSED : forall {A : Type'}, forall R' : A -> A -> Prop, ((@STC A R') = R') = ((forall x : A, forall y : A, (R' x y) -> R' y x) /\ (forall x : A, forall y : A, forall z : A, ((R' x y) /\ (R' y z)) -> R' x z)).
Axiom thm_STC_IDEMP : forall {A : Type'}, forall R' : A -> A -> Prop, (@STC A (@STC A R')) = (@STC A R').
Axiom thm_STC_REFL : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, R' x x) -> forall x : A, @STC A R' x x.
Axiom thm_RSTC : forall {A : Type'}, forall R' : A -> A -> Prop, (@RSTC A R') = (@RC A (@Relation_Operators.clos_trans A (@SC A R'))).
Axiom thm_RSTC_INC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (R' x y) -> @RSTC A R' x y.
Axiom thm_RSTC_REFL : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, @RSTC A R' x x.
Axiom thm_RSTC_SYM : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RSTC A R' x y) -> @RSTC A R' y x.
Axiom thm_RSTC_TRANS : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@RSTC A R' x y) /\ (@RSTC A R' y z)) -> @RSTC A R' x z.
Axiom thm_RSTC_RULES : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> @RSTC A R' x y) /\ ((forall x : A, @RSTC A R' x x) /\ ((forall x : A, forall y : A, (@RSTC A R' x y) -> @RSTC A R' y x) /\ (forall x : A, forall y : A, forall z : A, ((@RSTC A R' x y) /\ (@RSTC A R' y z)) -> @RSTC A R' x z))).
Axiom thm_RSTC_TRANS_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((@RSTC A R' x y) /\ (R' y z)) -> @RSTC A R' x z.
Axiom thm_RSTC_TRANS_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall z : A, ((R' x y) /\ (@RSTC A R' y z)) -> @RSTC A R' x z.
Axiom thm_RSTC_CASES : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@RSTC A R' x z) = ((x = z) \/ ((R' x z) \/ ((@RSTC A R' z x) \/ (exists y : A, (@RSTC A R' x y) /\ (@RSTC A R' y z))))).
Axiom thm_RSTC_CASES_L : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@RSTC A R' x z) = ((x = z) \/ ((R' x z) \/ ((@RSTC A R' z x) \/ (exists y : A, (@RSTC A R' x y) /\ (R' y z))))).
Axiom thm_RSTC_CASES_R : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall z : A, (@RSTC A R' x z) = ((x = z) \/ ((R' x z) \/ ((@RSTC A R' z x) \/ (exists y : A, (R' x y) /\ (@RSTC A R' y z))))).
Axiom thm_RSTC_INDUCT : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (R' x y) -> P x y) /\ ((forall x : A, P x x) /\ ((forall x : A, forall y : A, (P x y) -> P y x) /\ (forall x : A, forall y : A, forall z : A, ((P x y) /\ (P y z)) -> P x z)))) -> forall x : A, forall y : A, (@RSTC A R' x y) -> P x y.
Axiom thm_RSTC_MONO : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y : A, (R' x y) -> S' x y) -> forall x : A, forall y : A, (@RSTC A R' x y) -> @RSTC A S' x y.
Axiom thm_RSTC_CLOSED : forall {A : Type'}, forall R' : A -> A -> Prop, ((@RSTC A R') = R') = ((forall x : A, R' x x) /\ ((forall x : A, forall y : A, (R' x y) -> R' y x) /\ (forall x : A, forall y : A, forall z : A, ((R' x y) /\ (R' y z)) -> R' x z))).
Axiom thm_RSTC_IDEMP : forall {A : Type'}, forall R' : A -> A -> Prop, (@RSTC A (@RSTC A R')) = (@RSTC A R').
Axiom thm_RSC_INC_RC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RC A R' x y) -> @RSC A R' x y.
Axiom thm_RSC_INC_SC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@SC A R' x y) -> @RSC A R' x y.
Axiom thm_RTC_INC_RC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RC A R' x y) -> @RTC A R' x y.
Axiom thm_RTC_INC_TC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) -> @RTC A R' x y.
Axiom thm_STC_INC_SC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@SC A R' x y) -> @STC A R' x y.
Axiom thm_STC_INC_TC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) -> @STC A R' x y.
Axiom thm_RSTC_INC_RC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RC A R' x y) -> @RSTC A R' x y.
Axiom thm_RSTC_INC_SC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@SC A R' x y) -> @RSTC A R' x y.
Axiom thm_RSTC_INC_TC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) -> @RSTC A R' x y.
Axiom thm_RSTC_INC_RSC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RSC A R' x y) -> @RSTC A R' x y.
Axiom thm_RSTC_INC_RTC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RTC A R' x y) -> @RSTC A R' x y.
Axiom thm_RSTC_INC_STC : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@STC A R' x y) -> @RSTC A R' x y.
Axiom thm_INV : forall {A B : Type'}, forall R' : B -> A -> Prop, forall y : B, forall x : A, (@INV A B R' x y) = (R' y x).
Axiom thm_RC_INV : forall {_180829 : Type'} (R' : _180829 -> _180829 -> Prop), (@RC _180829 (@INV _180829 _180829 R')) = (@INV _180829 _180829 (@RC _180829 R')).
Axiom thm_SC_INV : forall {_180843 : Type'} (R' : _180843 -> _180843 -> Prop), (@SC _180843 (@INV _180843 _180843 R')) = (@INV _180843 _180843 (@SC _180843 R')).
Axiom thm_SC_INV_STRONG : forall {_180854 : Type'} (R' : _180854 -> _180854 -> Prop), (@SC _180854 (@INV _180854 _180854 R')) = (@SC _180854 R').
Axiom thm_TC_INV : forall {_180868 : Type'} (R' : _180868 -> _180868 -> Prop), (@Relation_Operators.clos_trans _180868 (@INV _180868 _180868 R')) = (@INV _180868 _180868 (@Relation_Operators.clos_trans _180868 R')).
Axiom thm_RSC_INV : forall {_180882 : Type'} (R' : _180882 -> _180882 -> Prop), (@RSC _180882 (@INV _180882 _180882 R')) = (@INV _180882 _180882 (@RSC _180882 R')).
Axiom thm_RTC_INV : forall {_180896 : Type'} (R' : _180896 -> _180896 -> Prop), (@RTC _180896 (@INV _180896 _180896 R')) = (@INV _180896 _180896 (@RTC _180896 R')).
Axiom thm_STC_INV : forall {_180910 : Type'} (R' : _180910 -> _180910 -> Prop), (@STC _180910 (@INV _180910 _180910 R')) = (@INV _180910 _180910 (@STC _180910 R')).
Axiom thm_RSTC_INV : forall {_180924 : Type'} (R' : _180924 -> _180924 -> Prop), (@RSTC _180924 (@INV _180924 _180924 R')) = (@INV _180924 _180924 (@RSTC _180924 R')).
Axiom thm_RELPOW : forall {A : Type'} (n : N) (x : A) (R' : A -> A -> Prop) (y : A), ((@RELPOW A N0 R' x y) = (x = y)) /\ ((@RELPOW A (N.succ n) R' x y) = (exists z : A, (@RELPOW A n R' x z) /\ (R' z y))).
Axiom thm_RELPOW_R : forall {A : Type'} (x : A) (n : N) (R' : A -> A -> Prop) (y : A), ((@RELPOW A N0 R' x y) = (x = y)) /\ ((@RELPOW A (N.succ n) R' x y) = (exists z : A, (R' x z) /\ (@RELPOW A n R' z y))).
Axiom thm_RELPOW_M : forall {A : Type'} (R' : A -> A -> Prop), forall m : N, forall n : N, forall x : A, forall y : A, (@RELPOW A (N.add m n) R' x y) = (exists z : A, (@RELPOW A m R' x z) /\ (@RELPOW A n R' z y)).
Axiom thm_RTC_RELPOW : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@RTC A R' x y) = (exists n : N, @RELPOW A n R' x y).
Axiom thm_TC_RELPOW : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, (@Relation_Operators.clos_trans A R' x y) = (exists n : N, @RELPOW A (N.succ n) R' x y).
Axiom thm_RELPOW_SEQUENCE : forall {A : Type'}, forall R' : A -> A -> Prop, forall n : N, forall x : A, forall y : A, (@RELPOW A n R' x y) = (exists f : N -> A, ((f N0) = x) /\ (((f n) = y) /\ (forall i : N, (N.lt i n) -> R' (f i) (f (N.succ i))))).
Axiom thm_fld : forall {_181223 : Type'}, forall R' : _181223 -> _181223 -> Prop, (@fld _181223 R') = (@GSPEC _181223 (fun GEN_PVAR_406 : _181223 => exists x : _181223, @SETSPEC _181223 GEN_PVAR_406 (exists y : _181223, (R' x y) \/ (R' y x)) x)).
Axiom thm_NORMAL : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, (@NORMAL A R' x) = (~ (exists y : A, R' x y)).
Axiom thm_CR : forall {A : Type'}, forall R' : A -> A -> Prop, (@CR A R') = (forall x : A, forall y1 : A, forall y2 : A, ((R' x y1) /\ (R' x y2)) -> exists z : A, (R' y1 z) /\ (R' y2 z)).
Axiom thm_WCR : forall {A : Type'}, forall R' : A -> A -> Prop, (@WCR A R') = (forall x : A, forall y1 : A, forall y2 : A, ((R' x y1) /\ (R' x y2)) -> exists z : A, (@RTC A R' y1 z) /\ (@RTC A R' y2 z)).
Axiom thm_WN : forall {A : Type'}, forall R' : A -> A -> Prop, (@WN A R') = (forall x : A, exists y : A, (@RTC A R' x y) /\ (@NORMAL A R' y)).
Axiom thm_SN : forall {A : Type'}, forall R' : A -> A -> Prop, (@SN A R') = (~ (exists seq : N -> A, forall n : N, R' (seq n) (seq (N.succ n)))).
Axiom thm_TREE : forall {A : Type'}, forall R' : A -> A -> Prop, (@TREE A R') = ((forall y : A, ~ (@Relation_Operators.clos_trans A R' y y)) /\ (exists a : A, (@IN A a (@fld A R')) /\ (forall y : A, (@IN A y (@fld A R')) -> (y = a) \/ ((@Relation_Operators.clos_trans A R' a y) /\ (@ex1 A (fun x : A => R' x y)))))).
Axiom thm_LF : forall {A : Type'}, forall R' : A -> A -> Prop, (@LF A R') = (forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_407 : A => exists y : A, @SETSPEC A GEN_PVAR_407 (R' x y) y))).
Axiom thm_SN_WF : forall {A : Type'}, forall R' : A -> A -> Prop, (@SN A R') = (@well_founded A (@INV A A R')).
Axiom thm_SN_PRESERVE : forall {A : Type'}, forall R' : A -> A -> Prop, (@SN A R') = (forall P : A -> Prop, (forall x : A, (P x) -> exists y : A, (P y) /\ (R' x y)) -> ~ (exists x : A, P x)).
Axiom thm_SN_NOETHERIAN : forall {A : Type'}, forall R' : A -> A -> Prop, (@SN A R') = (forall P : A -> Prop, (forall x : A, (forall y : A, (R' x y) -> P y) -> P x) -> forall x : A, P x).
Axiom thm_NORMAL_TC : forall {A : Type'} (x : A), forall R' : A -> A -> Prop, (@NORMAL A (@Relation_Operators.clos_trans A R') x) = (@NORMAL A R' x).
Axiom thm_NORMAL_RTC : forall {A : Type'} (x : A), forall R' : A -> A -> Prop, (@NORMAL A R' x) -> forall y : A, (@RTC A R' x y) = (x = y).
Axiom thm_WN_TC : forall {A : Type'}, forall R' : A -> A -> Prop, (@WN A (@Relation_Operators.clos_trans A R')) = (@WN A R').
Axiom thm_SN_TC : forall {A : Type'}, forall R' : A -> A -> Prop, (@SN A (@Relation_Operators.clos_trans A R')) = (@SN A R').
Axiom thm_SN_WN : forall {A : Type'}, forall R' : A -> A -> Prop, (@SN A R') -> @WN A R'.
Axiom thm_RC_CR : forall {A : Type'}, forall R' : A -> A -> Prop, (@CR A R') -> @CR A (@RC A R').
Axiom thm_STRIP_LEMMA : forall {A : Type'}, forall R' : A -> A -> Prop, forall S' : A -> A -> Prop, (forall x : A, forall y1 : A, forall y2 : A, ((R' x y1) /\ (S' x y2)) -> exists z : A, (S' y1 z) /\ (R' y2 z)) -> forall x : A, forall y1 : A, forall y2 : A, ((@Relation_Operators.clos_trans A R' x y1) /\ (S' x y2)) -> exists z : A, (S' y1 z) /\ (@Relation_Operators.clos_trans A R' y2 z).
Axiom thm_TC_CR : forall {A : Type'}, forall R' : A -> A -> Prop, (@CR A R') -> @CR A (@Relation_Operators.clos_trans A R').
Axiom thm_RTC_CR : forall {A : Type'}, forall R' : A -> A -> Prop, (@CR A R') -> @CR A (@RTC A R').
Axiom thm_STC_CR : forall {A : Type'}, forall R' : A -> A -> Prop, (@CR A (@RTC A R')) = (forall x : A, forall y : A, (@RSTC A R' x y) -> exists z : A, (@RTC A R' x z) /\ (@RTC A R' y z)).
Axiom thm_NORM_CR : forall {A : Type'}, forall R' : A -> A -> Prop, (@WN A R') -> (@CR A (@RTC A R')) = (forall x : A, forall y1 : A, forall y2 : A, ((@RTC A R' x y1) /\ ((@NORMAL A R' y1) /\ ((@RTC A R' x y2) /\ (@NORMAL A R' y2)))) -> y1 = y2).
Axiom thm_CR_NORM : forall {A : Type'}, forall R' : A -> A -> Prop, ((@WN A R') /\ (@CR A (@RTC A R'))) = (forall x : A, @ex1 A (fun y : A => (@RTC A R' x y) /\ (@NORMAL A R' y))).
Axiom thm_NEWMAN_LEMMA : forall {A : Type'}, forall R' : A -> A -> Prop, ((@SN A R') /\ (@WCR A R')) -> @CR A (@RTC A R').
Axiom thm_LF_TC_FINITE : forall {A : Type'}, forall R' : A -> A -> Prop, ((@LF A R') /\ (@SN A R')) -> forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_414 : A => exists y : A, @SETSPEC A GEN_PVAR_414 (@Relation_Operators.clos_trans A R' x y) y)).
Axiom thm_SN_NOLOOP : forall {A : Type'}, forall R' : A -> A -> Prop, (@SN A R') -> forall z : A, ~ (@Relation_Operators.clos_trans A R' z z).
Axiom thm_RELPOW_RTC : forall {A : Type'}, forall R' : A -> A -> Prop, forall n : N, forall x : A, forall y : A, (@RELPOW A n R' x y) -> @RTC A R' x y.
Axiom thm_RTC_TC_LEMMA : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, (@GSPEC A (fun GEN_PVAR_415 : A => exists y : A, @SETSPEC A GEN_PVAR_415 (@RTC A R' x y) y)) = (@INSERT A x (@GSPEC A (fun GEN_PVAR_416 : A => exists y : A, @SETSPEC A GEN_PVAR_416 (@Relation_Operators.clos_trans A R' x y) y))).
Axiom thm_HAS_SIZE_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : N, forall n : N, ((@HAS_SIZE A s m) /\ ((@HAS_SIZE A t n) /\ (@subset A s t))) -> N.le m n.
Axiom thm_FC_FINITE_BOUND_LEMMA : forall {A : Type'} (x : A), forall R' : A -> A -> Prop, (forall z : A, ~ (@Relation_Operators.clos_trans A R' z z)) -> forall n : N, (@HAS_SIZE A (@GSPEC A (fun GEN_PVAR_426 : A => exists y : A, @SETSPEC A GEN_PVAR_426 (@RTC A R' x y) y)) n) -> forall m : N, forall y : A, (@RELPOW A m R' x y) -> N.le m n.
Axiom thm_FC_FINITE_BOUND : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, ((@finite_set A (@GSPEC A (fun GEN_PVAR_428 : A => exists y : A, @SETSPEC A GEN_PVAR_428 (@RTC A R' x y) y))) /\ (forall z : A, ~ (@Relation_Operators.clos_trans A R' z z))) -> exists N' : N, forall n : N, forall y : A, (@RELPOW A n R' x y) -> N.le n N'.
Axiom thm_BOUND_SN : forall {A : Type'}, forall R' : A -> A -> Prop, (forall x : A, exists N' : N, forall n : N, forall y : A, (@RELPOW A n R' x y) -> N.le n N') -> @SN A R'.
Axiom thm_LF_SN_BOUND : forall {A : Type'}, forall R' : A -> A -> Prop, (@LF A R') -> (@SN A R') = (forall x : A, exists N' : N, forall n : N, forall y : A, (@RELPOW A n R' x y) -> N.le n N').
Axiom thm_TREE_FLD : forall {A : Type'}, forall R' : A -> A -> Prop, (@TREE A R') -> exists a : A, (@fld A R') = (@GSPEC A (fun GEN_PVAR_429 : A => exists y : A, @SETSPEC A GEN_PVAR_429 (@RTC A R' a y) y)).
Axiom thm_KOENIG_LEMMA : forall {A : Type'}, forall R' : A -> A -> Prop, ((@TREE A R') /\ ((@LF A R') /\ (@SN A R'))) -> @finite_set A (@fld A R').
Axiom thm_JOINABLE : forall {_182791 : Type'}, forall s : _182791, forall R' : _182791 -> _182791 -> Prop, forall t : _182791, (@JOINABLE _182791 R' s t) = (exists u : _182791, (@RTC _182791 R' s u) /\ (@RTC _182791 R' t u)).
Axiom thm_JOINABLE_REFL : forall {_182808 : Type'}, forall R' : _182808 -> _182808 -> Prop, forall t : _182808, @JOINABLE _182808 R' t t.
Axiom thm_JOINABLE_SYM : forall {_182827 : Type'}, forall R' : _182827 -> _182827 -> Prop, forall s : _182827, forall t : _182827, (@JOINABLE _182827 R' s t) = (@JOINABLE _182827 R' t s).
Axiom thm_JOINABLE_TRANS_R : forall {_182856 : Type'}, forall R' : _182856 -> _182856 -> Prop, forall s : _182856, forall t : _182856, forall u : _182856, ((R' s t) /\ (@JOINABLE _182856 R' t u)) -> @JOINABLE _182856 R' s u.
Axiom thm_CR_RSTC_JOINABLE : forall {A : Type'}, forall R' : A -> A -> Prop, (@CR A (@RTC A R')) -> forall x : A, forall y : A, (@RSTC A R' x y) = (@JOINABLE A R' x y).
Axiom thm_JOINABLE_TRANS : forall {_182905 : Type'}, forall R' : _182905 -> _182905 -> Prop, (@CR _182905 (@RTC _182905 R')) = (forall x : _182905, forall y : _182905, forall z : _182905, ((@JOINABLE _182905 R' x y) /\ (@JOINABLE _182905 R' y z)) -> @JOINABLE _182905 R' x z).
Axiom thm_EMPTY_IS_FINITE : forall {_182944 : Type'}, forall s : _182944 -> Prop, (s = (@set0 _182944)) -> @finite_set _182944 s.
Axiom thm_SING_IS_FINITE : forall {_182964 : Type'}, forall s : _182964 -> Prop, forall a : _182964, (s = (@INSERT _182964 a (@set0 _182964))) -> @finite_set _182964 s.
Axiom thm_UNION_NONZERO : forall {_183028 : Type'} (f : _183028 -> N) (g : _183028 -> N), (@GSPEC _183028 (fun GEN_PVAR_430 : _183028 => exists a : _183028, @SETSPEC _183028 GEN_PVAR_430 (~ ((N.add (f a) (g a)) = N0)) a)) = (@setU _183028 (@GSPEC _183028 (fun GEN_PVAR_431 : _183028 => exists a : _183028, @SETSPEC _183028 GEN_PVAR_431 (~ ((f a) = N0)) a)) (@GSPEC _183028 (fun GEN_PVAR_432 : _183028 => exists a : _183028, @SETSPEC _183028 GEN_PVAR_432 (~ ((g a) = N0)) a))).
Axiom thm_multiset_tybij_th : forall {A : Type'}, exists f : A -> N, @finite_set A (@GSPEC A (fun GEN_PVAR_433 : A => exists a : A, @SETSPEC A GEN_PVAR_433 (~ ((f a) = N0)) a)).
Axiom thm_mempty : forall {_183063 : Type'}, (@mempty _183063) = (@multiset _183063 (fun b : _183063 => N0)).
Axiom thm_mmember : forall {_183073 : Type'}, forall M : Multiset _183073, forall a : _183073, (@mmember _183073 a M) = (~ ((@multiplicity _183073 M a) = N0)).
Axiom thm_msing : forall {_183089 : Type'}, forall a : _183089, (@msing _183089 a) = (@multiset _183089 (fun b : _183089 => @COND N (b = a) ((BIT1 N0)) N0)).
Axiom thm_munion : forall {_183108 : Type'}, forall M : Multiset _183108, forall N' : Multiset _183108, (@munion _183108 M N') = (@multiset _183108 (fun b : _183108 => N.add (@multiplicity _183108 M b) (@multiplicity _183108 N' b))).
Axiom thm_mdiff : forall {_183127 : Type'}, forall M : Multiset _183127, forall N' : Multiset _183127, (@mdiff _183127 M N') = (@multiset _183127 (fun b : _183127 => N.sub (@multiplicity _183127 M b) (@multiplicity _183127 N' b))).
Axiom thm_MEXTENSION : forall {_183144 : Type'} (M : Multiset _183144) (N' : Multiset _183144), (M = N') = (forall a : _183144, (@multiplicity _183144 M a) = (@multiplicity _183144 N' a)).
Axiom thm_MULTIPLICITY_MULTISET : forall {_183177 : Type'} (f : _183177 -> N) (a : _183177) (y : N), ((@finite_set _183177 (@GSPEC _183177 (fun GEN_PVAR_434 : _183177 => exists a' : _183177, @SETSPEC _183177 GEN_PVAR_434 (~ ((f a') = N0)) a'))) /\ ((f a) = y)) -> (@multiplicity _183177 (@multiset _183177 f) a) = y.
Axiom thm_MEMPTY : forall {_183193 : Type'} (a : _183193), (@multiplicity _183193 (@mempty _183193) a) = N0.
Axiom thm_MSING : forall {A : Type'} (b : A) (a : A), (@multiplicity A (@msing A a) b) = (@COND N (b = a) ((BIT1 N0)) N0).
Axiom thm_MUNION : forall {_183220 : Type'} (M : Multiset _183220) (N' : Multiset _183220) (a : _183220), (@multiplicity _183220 (@munion _183220 M N') a) = (N.add (@multiplicity _183220 M a) (@multiplicity _183220 N' a)).
Axiom thm_MDIFF : forall {A : Type'} (M : Multiset A) (N' : Multiset A) (a : A), (@multiplicity A (@mdiff A M N') a) = (N.sub (@multiplicity A M a) (@multiplicity A N' a)).
Axiom thm_MUNION_MEMPTY : forall {A : Type'} (M : Multiset A) (a : A), ~ ((@munion A M (@msing A a)) = (@mempty A)).
Axiom thm_MMEMBER_MUNION : forall {_183296 : Type'} (M : Multiset _183296) (x : _183296) (N' : Multiset _183296), (@mmember _183296 x (@munion _183296 M N')) = ((@mmember _183296 x M) \/ (@mmember _183296 x N')).
Axiom thm_MMEMBER_MSING : forall {_183306 : Type'} (x : _183306) (a : _183306), (@mmember _183306 x (@msing _183306 a)) = (x = a).
Axiom thm_MUNION_EMPTY : forall {_183316 : Type'} (M : Multiset _183316), (@munion _183316 M (@mempty _183316)) = M.
Axiom thm_MUNION_ASSOC : forall {_183332 : Type'} (M1 : Multiset _183332) (M2 : Multiset _183332) (M3 : Multiset _183332), (@munion _183332 M1 (@munion _183332 M2 M3)) = (@munion _183332 (@munion _183332 M1 M2) M3).
Axiom thm_MUNION_AC : forall {_183376 : Type'} (M2 : Multiset _183376) (M1 : Multiset _183376) (M3 : Multiset _183376), ((@munion _183376 M1 M2) = (@munion _183376 M2 M1)) /\ (((@munion _183376 (@munion _183376 M1 M2) M3) = (@munion _183376 M1 (@munion _183376 M2 M3))) /\ ((@munion _183376 M1 (@munion _183376 M2 M3)) = (@munion _183376 M2 (@munion _183376 M1 M3)))).
Axiom thm_MUNION_11 : forall {_183388 : Type'} (N' : Multiset _183388) (M1 : Multiset _183388) (M2 : Multiset _183388), ((@munion _183388 M1 N') = (@munion _183388 M2 N')) = (M1 = M2).
Axiom thm_MUNION_INUNION : forall {_183410 : Type'} (b : _183410) (a : _183410) (M : Multiset _183410), ((@mmember _183410 a (@munion _183410 M (@msing _183410 b))) /\ (~ (b = a))) -> @mmember _183410 a M.
Axiom thm_MMEMBER_MDIFF : forall {A : Type'} (M : Multiset A) (a : A), (@mmember A a M) -> M = (@munion A (@mdiff A M (@msing A a)) (@msing A a)).
Axiom thm_MULTISET_INDUCT_LEMMA1 : forall {A : Type'} (a : A) (s : A -> Prop) (P : (Multiset A) -> Prop), ((forall M : Multiset A, (@subset A (@GSPEC A (fun GEN_PVAR_439 : A => exists a' : A, @SETSPEC A GEN_PVAR_439 (~ ((@multiplicity A M a') = N0)) a')) s) -> P M) /\ (forall a' : A, forall M : Multiset A, (P M) -> P (@munion A M (@msing A a')))) -> forall n : N, forall M : Multiset A, (((@multiplicity A M a) = n) /\ (@subset A (@GSPEC A (fun GEN_PVAR_440 : A => exists a' : A, @SETSPEC A GEN_PVAR_440 (~ ((@multiplicity A M a') = N0)) a')) (@INSERT A a s))) -> P M.
Axiom thm_MULTISET_INDUCT_LEMMA2 : forall {A : Type'} (P : (Multiset A) -> Prop), ((P (@mempty A)) /\ (forall a : A, forall M : Multiset A, (P M) -> P (@munion A M (@msing A a)))) -> forall s : A -> Prop, (@finite_set A s) -> forall M : Multiset A, (@subset A (@GSPEC A (fun GEN_PVAR_441 : A => exists a : A, @SETSPEC A GEN_PVAR_441 (~ ((@multiplicity A M a) = N0)) a)) s) -> P M.
Axiom thm_MULTISET_INDUCT : forall {A : Type'} (P : (Multiset A) -> Prop), ((P (@mempty A)) /\ (forall a : A, forall M : Multiset A, (P M) -> P (@munion A M (@msing A a)))) -> forall M : Multiset A, P M.
Axiom thm_WFP_CASES : forall {_183794 : Type'}, forall lt2 : _183794 -> _183794 -> Prop, forall a : _183794, (@Acc _183794 lt2 a) = (forall y : _183794, (lt2 y a) -> @Acc _183794 lt2 y).
Axiom thm_WFP_INDUCT : forall {_183794 : Type'}, forall lt2 : _183794 -> _183794 -> Prop, forall WFP' : _183794 -> Prop, (forall x : _183794, (forall y : _183794, (lt2 y x) -> WFP' y) -> WFP' x) -> forall a : _183794, (@Acc _183794 lt2 a) -> WFP' a.
Axiom thm_WFP_RULES : forall {_183794 : Type'}, forall lt2 : _183794 -> _183794 -> Prop, forall x : _183794, (forall y : _183794, (lt2 y x) -> @Acc _183794 lt2 y) -> @Acc _183794 lt2 x.
Axiom thm_WFP_PART_INDUCT : forall {A : Type'} (lt2 : A -> A -> Prop), forall P : A -> Prop, (forall x : A, ((@IN A x (@Acc A lt2)) /\ (forall y : A, (lt2 y x) -> P y)) -> P x) -> forall x : A, (@IN A x (@Acc A lt2)) -> P x.
Axiom thm_WFP_WF : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = ((@Acc A lt2) = (@setT A)).
Axiom thm_WFP_DCHAIN : forall {A : Type'}, forall lt2 : A -> A -> Prop, (@Acc A lt2) = (@GSPEC A (fun GEN_PVAR_443 : A => exists a : A, @SETSPEC A GEN_PVAR_443 (forall x : N -> A, (forall n : N, lt2 (x (N.succ n)) (x n)) -> ~ ((x N0) = a)) a)).
Axiom thm_morder : forall {_183976 : Type'}, forall M : Multiset _183976, forall N' : Multiset _183976, forall lt2 : _183976 -> _183976 -> Prop, (@morder _183976 lt2 N' M) = (exists M0 : Multiset _183976, exists a : _183976, exists K : Multiset _183976, (M = (@munion _183976 M0 (@msing _183976 a))) /\ ((N' = (@munion _183976 M0 K)) /\ (forall b : _183976, (@mmember _183976 b K) -> lt2 b a))).
Axiom thm_LEMMA_2_0 : forall {A : Type'} (N' : Multiset A) (M0 : Multiset A) (lt2 : A -> A -> Prop) (a : A), (@morder A lt2 N' (@munion A M0 (@msing A a))) -> (exists M : Multiset A, (@morder A lt2 M M0) /\ (N' = (@munion A M (@msing A a)))) \/ (exists K : Multiset A, (N' = (@munion A M0 K)) /\ (forall b : A, (@mmember A b K) -> lt2 b a)).
Axiom thm_LEMMA_2_1 : forall {A : Type'} (M0 : Multiset A) (a : A) (lt2 : A -> A -> Prop), ((forall M : Multiset A, forall b : A, ((lt2 b a) /\ (@IN (Multiset A) M (@Acc (Multiset A) (@morder A lt2)))) -> @IN (Multiset A) (@munion A M (@msing A b)) (@Acc (Multiset A) (@morder A lt2))) /\ ((@IN (Multiset A) M0 (@Acc (Multiset A) (@morder A lt2))) /\ (forall M : Multiset A, (@morder A lt2 M M0) -> @IN (Multiset A) (@munion A M (@msing A a)) (@Acc (Multiset A) (@morder A lt2))))) -> @IN (Multiset A) (@munion A M0 (@msing A a)) (@Acc (Multiset A) (@morder A lt2)).
Axiom thm_LEMMA_2_2 : forall {_184244 : Type'} (a : _184244) (lt2 : _184244 -> _184244 -> Prop), (forall M : Multiset _184244, forall b : _184244, ((lt2 b a) /\ (@IN (Multiset _184244) M (@Acc (Multiset _184244) (@morder _184244 lt2)))) -> @IN (Multiset _184244) (@munion _184244 M (@msing _184244 b)) (@Acc (Multiset _184244) (@morder _184244 lt2))) -> forall M : Multiset _184244, (@IN (Multiset _184244) M (@Acc (Multiset _184244) (@morder _184244 lt2))) -> @IN (Multiset _184244) (@munion _184244 M (@msing _184244 a)) (@Acc (Multiset _184244) (@morder _184244 lt2)).
Axiom thm_LEMMA_2_3 : forall {_184278 : Type'} (lt2 : _184278 -> _184278 -> Prop), (@well_founded _184278 lt2) -> forall a : _184278, forall M : Multiset _184278, (@IN (Multiset _184278) M (@Acc (Multiset _184278) (@morder _184278 lt2))) -> @IN (Multiset _184278) (@munion _184278 M (@msing _184278 a)) (@Acc (Multiset _184278) (@morder _184278 lt2)).
Axiom thm_LEMMA_2_4 : forall {_184283 : Type'} (lt2 : _184283 -> _184283 -> Prop), (@well_founded _184283 lt2) -> forall M : Multiset _184283, @IN (Multiset _184283) M (@Acc (Multiset _184283) (@morder _184283 lt2)).
Axiom thm_MORDER_WF : forall {_184299 : Type'} (lt2 : _184299 -> _184299 -> Prop), (@well_founded _184299 lt2) -> @well_founded (Multiset _184299) (@morder _184299 lt2).
Axiom thm_LIST_UNION : forall {_184322 : Type'} (h : _184322 -> Prop) (t : list (_184322 -> Prop)), ((@list_Union _184322 (@nil (_184322 -> Prop))) = (@set0 _184322)) /\ ((@list_Union _184322 (@cons (_184322 -> Prop) h t)) = (@setU _184322 h (@list_Union _184322 t))).
Axiom thm_LIST_UNION_FINITE : forall {_184338 : Type'}, forall l : list (_184338 -> Prop), (@List.Forall (_184338 -> Prop) (@finite_set _184338) l) -> @finite_set _184338 (@list_Union _184338 l).
Axiom thm_IN_LIST_UNION : forall {_184361 : Type'}, forall x : _184361, forall l : list (_184361 -> Prop), (@IN _184361 x (@list_Union _184361 l)) = (@List.Exists (_184361 -> Prop) (fun s : _184361 -> Prop => @IN _184361 x s) l).
Axiom thm_LIST_UNION_APPEND : forall {_184386 : Type'}, forall l1 : list (_184386 -> Prop), forall l2 : list (_184386 -> Prop), (@list_Union _184386 (@app (_184386 -> Prop) l1 l2)) = (@setU _184386 (@list_Union _184386 l1) (@list_Union _184386 l2)).
Axiom thm_term_raw_INDUCT : forall P0 : term -> Prop, forall P1 : (list term) -> Prop, ((forall a : N, P0 (V a)) /\ ((forall a0 : N, forall a1 : list term, (P1 a1) -> P0 (Fn a0 a1)) /\ ((P1 (@nil term)) /\ (forall a0 : term, forall a1 : list term, ((P0 a0) /\ (P1 a1)) -> P1 (@cons term a0 a1))))) -> (forall x0 : term, P0 x0) /\ (forall x1 : list term, P1 x1).
Axiom thm_term_raw_RECURSION : forall {Z0 Z1 : Type'}, forall f0 : N -> Z1, forall f1 : N -> (list term) -> Z0 -> Z1, forall f2 : Z0, forall f3 : term -> (list term) -> Z1 -> Z0 -> Z0, exists fn0 : (list term) -> Z0, exists fn1 : term -> Z1, (forall a : N, (fn1 (V a)) = (f0 a)) /\ ((forall a0 : N, forall a1 : list term, (fn1 (Fn a0 a1)) = (f1 a0 a1 (fn0 a1))) /\ (((fn0 (@nil term)) = f2) /\ (forall a0 : term, forall a1 : list term, (fn0 (@cons term a0 a1)) = (f3 a0 a1 (fn1 a0) (fn0 a1))))).
Axiom thm_term_INDUCT : forall P : term -> Prop, ((forall v : N, P (V v)) /\ (forall s : N, forall l : list term, (@List.Forall term P l) -> P (Fn s l))) -> forall t : term, P t.
Axiom thm_term_RECURSION : forall {Z' : Type'}, forall f : N -> Z', forall h : N -> (list term) -> (list Z') -> Z', exists fn : term -> Z', (forall v : N, (fn (V v)) = (f v)) /\ (forall s : N, forall l : list term, (fn (Fn s l)) = (h s l (@List.map term Z' fn l))).
Axiom thm_term_INJ : (forall v : N, forall v' : N, ((V v) = (V v')) = (v = v')) /\ (forall s : N, forall l : list term, forall s' : N, forall l' : list term, ((Fn s l) = (Fn s' l')) = ((s = s') /\ (l = l'))).
Axiom thm_term_DISTINCT : forall v : N, forall s' : N, forall l' : list term, ~ ((V v) = (Fn s' l')).
Axiom thm_term_CASES : forall t : term, (exists v : N, t = (V v)) \/ (exists s : N, exists l : list term, t = (Fn s l)).
Axiom thm_form_INDUCTION : forall P : form -> Prop, ((P FFalse) /\ ((forall a0 : N, forall a1 : list term, P (Atom a0 a1)) /\ ((forall a0 : form, forall a1 : form, ((P a0) /\ (P a1)) -> P (FImp a0 a1)) /\ (forall a0 : N, forall a1 : form, (P a1) -> P (FAll a0 a1))))) -> forall x : form, P x.
Axiom thm_form_RECURSION : forall {Z' : Type'}, forall f0 : Z', forall f1 : N -> (list term) -> Z', forall f2 : form -> form -> Z' -> Z' -> Z', forall f3 : N -> form -> Z' -> Z', exists fn : form -> Z', ((fn FFalse) = f0) /\ ((forall a0 : N, forall a1 : list term, (fn (Atom a0 a1)) = (f1 a0 a1)) /\ ((forall a0 : form, forall a1 : form, (fn (FImp a0 a1)) = (f2 a0 a1 (fn a0) (fn a1))) /\ (forall a0 : N, forall a1 : form, (fn (FAll a0 a1)) = (f3 a0 a1 (fn a1))))).
Axiom thm_form_INJ : (forall a0 : N, forall a1 : list term, forall a0' : N, forall a1' : list term, ((Atom a0 a1) = (Atom a0' a1')) = ((a0 = a0') /\ (a1 = a1'))) /\ ((forall a0 : form, forall a1 : form, forall a0' : form, forall a1' : form, ((FImp a0 a1) = (FImp a0' a1')) = ((a0 = a0') /\ (a1 = a1'))) /\ (forall a0 : N, forall a1 : form, forall a0' : N, forall a1' : form, ((FAll a0 a1) = (FAll a0' a1')) = ((a0 = a0') /\ (a1 = a1')))).
Axiom thm_form_DISTINCT : (forall a0' : N, forall a1' : list term, ~ (FFalse = (Atom a0' a1'))) /\ ((forall a0' : form, forall a1' : form, ~ (FFalse = (FImp a0' a1'))) /\ ((forall a0' : N, forall a1' : form, ~ (FFalse = (FAll a0' a1'))) /\ ((forall a0 : N, forall a1 : list term, forall a0' : form, forall a1' : form, ~ ((Atom a0 a1) = (FImp a0' a1'))) /\ ((forall a0 : N, forall a1 : list term, forall a0' : N, forall a1' : form, ~ ((Atom a0 a1) = (FAll a0' a1'))) /\ (forall a0 : form, forall a1 : form, forall a0' : N, forall a1' : form, ~ ((FImp a0 a1) = (FAll a0' a1'))))))).
Axiom thm_form_CASES : forall x : form, (x = FFalse) \/ ((exists a0 : N, exists a1 : list term, x = (Atom a0 a1)) \/ ((exists a0 : form, exists a1 : form, x = (FImp a0 a1)) \/ (exists a0 : N, exists a1 : form, x = (FAll a0 a1)))).
Axiom thm_Not_DEF : forall p : form, (Not p) = (FImp p FFalse).
Axiom thm_True_DEF : FTrue = (Not FFalse).
Axiom thm_Or_DEF : forall p : form, forall q : form, (FOr p q) = (FImp (FImp p q) q).
Axiom thm_And_DEF : forall p : form, forall q : form, (FAnd p q) = (Not (FOr (Not p) (Not q))).
Axiom thm_Iff_DEF : forall q : form, forall p : form, (FEquiv p q) = (FAnd (FImp p q) (FImp q p)).
Axiom thm_Exists_DEF : forall x : N, forall p : form, (FEx x p) = (Not (FAll x (Not p))).
Axiom thm_functions_term : (forall v : N, (functions_term (V v)) = (@set0 (prod N N))) /\ (forall f : N, forall l : list term, (functions_term (Fn f l)) = (@INSERT (prod N N) (@pair N N f (@lengthN term l)) (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) functions_term l)))).
Axiom thm_functions_form : forall (a : N) (l : list term) (q : form) (x : N) (p : form), ((functions_form FFalse) = (@set0 (prod N N))) /\ (((functions_form (Atom a l)) = (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) functions_term l))) /\ (((functions_form (FImp p q)) = (@setU (prod N N) (functions_form p) (functions_form q))) /\ ((functions_form (FAll x p)) = (functions_form p)))).
Axiom thm_predicates_form : forall (a : N) (l : list term) (q : form) (x : N) (p : form), ((predicates_form FFalse) = (@set0 (prod N N))) /\ (((predicates_form (Atom a l)) = (@INSERT (prod N N) (@pair N N a (@lengthN term l)) (@set0 (prod N N)))) /\ (((predicates_form (FImp p q)) = (@setU (prod N N) (predicates_form p) (predicates_form q))) /\ ((predicates_form (FAll x p)) = (predicates_form p)))).
Axiom thm_functions : forall fms : form -> Prop, (functions fms) = (@UNIONS (prod N N) (@GSPEC ((prod N N) -> Prop) (fun GEN_PVAR_444 : (prod N N) -> Prop => exists f : form, @SETSPEC ((prod N N) -> Prop) GEN_PVAR_444 (@IN form f fms) (functions_form f)))).
Axiom thm_predicates : forall fms : form -> Prop, (predicates fms) = (@UNIONS (prod N N) (@GSPEC ((prod N N) -> Prop) (fun GEN_PVAR_445 : (prod N N) -> Prop => exists f : form, @SETSPEC ((prod N N) -> Prop) GEN_PVAR_445 (@IN form f fms) (predicates_form f)))).
Axiom thm_language : forall fms : form -> Prop, (language fms) = (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) (functions fms) (predicates fms)).
Axiom thm_FUNCTIONS_SING : forall (p : form), (functions (@INSERT form p (@set0 form))) = (functions_form p).
Axiom thm_LANGUAGE_1 : forall (p : form), (language (@INSERT form p (@set0 form))) = (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) (functions_form p) (predicates_form p)).
Axiom thm_Dom_DEF : forall {A : Type'}, forall Funs : N -> (list A) -> A, forall Preds : N -> (list A) -> Prop, forall D : A -> Prop, (@Dom A (@pair (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) D (@pair (N -> (list A) -> A) (N -> (list A) -> Prop) Funs Preds))) = D.
Axiom thm_Fun_DEF : forall {A : Type'}, forall D : A -> Prop, forall Preds : N -> (list A) -> Prop, forall Funs : N -> (list A) -> A, (@Fun A (@pair (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) D (@pair (N -> (list A) -> A) (N -> (list A) -> Prop) Funs Preds))) = Funs.
Axiom thm_Pred_DEF : forall {A : Type'}, forall D : A -> Prop, forall Funs : N -> (list A) -> A, forall Preds : N -> (list A) -> Prop, (@Pred A (@pair (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) D (@pair (N -> (list A) -> A) (N -> (list A) -> Prop) Funs Preds))) = Preds.
Axiom thm_MODEL_EQ : forall {_184858 : Type'} (M : prod (_184858 -> Prop) (prod (N -> (list _184858) -> _184858) (N -> (list _184858) -> Prop))) (M' : prod (_184858 -> Prop) (prod (N -> (list _184858) -> _184858) (N -> (list _184858) -> Prop))), (M = M') = (((@Dom _184858 M) = (@Dom _184858 M')) /\ (((@Fun _184858 M) = (@Fun _184858 M')) /\ ((@Pred _184858 M) = (@Pred _184858 M')))).
Axiom thm_MODEL_DECOMP : forall {_184876 : Type'} (M : prod (_184876 -> Prop) (prod (N -> (list _184876) -> _184876) (N -> (list _184876) -> Prop))), M = (@pair (_184876 -> Prop) (prod (N -> (list _184876) -> _184876) (N -> (list _184876) -> Prop)) (@Dom _184876 M) (@pair (N -> (list _184876) -> _184876) (N -> (list _184876) -> Prop) (@Fun _184876 M) (@Pred _184876 M))).
Axiom thm_FVT : (forall x : N, (free_variables_term (V x)) = (@INSERT N x (@set0 N))) /\ (forall f : N, forall l : list term, (free_variables_term (Fn f l)) = (@list_Union N (@List.map term (N -> Prop) free_variables_term l))).
Axiom thm_FV : ((free_variables FFalse) = (@set0 N)) /\ ((forall a : N, forall l : list term, (free_variables (Atom a l)) = (@list_Union N (@List.map term (N -> Prop) free_variables_term l))) /\ ((forall p : form, forall q : form, (free_variables (FImp p q)) = (@setU N (free_variables p) (free_variables q))) /\ (forall x : N, forall p : form, (free_variables (FAll x p)) = (@DELETE N (free_variables p) x)))).
Axiom thm_BV : ((bound_variables FFalse) = (@set0 N)) /\ ((forall a : N, forall l : list term, (bound_variables (Atom a l)) = (@set0 N)) /\ ((forall p : form, forall q : form, (bound_variables (FImp p q)) = (@setU N (bound_variables p) (bound_variables q))) /\ (forall x : N, forall p : form, (bound_variables (FAll x p)) = (@INSERT N x (bound_variables p))))).
Axiom thm_FVT_FINITE : forall t : term, @finite_set N (free_variables_term t).
Axiom thm_FV_FINITE : forall p : form, @finite_set N (free_variables p).
Axiom thm_BV_FINITE : forall p : form, @finite_set N (bound_variables p).
Axiom thm_FV_EXISTS : forall (p : form) (x : N), (free_variables (FEx x p)) = (@DELETE N (free_variables p) x).
Axiom thm_valmod : forall {_185091 _185100 : Type'}, forall x : _185100, forall a : _185091, forall v : _185100 -> _185091, (@valmod _185091 _185100 (@pair _185100 _185091 x a) v) = (fun y : _185100 => @COND _185091 (y = x) a (v y)).
Axiom thm_VALMOD_CLAUSES : forall {_185124 _185125 _185158 _185162 : Type'}, (forall v : _185125 -> _185124, forall a : _185124, forall k : _185125, (@valmod _185124 _185125 (@pair _185125 _185124 k a) v k) = a) /\ (forall v : _185162 -> _185158, forall a : _185158, forall k : _185162, forall x : _185162, (~ (x = k)) -> (@valmod _185158 _185162 (@pair _185162 _185158 k a) v x) = (v x)).
Axiom thm_VALMOD_TRIV : forall {_185179 _185183 : Type'}, forall v : _185183 -> _185179, forall x : _185183, (@valmod _185179 _185183 (@pair _185183 _185179 x (v x)) v) = v.
Axiom thm_VALMOD_VALMOD : forall {_185224 _185225 : Type'}, forall v : _185225 -> _185224, forall a : _185224, forall x : _185225, forall b : _185224, (@valmod _185224 _185225 (@pair _185225 _185224 x a) (@valmod _185224 _185225 (@pair _185225 _185224 x b) v)) = (@valmod _185224 _185225 (@pair _185225 _185224 x a) v).
Axiom thm_valuation : forall {_185242 : Type'}, forall v : N -> _185242, forall M : prod (_185242 -> Prop) (prod (N -> (list _185242) -> _185242) (N -> (list _185242) -> Prop)), (@valuation _185242 M v) = (forall x : N, @IN _185242 (v x) (@Dom _185242 M)).
Axiom thm_VALUATION_VALMOD : forall {_185275 : Type'} (x : N), forall M : prod (_185275 -> Prop) (prod (N -> (list _185275) -> _185275) (N -> (list _185275) -> Prop)), forall a : _185275, forall v : N -> _185275, ((@valuation _185275 M v) /\ (@IN _185275 a (@Dom _185275 M))) -> @valuation _185275 M (@valmod _185275 N (@pair N _185275 x a) v).
Axiom thm_VALUATION_IS_VALMOD : forall {_185295 _185299 : Type'}, forall v : _185299 -> _185295, forall x : _185299, (@valmod _185295 _185299 (@pair _185299 _185295 x (v x)) v) = v.
Axiom thm_holds : forall {_185435 : Type'} (M : prod (_185435 -> Prop) (prod (N -> (list _185435) -> _185435) (N -> (list _185435) -> Prop))) (v : N -> _185435), ((@holds _185435 M v FFalse) = False) /\ ((forall a : N, forall l : list term, (@holds _185435 M v (Atom a l)) = (@Pred _185435 M a (@List.map term _185435 (@termval _185435 M v) l))) /\ ((forall p : form, forall q : form, (@holds _185435 M v (FImp p q)) = ((@holds _185435 M v p) -> @holds _185435 M v q)) /\ (forall x : N, forall p : form, (@holds _185435 M v (FAll x p)) = (forall a : _185435, (@IN _185435 a (@Dom _185435 M)) -> @holds _185435 M (@valmod _185435 N (@pair N _185435 x a) v) p)))).
Axiom thm_hold : forall {_185457 : Type'}, forall fms : form -> Prop, forall M : prod (_185457 -> Prop) (prod (N -> (list _185457) -> _185457) (N -> (list _185457) -> Prop)), forall v : N -> _185457, (@hold _185457 M v fms) = (forall p : form, (@IN form p fms) -> @holds _185457 M v p).
Axiom thm_satisfies : forall {_185477 : Type'}, forall fms : form -> Prop, forall M : prod (_185477 -> Prop) (prod (N -> (list _185477) -> _185477) (N -> (list _185477) -> Prop)), (@satisfies _185477 M fms) = (forall v : N -> _185477, forall p : form, ((@valuation _185477 M v) /\ (@IN form p fms)) -> @holds _185477 M v p).
Axiom thm_SATISFIES_1 : forall {_185490 : Type'} (M : prod (_185490 -> Prop) (prod (N -> (list _185490) -> _185490) (N -> (list _185490) -> Prop))) (p : form), (@satisfies _185490 M (@INSERT form p (@set0 form))) = (forall v : N -> _185490, (@valuation _185490 M v) -> @holds _185490 M v p).
Axiom thm_HOLDS : forall {_185761 : Type'} (M : prod (_185761 -> Prop) (prod (N -> (list _185761) -> _185761) (N -> (list _185761) -> Prop))) (v : N -> _185761), ((@holds _185761 M v FFalse) = False) /\ (((@holds _185761 M v FTrue) = True) /\ ((forall a : N, forall l : list term, (@holds _185761 M v (Atom a l)) = (@Pred _185761 M a (@List.map term _185761 (@termval _185761 M v) l))) /\ ((forall p : form, (@holds _185761 M v (Not p)) = (~ (@holds _185761 M v p))) /\ ((forall p : form, forall q : form, (@holds _185761 M v (FOr p q)) = ((@holds _185761 M v p) \/ (@holds _185761 M v q))) /\ ((forall p : form, forall q : form, (@holds _185761 M v (FAnd p q)) = ((@holds _185761 M v p) /\ (@holds _185761 M v q))) /\ ((forall p : form, forall q : form, (@holds _185761 M v (FImp p q)) = ((@holds _185761 M v p) -> @holds _185761 M v q)) /\ ((forall p : form, forall q : form, (@holds _185761 M v (FEquiv p q)) = ((@holds _185761 M v p) = (@holds _185761 M v q))) /\ ((forall x : N, forall p : form, (@holds _185761 M v (FAll x p)) = (forall a : _185761, (@IN _185761 a (@Dom _185761 M)) -> @holds _185761 M (@valmod _185761 N (@pair N _185761 x a) v) p)) /\ (forall x : N, forall p : form, (@holds _185761 M v (FEx x p)) = (exists a : _185761, (@IN _185761 a (@Dom _185761 M)) /\ (@holds _185761 M (@valmod _185761 N (@pair N _185761 x a) v) p))))))))))).
Axiom thm_TERMVAL_VALUATION : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall t : term, forall v : N -> A, forall v' : N -> A, (forall x : N, (@IN N x (free_variables_term t)) -> (v' x) = (v x)) -> (@termval A M v' t) = (@termval A M v t).
Axiom thm_HOLDS_VALUATION : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall p : form, forall v : N -> A, forall v' : N -> A, (forall x : N, (@IN N x (free_variables p)) -> (v' x) = (v x)) -> (@holds A M v' p) = (@holds A M v p).
Axiom thm_satisfiable : forall {A : Type'}, forall U : A -> Prop, forall fms : form -> Prop, (@satisfiable A U fms) = (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M fms)).
Axiom thm_valid : forall {A : Type'}, forall U : A -> Prop, forall fms : form -> Prop, (@valid A U fms) = (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), @satisfies A M fms).
Axiom thm_entails : forall {A : Type'}, forall U : A -> Prop, forall A' : form -> Prop, forall p : form, (@entails A U A' p) = (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (@hold A M v A') -> @holds A M v p).
Axiom thm_equivalent : forall {A : Type'}, forall U : A -> Prop, forall p : form, forall q : form, (@equivalent A U p q) = (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (@holds A M v p) = (@holds A M v q)).
Axiom thm_interpretation : forall {_186064 : Type'}, forall preds : (prod N N) -> Prop, forall fns : (prod N N) -> Prop, forall M : prod (_186064 -> Prop) (prod (N -> (list _186064) -> _186064) (N -> (list _186064) -> Prop)), (@interpretation _186064 (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) fns preds) M) = (forall f : N, forall l : list _186064, ((@IN (prod N N) (@pair N N f (@lengthN _186064 l)) fns) /\ (@List.Forall _186064 (fun x : _186064 => @IN _186064 x (@Dom _186064 M)) l)) -> @IN _186064 (@Fun _186064 M f l) (@Dom _186064 M)).
Axiom thm_INTERPRETATION_TERMVAL : forall {_186111 : Type'}, forall any : (prod N N) -> Prop, forall M : prod (_186111 -> Prop) (prod (N -> (list _186111) -> _186111) (N -> (list _186111) -> Prop)), forall v : N -> _186111, forall t : term, ((@interpretation _186111 (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) (functions_term t) any) M) /\ (@valuation _186111 M v)) -> @IN _186111 (@termval _186111 M v t) (@Dom _186111 M).
Axiom thm_INTERPRETATION_SUBLANGUAGE : forall {_186142 : Type'}, forall M : prod (_186142 -> Prop) (prod (N -> (list _186142) -> _186142) (N -> (list _186142) -> Prop)), forall funs1 : (prod N N) -> Prop, forall funs2 : (prod N N) -> Prop, forall preds1 : (prod N N) -> Prop, forall preds2 : (prod N N) -> Prop, (@subset (prod N N) funs2 funs1) -> (@interpretation _186142 (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) funs1 preds1) M) -> @interpretation _186142 (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) funs2 preds2) M.
Axiom thm_TERMSUBST_TERMVAL : forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), ((@Fun term M) = Fn) -> forall v : N -> term, forall t : term, (termsubst v t) = (@termval term M v t).
Axiom thm_TERMVAL_TRIV : forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), ((@Fun term M) = Fn) -> forall t : term, (@termval term M V t) = t.
Axiom thm_TERMVAL_TERMSUBST : forall {_186279 : Type'}, forall M : prod (_186279 -> Prop) (prod (N -> (list _186279) -> _186279) (N -> (list _186279) -> Prop)), forall v : N -> _186279, forall i : N -> term, forall t : term, (@termval _186279 M v (termsubst i t)) = (@termval _186279 M (@o N term _186279 (@termval _186279 M v) i) t).
Axiom thm_TERMSUBST_TERMSUBST : forall i : N -> term, forall j : N -> term, forall t : term, (termsubst j (termsubst i t)) = (termsubst (@o N term term (termsubst j) i) t).
Axiom thm_TERMSUBST_TRIV : forall t : term, (termsubst V t) = t.
Axiom thm_TERMSUBST_VALUATION : forall t : term, forall v : N -> term, forall v' : N -> term, (forall x : N, (@IN N x (free_variables_term t)) -> (v' x) = (v x)) -> (termsubst v' t) = (termsubst v t).
Axiom thm_TERMSUBST_FVT : forall t : term, forall i : N -> term, (free_variables_term (termsubst i t)) = (@GSPEC N (fun GEN_PVAR_449 : N => exists x : N, @SETSPEC N GEN_PVAR_449 (exists y : N, (@IN N y (free_variables_term t)) /\ (@IN N x (free_variables_term (i y)))) x)).
Axiom thm_MAX_SYM : forall x : N, forall y : N, (N.max x y) = (N.max y x).
Axiom thm_MAX_ASSOC : forall x : N, forall y : N, forall z : N, (N.max x (N.max y z)) = (N.max (N.max x y) z).
Axiom thm_SETMAX : forall s : N -> Prop, (SETMAX s) = (@fold_set N N N.max s N0).
Axiom thm_VARIANT : forall s : N -> Prop, (VARIANT s) = (N.add (SETMAX s) ((BIT1 N0))).
Axiom thm_SETMAX_LEMMA : ((SETMAX (@set0 N)) = N0) /\ (forall x : N, forall s : N -> Prop, (@finite_set N s) -> (SETMAX (@INSERT N x s)) = (@COND N (@IN N x s) (SETMAX s) (N.max x (SETMAX s)))).
Axiom thm_SETMAX_MEMBER : forall s : N -> Prop, (@finite_set N s) -> forall x : N, (@IN N x s) -> N.le x (SETMAX s).
Axiom thm_SETMAX_THM : ((SETMAX (@set0 N)) = N0) /\ (forall x : N, forall s : N -> Prop, (@finite_set N s) -> (SETMAX (@INSERT N x s)) = (N.max x (SETMAX s))).
Axiom thm_SETMAX_UNION : forall s : N -> Prop, forall t : N -> Prop, (@finite_set N (@setU N s t)) -> (SETMAX (@setU N s t)) = (N.max (SETMAX s) (SETMAX t)).
Axiom thm_VARIANT_FINITE : forall s : N -> Prop, (@finite_set N s) -> ~ (@IN N (VARIANT s) s).
Axiom thm_VARIANT_THM : forall p : form, ~ (@IN N (VARIANT (free_variables p)) (free_variables p)).
Axiom thm_formsubst : forall (p : N) (l : list term) (r : form) (q : form) (x : N) (v : N -> term), ((formsubst v FFalse) = FFalse) /\ (((formsubst v (Atom p l)) = (Atom p (@List.map term term (termsubst v) l))) /\ (((formsubst v (FImp q r)) = (FImp (formsubst v q) (formsubst v r))) /\ ((formsubst v (FAll x q)) = (@LET (N -> term) form (fun v' : N -> term => @LET_END form (@LET N form (fun z : N => @LET_END form (FAll z (formsubst (@valmod term N (@pair N term x (V z)) v) q))) (@COND N (exists y : N, (@IN N y (free_variables (FAll x q))) /\ (@IN N x (free_variables_term (v' y)))) (VARIANT (free_variables (formsubst v' q))) x))) (@valmod term N (@pair N term x (V x)) v))))).
Axiom thm_FORMSUBST_TRIV : forall p : form, (formsubst V p) = p.
Axiom thm_FORMSUBST_VALUATION : forall p : form, forall v : N -> term, forall v' : N -> term, (forall x : N, (@IN N x (free_variables p)) -> (v' x) = (v x)) -> (formsubst v' p) = (formsubst v p).
Axiom thm_FORMSUBST_FV : forall p : form, forall i : N -> term, (free_variables (formsubst i p)) = (@GSPEC N (fun GEN_PVAR_453 : N => exists x : N, @SETSPEC N GEN_PVAR_453 (exists y : N, (@IN N y (free_variables p)) /\ (@IN N x (free_variables_term (i y)))) x)).
Axiom thm_HOLDS_FORMSUBST : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))), forall p : form, forall i : N -> term, forall v : N -> A, (@holds A M v (formsubst i p)) = (@holds A M (@o N term A (@termval A M v) i) p).
Axiom thm_HOLDS_FORMSUBST1 : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))), forall x : N, forall t : term, forall p : form, forall v : N -> A, (@holds A M v (formsubst (@valmod term N (@pair N term x t) V) p)) = (@holds A M (@valmod A N (@pair N A x (@termval A M v t)) v) p).
Axiom thm_HOLDS_RENAME : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))), forall x : N, forall y : N, forall p : form, forall v : N -> A, (@holds A M v (formsubst (@valmod term N (@pair N term x (V y)) V) p)) = (@holds A M (@valmod A N (@pair N A x (v y)) v) p).
Axiom thm_HOLDS_ALPHA_FORALL : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))), forall x : N, forall y : N, forall p : form, forall v : N -> A, (~ (@IN N y (free_variables (FAll x p)))) -> (@holds A M v (FAll y (formsubst (@valmod term N (@pair N term x (V y)) V) p))) = (@holds A M v (FAll x p)).
Axiom thm_HOLDS_ALPHA_EXISTS : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))), forall x : N, forall y : N, forall p : form, forall v : N -> A, (~ (@IN N y (free_variables (FEx x p)))) -> (@holds A M v (FEx y (formsubst (@valmod term N (@pair N term x (V y)) V) p))) = (@holds A M v (FEx x p)).
Axiom thm_FORMSUBST_RENAME : forall p : form, forall x : N, forall y : N, (@DELETE N (free_variables (formsubst (@valmod term N (@pair N term x (V y)) V) p)) y) = (@DELETE N (@DELETE N (free_variables p) x) y).
Axiom thm_TERMSUBST_FUNCTIONS_TERM : forall t : term, forall i : N -> term, (functions_term (termsubst i t)) = (@setU (prod N N) (functions_term t) (@GSPEC (prod N N) (fun GEN_PVAR_459 : prod N N => exists x : prod N N, @SETSPEC (prod N N) GEN_PVAR_459 (exists y : N, (@IN N y (free_variables_term t)) /\ (@IN (prod N N) x (functions_term (i y)))) x))).
Axiom thm_FORMSUBST_FUNCTIONS_FORM : forall p : form, forall i : N -> term, (functions_form (formsubst i p)) = (@setU (prod N N) (functions_form p) (@GSPEC (prod N N) (fun GEN_PVAR_463 : prod N N => exists x : prod N N, @SETSPEC (prod N N) GEN_PVAR_463 (exists y : N, (@IN N y (free_variables p)) /\ (@IN (prod N N) x (functions_term (i y)))) x))).
Axiom thm_FORMSUBST_FUNCTIONS_FORM_1 : forall x : N, forall t : term, forall p : form, (@IN N x (free_variables p)) -> (functions_form (formsubst (@valmod term N (@pair N term x t) V) p)) = (@setU (prod N N) (functions_form p) (functions_term t)).
Axiom thm_FORMSUBST_PREDICATES : forall p : form, forall i : N -> term, (predicates_form (formsubst i p)) = (predicates_form p).
Axiom thm_FORMSUBST_LANGUAGE_RENAME : forall (x : N) (y : N) (p : form), (language (@INSERT form (formsubst (@valmod term N (@pair N term x (V y)) V) p) (@set0 form))) = (language (@INSERT form p (@set0 form))).
Axiom thm_TERMVAL_FUNCTIONS : forall {A : Type'} (M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))), forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall t : term, (forall f : N, forall zs : list A, (@IN (prod N N) (@pair N N f (@lengthN A zs)) (functions_term t)) -> (@Fun A M f zs) = (@Fun A M' f zs)) -> forall v : N -> A, (@termval A M v t) = (@termval A M' v t).
Axiom thm_HOLDS_FUNCTIONS : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall p : form, (((@Dom A M) = (@Dom A M')) /\ ((forall P : N, forall zs : list A, (@Pred A M P zs) = (@Pred A M' P zs)) /\ (forall f : N, forall zs : list A, (@IN (prod N N) (@pair N N f (@lengthN A zs)) (functions_form p)) -> (@Fun A M f zs) = (@Fun A M' f zs)))) -> forall v : N -> A, (@holds A M v p) = (@holds A M' v p).
Axiom thm_HOLDS_PREDICATES : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall p : form, (((@Dom A M) = (@Dom A M')) /\ ((forall f : N, forall zs : list A, (@Fun A M f zs) = (@Fun A M' f zs)) /\ (forall P : N, forall zs : list A, (@IN (prod N N) (@pair N N P (@lengthN A zs)) (predicates_form p)) -> (@Pred A M P zs) = (@Pred A M' P zs)))) -> forall v : N -> A, (@holds A M v p) = (@holds A M' v p).
Axiom thm_HOLDS_UCLOSE : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall x : N, forall p : form, (forall v : N -> A, (@valuation A M v) -> @holds A M v (FAll x p)) = (((@Dom A M) = (@set0 A)) \/ (forall v : N -> A, (@valuation A M v) -> @holds A M v p)).
Axiom thm_MODEL_DUPLICATE : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall fns : (prod N N) -> Prop, forall preds : (prod N N) -> Prop, forall D : A -> Prop, ((@interpretation A (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) fns preds) M) /\ ((@subset A (@Dom A M) D) /\ (~ ((@Dom A M) = (@set0 A))))) -> exists M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) fns preds) M') /\ (((@Dom A M') = D) /\ (forall s : form -> Prop, ((@subset (prod N N) (functions s) fns) /\ (@subset (prod N N) (predicates s) preds)) -> (@satisfies A M' s) = (@satisfies A M s))).
Axiom thm_qfree : forall (n : N) (l : list term) (q : form) (x : N) (p : form), ((qfree FFalse) = True) /\ (((qfree (Atom n l)) = True) /\ (((qfree (FImp p q)) = ((qfree p) /\ (qfree q))) /\ ((qfree (FAll x p)) = False))).
Axiom thm_QFREE : ((qfree FFalse) = True) /\ (((qfree FTrue) = True) /\ ((forall a : N, forall l : list term, (qfree (Atom a l)) = True) /\ ((forall p : form, (qfree (Not p)) = (qfree p)) /\ ((forall p : form, forall q : form, (qfree (FOr p q)) = ((qfree p) /\ (qfree q))) /\ ((forall p : form, forall q : form, (qfree (FAnd p q)) = ((qfree p) /\ (qfree q))) /\ ((forall p : form, forall q : form, (qfree (FImp p q)) = ((qfree p) /\ (qfree q))) /\ ((forall p : form, forall q : form, (qfree (FEquiv p q)) = ((qfree p) /\ (qfree q))) /\ ((forall x : N, forall p : form, (qfree (FAll x p)) = False) /\ (forall x : N, forall p : form, (qfree (FEx x p)) = False))))))))).
Axiom thm_QFREE_FORMSUBST : forall p : form, forall v : N -> term, (qfree (formsubst v p)) = (qfree p).
Axiom thm_QFREE_BV_EMPTY : forall p : form, (qfree p) = ((bound_variables p) = (@set0 N)).
Axiom thm_prenex_RULES : (forall p : form, (qfree p) -> prenex p) /\ ((forall x : N, forall p : form, (prenex p) -> prenex (FAll x p)) /\ (forall x : N, forall p : form, (prenex p) -> prenex (FEx x p))).
Axiom thm_prenex_CASES : forall a : form, (prenex a) = ((qfree a) \/ ((exists x : N, exists p : form, (a = (FAll x p)) /\ (prenex p)) \/ (exists x : N, exists p : form, (a = (FEx x p)) /\ (prenex p)))).
Axiom thm_prenex_INDUCT : forall prenex' : form -> Prop, ((forall p : form, (qfree p) -> prenex' p) /\ ((forall x : N, forall p : form, (prenex' p) -> prenex' (FAll x p)) /\ (forall x : N, forall p : form, (prenex' p) -> prenex' (FEx x p)))) -> forall a : form, (prenex a) -> prenex' a.
Axiom thm_universal_RULES : (forall p : form, (qfree p) -> universal p) /\ (forall x : N, forall p : form, (universal p) -> universal (FAll x p)).
Axiom thm_universal_CASES : forall a : form, (universal a) = ((qfree a) \/ (exists x : N, exists p : form, (a = (FAll x p)) /\ (universal p))).
Axiom thm_universal_INDUCT : forall universal' : form -> Prop, ((forall p : form, (qfree p) -> universal' p) /\ (forall x : N, forall p : form, (universal' p) -> universal' (FAll x p))) -> forall a : form, (universal a) -> universal' a.
Axiom thm_prenex_INDUCT_NOT : forall {_189129 : Type'}, forall P : form -> Prop, ((forall p : form, (qfree p) -> P p) /\ ((forall x : N, forall p : form, (P p) -> P (FAll x p)) /\ (forall x : _189129, forall p : form, (P p) -> P (Not p)))) -> forall a : form, (prenex a) -> P a.
Axiom thm_PRENEX : ((prenex FFalse) = True) /\ (((prenex FTrue) = True) /\ ((forall a : N, forall l : list term, (prenex (Atom a l)) = True) /\ ((forall p : form, (prenex (Not p)) = ((qfree p) \/ (exists q : form, exists x : N, ((Not p) = (FEx x q)) /\ (prenex q)))) /\ ((forall p : form, forall q : form, (prenex (FOr p q)) = ((qfree p) /\ (qfree q))) /\ ((forall p : form, forall q : form, (prenex (FAnd p q)) = ((qfree p) /\ (qfree q))) /\ ((forall p : form, forall q : form, (prenex (FImp p q)) = (((qfree p) /\ (qfree q)) \/ (exists r : form, exists x : N, ((FImp p q) = (FEx x r)) /\ (prenex r)))) /\ ((forall p : form, forall q : form, (prenex (FEquiv p q)) = ((qfree p) /\ (qfree q))) /\ ((forall x : N, forall p : form, (prenex (FAll x p)) = (prenex p)) /\ (forall x : N, forall p : form, (prenex (FEx x p)) = (prenex p)))))))))).
Axiom thm_FORMSUBST_STRUCTURE_LEMMA : forall p : form, forall i : N -> term, (((formsubst i p) = FFalse) = (p = FFalse)) /\ (((exists a : N, exists l : list term, (formsubst i p) = (Atom a l)) = (exists a : N, exists l : list term, p = (Atom a l))) /\ (((exists q : form, exists r : form, (formsubst i p) = (FImp q r)) = (exists q : form, exists r : form, p = (FImp q r))) /\ ((exists x : N, exists q : form, (formsubst i p) = (FAll x q)) = (exists x : N, exists q : form, p = (FAll x q))))).
Axiom thm_FORMSUBST_STRUCTURE_NOT : forall p : form, forall i : N -> term, (exists q : form, (formsubst i p) = (Not q)) = (exists q : form, p = (Not q)).
Axiom thm_FORMSUBST_STRUCTURE_EXISTS : forall p : form, forall i : N -> term, (exists x : N, exists q : form, (formsubst i p) = (FEx x q)) = (exists x : N, exists q : form, p = (FEx x q)).
Axiom thm_PRENEX_FORMSUBST_LEMMA : forall p : form, (prenex p) -> forall i : N -> term, forall q : form, (p = (formsubst i q)) -> prenex q.
Axiom thm_PRENEX_FORMSUBST : forall p : form, forall i : N -> term, (prenex (formsubst i p)) = (prenex p).
Axiom thm_size : forall (p : N) (l : list term) (r : form) (x : N) (q : form), ((sizeN FFalse) = ((BIT1 N0))) /\ (((sizeN (Atom p l)) = ((BIT1 N0))) /\ (((sizeN (FImp q r)) = (N.add (sizeN q) (sizeN r))) /\ ((sizeN (FAll x q)) = (N.add ((BIT1 N0)) (sizeN q))))).
Axiom thm_SIZE : ((sizeN FFalse) = ((BIT1 N0))) /\ (((sizeN FTrue) = ((BIT0 (BIT1 N0)))) /\ ((forall a : N, forall l : list term, (sizeN (Atom a l)) = ((BIT1 N0))) /\ ((forall p : form, (sizeN (Not p)) = (N.add ((BIT1 N0)) (sizeN p))) /\ ((forall p : form, forall q : form, (sizeN (FOr p q)) = (N.add (sizeN p) (N.mul ((BIT0 (BIT1 N0))) (sizeN q)))) /\ ((forall p : form, forall q : form, (sizeN (FAnd p q)) = (N.add (sizeN p) (N.add (N.mul ((BIT0 (BIT1 N0))) (sizeN q)) ((BIT0 (BIT0 (BIT1 N0))))))) /\ ((forall p : form, forall q : form, (sizeN (FImp p q)) = (N.add (sizeN p) (sizeN q))) /\ ((forall p : form, forall q : form, (sizeN (FEquiv p q)) = (N.add (N.mul ((BIT1 (BIT1 N0))) (sizeN p)) (N.add (N.mul ((BIT1 (BIT1 N0))) (sizeN q)) ((BIT0 (BIT0 (BIT1 N0))))))) /\ ((forall x : N, forall p : form, (sizeN (FAll x p)) = (N.add ((BIT1 N0)) (sizeN p))) /\ (forall x : N, forall p : form, (sizeN (FEx x p)) = (N.add ((BIT1 (BIT1 N0))) (sizeN p))))))))))).
Axiom thm_SIZE_FORMSUBST : forall p : form, forall i : N -> term, (sizeN (formsubst i p)) = (sizeN p).
Axiom thm_PPAT_DEF : forall {_189841 : Type'}, forall A : N -> form -> _189841, forall B : N -> form -> _189841, forall C : form -> _189841, forall r : form, (@PPAT _189841 A B C r) = (@COND _189841 (exists x : N, exists p : form, r = (FAll x p)) (A (@ε N (fun x : N => exists p : form, r = (FAll x p))) (@ε form (fun p : form => r = (FAll (@ε N (fun x : N => exists p' : form, r = (FAll x p'))) p)))) (@COND _189841 (exists x : N, exists p : form, r = (FEx x p)) (B (@ε N (fun x : N => exists p : form, r = (FEx x p))) (@ε form (fun p : form => r = (FEx (@ε N (fun x : N => exists p' : form, r = (FEx x p'))) p)))) (C r))).
Axiom thm_PRENEX_DISTINCT : forall x : N, forall y : N, forall p : form, forall q : form, (((FAll x p) = (FAll y q)) = ((x = y) /\ (p = q))) /\ ((((FEx x p) = (FEx y q)) = ((x = y) /\ (p = q))) /\ (~ ((FAll x p) = (FEx y q)))).
Axiom thm_PPAT : forall {A : Type'}, forall A' : N -> form -> A, forall B : N -> form -> A, forall C : form -> A, (forall x : N, forall p : form, (@PPAT A A' B C (FAll x p)) = (A' x p)) /\ ((forall x : N, forall p : form, (@PPAT A A' B C (FEx x p)) = (B x p)) /\ (forall r : form, ((~ (exists x : N, exists p : form, r = (FAll x p))) /\ (~ (exists x : N, exists p : form, r = (FEx x p)))) -> (@PPAT A A' B C r) = (C r))).
Axiom thm_SIZE_REC : forall {_190174 : Type'}, forall H : (form -> _190174) -> form -> _190174, (forall f : form -> _190174, forall g : form -> _190174, forall x : form, (forall z : form, (N.lt (sizeN z) (sizeN x)) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : form -> _190174, forall x : form, (f x) = (H f x).
Axiom thm_PRENEX_RIGHT_EXISTENCE : exists Prenex_right' : form -> form -> form, (forall p : form, forall x : N, forall q : form, (Prenex_right' p (FAll x q)) = (@LET N form (fun y : N => @LET_END form (FAll y (Prenex_right' p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_right' p (FEx x q)) = (@LET N form (fun y : N => @LET_END form (FEx y (Prenex_right' p (formsubst (@valmod term N (@pair N term x (V y)) V) q)))) (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' p q) = (FImp p q))).
Axiom thm_PRENEX_LEFT_EXISTENCE : exists Prenex_left' : form -> form -> form, (forall p : form, forall x : N, forall q : form, (Prenex_left' (FAll x q) p) = (@LET N form (fun y : N => @LET_END form (FEx y (Prenex_left' (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@setU N (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : N, forall q : form, (Prenex_left' (FEx x q) p) = (@LET N form (fun y : N => @LET_END form (FAll y (Prenex_left' (formsubst (@valmod term N (@pair N term x (V y)) V) q) p))) (VARIANT (@setU N (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' q p) = (Prenex_right q p))).
Axiom thm_Prenex_DEF : forall (a : N) (l : list term) (q : form) (x : N) (p : form), ((Prenex FFalse) = FFalse) /\ (((Prenex (Atom a l)) = (Atom a l)) /\ (((Prenex (FImp p q)) = (Prenex_left (Prenex p) (Prenex q))) /\ ((Prenex (FAll x p)) = (FAll x (Prenex p))))).
Axiom thm_PRENEX_RIGHT_FORALL : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (v : N -> A) (p : form) (x : N) (q : form), (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (FImp p (FAll x q))) = (@holds A M v (FAll (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))) (FImp p (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) V) q)))).
Axiom thm_PRENEX_RIGHT_EXISTS : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (v : N -> A) (p : form) (x : N) (q : form), (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (FImp p (FEx x q))) = (@holds A M v (FEx (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))) (FImp p (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) V) q)))).
Axiom thm_PRENEX_DUALITY_LEMMAS : forall {_191050 : Type'} (M : prod (_191050 -> Prop) (prod (N -> (list _191050) -> _191050) (N -> (list _191050) -> Prop))) (v : N -> _191050) (q : form) (x : N) (p : form), ((@holds _191050 M v (FImp (FEx x p) q)) = (@holds _191050 M v (FImp (Not q) (FAll x (Not p))))) /\ ((@holds _191050 M v (FImp (FAll x p) q)) = (@holds _191050 M v (FImp (Not q) (FEx x (Not p))))).
Axiom thm_PRENEX_LEFT_FORALL : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (v : N -> A) (x : N) (p : form) (q : form), (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (FImp (FAll x p) q)) = (@holds A M v (FEx (VARIANT (@setU N (free_variables (FAll x p)) (free_variables q))) (FImp (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables (FAll x p)) (free_variables q))))) V) p) q))).
Axiom thm_PRENEX_LEFT_EXISTS : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (v : N -> A) (x : N) (p : form) (q : form), (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (FImp (FEx x p) q)) = (@holds A M v (FAll (VARIANT (@setU N (free_variables (FEx x p)) (free_variables q))) (FImp (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables (FEx x p)) (free_variables q))))) V) p) q))).
Axiom thm_PRENEX_RIGHT_FORALL_FV : forall (p : form) (x : N) (q : form), (free_variables (FImp p (FAll x q))) = (free_variables (FAll (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))) (FImp p (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) V) q)))).
Axiom thm_PRENEX_RIGHT_EXISTS_FV : forall (p : form) (x : N) (q : form), (free_variables (FImp p (FEx x q))) = (free_variables (FEx (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))) (FImp p (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) V) q)))).
Axiom thm_PRENEX_LEFT_FORALL_FV : forall (x : N) (p : form) (q : form), (free_variables (FImp (FAll x p) q)) = (free_variables (FEx (VARIANT (@setU N (free_variables (FAll x p)) (free_variables q))) (FImp (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables (FAll x p)) (free_variables q))))) V) p) q))).
Axiom thm_PRENEX_LEFT_EXISTS_FV : forall (x : N) (p : form) (q : form), (free_variables (FImp (FEx x p) q)) = (free_variables (FAll (VARIANT (@setU N (free_variables (FEx x p)) (free_variables q))) (FImp (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables (FEx x p)) (free_variables q))))) V) p) q))).
Axiom thm_PRENEX_RIGHT_FORALL_LANGUAGE : forall (p : form) (x : N) (q : form), (language (@INSERT form (FImp p (FAll x q)) (@set0 form))) = (language (@INSERT form (FAll (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))) (FImp p (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables p) (free_variables (FAll x q)))))) V) q))) (@set0 form))).
Axiom thm_PRENEX_RIGHT_EXISTS_LANGUAGE : forall (p : form) (x : N) (q : form), (language (@INSERT form (FImp p (FEx x q)) (@set0 form))) = (language (@INSERT form (FEx (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))) (FImp p (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables p) (free_variables (FEx x q)))))) V) q))) (@set0 form))).
Axiom thm_PRENEX_LEFT_FORALL_LANGUAGE : forall (x : N) (p : form) (q : form), (language (@INSERT form (FImp (FAll x p) q) (@set0 form))) = (language (@INSERT form (FEx (VARIANT (@setU N (free_variables (FAll x p)) (free_variables q))) (FImp (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables (FAll x p)) (free_variables q))))) V) p) q)) (@set0 form))).
Axiom thm_PRENEX_LEFT_EXISTS_LANGUAGE : forall (x : N) (p : form) (q : form), (language (@INSERT form (FImp (FEx x p) q) (@set0 form))) = (language (@INSERT form (FAll (VARIANT (@setU N (free_variables (FEx x p)) (free_variables q))) (FImp (formsubst (@valmod term N (@pair N term x (V (VARIANT (@setU N (free_variables (FEx x p)) (free_variables q))))) V) p) q)) (@set0 form))).
Axiom thm_PRENEX_LEMMA_FORALL : forall {A : Type'} (P : Prop) (r1 : form) (z : N) (r2 : form) (p : form) (x : N) (q : form), (P /\ (((free_variables r1) = (free_variables r2)) /\ (((language (@INSERT form r1 (@set0 form))) = (language (@INSERT form r2 (@set0 form)))) /\ (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v p) = (@holds A M v q))))) -> P /\ (((free_variables (FAll z r1)) = (free_variables (FAll z r2))) /\ (((language (@INSERT form (FAll z r1) (@set0 form))) = (language (@INSERT form (FAll z r2) (@set0 form)))) /\ (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (FAll x p)) = (@holds A M v (FAll x q))))).
Axiom thm_PRENEX_LEMMA_EXISTS : forall {A : Type'} (P : Prop) (r1 : form) (z : N) (r2 : form) (p : form) (x : N) (q : form), (P /\ (((free_variables r1) = (free_variables r2)) /\ (((language (@INSERT form r1 (@set0 form))) = (language (@INSERT form r2 (@set0 form)))) /\ (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v p) = (@holds A M v q))))) -> P /\ (((free_variables (FEx z r1)) = (free_variables (FEx z r2))) /\ (((language (@INSERT form (FEx z r1) (@set0 form))) = (language (@INSERT form (FEx z r2) (@set0 form)))) /\ (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (FEx x p)) = (@holds A M v (FEx x q))))).
Axiom thm_PRENEX_RIGHT_THM : forall {A : Type'}, forall p : form, forall q : form, ((qfree p) /\ (prenex q)) -> (prenex (Prenex_right p q)) /\ (((free_variables (Prenex_right p q)) = (free_variables (FImp p q))) /\ (((language (@INSERT form (Prenex_right p q) (@set0 form))) = (language (@INSERT form (FImp p q) (@set0 form)))) /\ (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (Prenex_right p q)) = (@holds A M v (FImp p q))))).
Axiom thm_PRENEX_LEFT_THM : forall {A : Type'}, forall p : form, forall q : form, ((prenex p) /\ (prenex q)) -> (prenex (Prenex_left p q)) /\ (((free_variables (Prenex_left p q)) = (free_variables (FImp p q))) /\ (((language (@INSERT form (Prenex_left p q) (@set0 form))) = (language (@INSERT form (FImp p q) (@set0 form)))) /\ (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (Prenex_left p q)) = (@holds A M v (FImp p q))))).
Axiom thm_PRENEX_THM : forall {A : Type'}, forall p : form, (prenex (Prenex p)) /\ (((free_variables (Prenex p)) = (free_variables p)) /\ (((language (@INSERT form (Prenex p) (@set0 form))) = (language (@INSERT form p (@set0 form)))) /\ (forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, (~ ((@Dom A M) = (@set0 A))) -> (@holds A M v (Prenex p)) = (@holds A M v p)))).
Axiom thm_HOLDS_EXISTS_LEMMA : forall {A : Type'}, forall p : form, forall t : term, forall x : N, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, forall preds : (prod N N) -> Prop, ((@interpretation A (@pair ((prod N N) -> Prop) ((prod N N) -> Prop) (functions_term t) preds) M) /\ ((@valuation A M v) /\ (@holds A M v (formsubst (@valmod term N (@pair N term x t) V) p)))) -> @holds A M v (FEx x p).
Axiom thm_Skolem1_DEF : forall f : N, forall x : N, forall p : form, (Skolem1 f x p) = (formsubst (@valmod term N (@pair N term x (Fn f (@List.map N term V (@list_of_set N (free_variables (FEx x p)))))) V) p).
Axiom thm_HOLDS_SKOLEM1 : forall {A : Type'}, forall f : N, forall x : N, forall p : form, ((prenex (FEx x p)) /\ (~ (@IN (prod N N) (@pair N N f (@card N (free_variables (FEx x p)))) (functions_form (FEx x p))))) -> (prenex (Skolem1 f x p)) /\ (((free_variables (Skolem1 f x p)) = (free_variables (FEx x p))) /\ ((N.lt (sizeN (Skolem1 f x p)) (sizeN (FEx x p))) /\ (((predicates_form (Skolem1 f x p)) = (predicates_form (FEx x p))) /\ ((@subset (prod N N) (functions_form (FEx x p)) (functions_form (Skolem1 f x p))) /\ ((@subset (prod N N) (functions_form (Skolem1 f x p)) (@INSERT (prod N N) (@pair N N f (@card N (free_variables (FEx x p)))) (functions_form (FEx x p)))) /\ ((forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form p (@set0 form))) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (forall v : N -> A, (@valuation A M v) -> @holds A M v (FEx x p)))) -> exists M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@Dom A M') = (@Dom A M)) /\ (((@Pred A M') = (@Pred A M)) /\ ((forall g : N, forall zs : list A, ((~ (g = f)) \/ (~ ((@lengthN A zs) = (@card N (free_variables (FEx x p)))))) -> (@Fun A M' g zs) = (@Fun A M g zs)) /\ ((@interpretation A (language (@INSERT form (Skolem1 f x p) (@set0 form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (Skolem1 f x p)))))) /\ (forall N' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form (Skolem1 f x p) (@set0 form))) N') /\ (~ ((@Dom A N') = (@set0 A)))) -> forall v : N -> A, ((@valuation A N' v) /\ (@holds A N' v (Skolem1 f x p))) -> @holds A N' v (FEx x p)))))))).
Axiom thm_Skolems_EXISTENCE : forall J : N, exists Skolems' : form -> N -> form, forall r : form, (Skolems' r) = (fun k : N => @PPAT form (fun x : N => fun q : form => FAll x (Skolems' q k)) (fun x : N => fun q : form => Skolems' (Skolem1 (NUMPAIR J k) x q) (N.succ k)) (fun p : form => p) r).
Axiom thm_Skolems_SPECIFICATION : exists Skolems' : N -> form -> N -> form, forall J : N, forall r : form, forall k : N, (Skolems' J r k) = (@PPAT form (fun x : N => fun q : form => FAll x (Skolems' J q k)) (fun x : N => fun q : form => Skolems' J (Skolem1 (NUMPAIR J k) x q) (N.succ k)) (fun p : form => p) r).
Axiom thm_HOLDS_SKOLEMS_INDUCTION : forall {A : Type'}, forall n : N, forall J : N, forall k : N, forall p : form, (((sizeN p) = n) /\ ((prenex p) /\ (forall l : N, forall m : N, (@IN (prod N N) (@pair N N (NUMPAIR J l) m) (functions_form p)) -> N.lt l k))) -> (universal (Skolems J p k)) /\ (((free_variables (Skolems J p k)) = (free_variables p)) /\ (((predicates_form (Skolems J p k)) = (predicates_form p)) /\ ((@subset (prod N N) (functions_form p) (functions_form (Skolems J p k))) /\ ((@subset (prod N N) (functions_form (Skolems J p k)) (@setU (prod N N) (@GSPEC (prod N N) (fun GEN_PVAR_467 : prod N N => exists j : N, exists l : N, exists m : N, @SETSPEC (prod N N) GEN_PVAR_467 ((j = J) /\ (N.le k l)) (@pair N N (NUMPAIR j l) m))) (functions_form p))) /\ ((forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form p (@set0 form))) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (forall v : N -> A, (@valuation A M v) -> @holds A M v p))) -> exists M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@Dom A M') = (@Dom A M)) /\ (((@Pred A M') = (@Pred A M)) /\ ((forall g : N, forall zs : list A, (~ ((@Fun A M' g zs) = (@Fun A M g zs))) -> exists l : N, (N.le k l) /\ (g = (NUMPAIR J l))) /\ ((@interpretation A (language (@INSERT form (Skolems J p k) (@set0 form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (Skolems J p k)))))) /\ (forall N' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form (Skolems J p k) (@set0 form))) N') /\ (~ ((@Dom A N') = (@set0 A)))) -> forall v : N -> A, ((@valuation A N' v) /\ (@holds A N' v (Skolems J p k))) -> @holds A N' v p)))))).
Axiom thm_HOLDS_SKOLEMS_PRENEX : forall {A : Type'}, forall p : form, (prenex p) -> forall K : N, (forall l : N, forall m : N, ~ (@IN (prod N N) (@pair N N (NUMPAIR K l) m) (functions_form p))) -> (universal (Skolems K p N0)) /\ (((free_variables (Skolems K p N0)) = (free_variables p)) /\ (((predicates_form (Skolems K p N0)) = (predicates_form p)) /\ ((@subset (prod N N) (functions_form p) (functions_form (Skolems K p N0))) /\ ((@subset (prod N N) (functions_form (Skolems K p N0)) (@setU (prod N N) (@GSPEC (prod N N) (fun GEN_PVAR_468 : prod N N => exists k : N, exists l : N, exists m : N, @SETSPEC (prod N N) GEN_PVAR_468 (k = K) (@pair N N (NUMPAIR k l) m))) (functions_form p))) /\ ((forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form p (@set0 form))) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (forall v : N -> A, (@valuation A M v) -> @holds A M v p))) -> exists M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@Dom A M') = (@Dom A M)) /\ (((@Pred A M') = (@Pred A M)) /\ ((forall g : N, forall zs : list A, (~ ((@Fun A M' g zs) = (@Fun A M g zs))) -> exists l : N, g = (NUMPAIR K l)) /\ ((@interpretation A (language (@INSERT form (Skolems K p N0) (@set0 form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (Skolems K p N0)))))) /\ (forall N' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form (Skolems K p N0) (@set0 form))) N') /\ (~ ((@Dom A N') = (@set0 A)))) -> forall v : N -> A, ((@valuation A N' v) /\ (@holds A N' v (Skolems K p N0))) -> @holds A N' v p)))))).
Axiom thm_Skopre_DEF : forall K : N, forall p : form, (Skopre K p) = (Skolems K (Prenex p) N0).
Axiom thm_SKOPRE : forall {A : Type'}, forall p : form, forall K : N, (forall l : N, forall m : N, ~ (@IN (prod N N) (@pair N N (NUMPAIR K l) m) (functions_form p))) -> (universal (Skopre K p)) /\ (((free_variables (Skopre K p)) = (free_variables p)) /\ (((predicates_form (Skopre K p)) = (predicates_form p)) /\ ((@subset (prod N N) (functions_form p) (functions_form (Skopre K p))) /\ ((@subset (prod N N) (functions_form (Skopre K p)) (@setU (prod N N) (@GSPEC (prod N N) (fun GEN_PVAR_469 : prod N N => exists k : N, exists l : N, exists m : N, @SETSPEC (prod N N) GEN_PVAR_469 (k = K) (@pair N N (NUMPAIR k l) m))) (functions_form p))) /\ ((forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form p (@set0 form))) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (forall v : N -> A, (@valuation A M v) -> @holds A M v p))) -> exists M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@Dom A M') = (@Dom A M)) /\ (((@Pred A M') = (@Pred A M)) /\ ((forall g : N, forall zs : list A, (~ ((@Fun A M' g zs) = (@Fun A M g zs))) -> exists l : N, g = (NUMPAIR K l)) /\ ((@interpretation A (language (@INSERT form (Skopre K p) (@set0 form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (Skopre K p)))))) /\ (forall N' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form (Skopre K p) (@set0 form))) N') /\ (~ ((@Dom A N') = (@set0 A)))) -> forall v : N -> A, ((@valuation A N' v) /\ (@holds A N' v (Skopre K p))) -> @holds A N' v p)))))).
Axiom thm_bumpmod : forall {_195031 : Type'}, forall M : prod (_195031 -> Prop) (prod (N -> (list _195031) -> _195031) (N -> (list _195031) -> Prop)), (@bumpmod _195031 M) = (@pair (_195031 -> Prop) (prod (N -> (list _195031) -> _195031) (N -> (list _195031) -> Prop)) (@Dom _195031 M) (@pair (N -> (list _195031) -> _195031) (N -> (list _195031) -> Prop) (fun k : N => fun zs : list _195031 => @Fun _195031 M (NUMSND k) zs) (@Pred _195031 M))).
Axiom thm_bumpterm : forall (x : N) (k : N) (l : list term), ((bumpterm (V x)) = (V x)) /\ ((bumpterm (Fn k l)) = (Fn (NUMPAIR N0 k) (@List.map term term bumpterm l))).
Axiom thm_bumpform : forall (p : N) (l : list term) (q : form) (x : N) (r : form), ((bumpform FFalse) = FFalse) /\ (((bumpform (Atom p l)) = (Atom p (@List.map term term bumpterm l))) /\ (((bumpform (FImp q r)) = (FImp (bumpform q) (bumpform r))) /\ ((bumpform (FAll x r)) = (FAll x (bumpform r))))).
Axiom thm_BUMPTERM : forall {_195137 : Type'}, forall M : prod (_195137 -> Prop) (prod (N -> (list _195137) -> _195137) (N -> (list _195137) -> Prop)), forall v : N -> _195137, forall t : term, (@termval _195137 M v t) = (@termval _195137 (@bumpmod _195137 M) v (bumpterm t)).
Axiom thm_BUMPFORM : forall {_195158 : Type'}, forall M : prod (_195158 -> Prop) (prod (N -> (list _195158) -> _195158) (N -> (list _195158) -> Prop)), forall p : form, forall v : N -> _195158, (@holds _195158 M v p) = (@holds _195158 (@bumpmod _195158 M) v (bumpform p)).
Axiom thm_FUNCTIONS_FORM_BUMPFORM : forall p : form, forall f : N, forall m : N, (@IN (prod N N) (@pair N N f m) (functions_form (bumpform p))) -> exists k : N, (f = (NUMPAIR N0 k)) /\ (@IN (prod N N) (@pair N N k m) (functions_form p)).
Axiom thm_BUMPFORM_INTERPRETATION : forall {_195244 : Type'} (p : form) (M : prod (_195244 -> Prop) (prod (N -> (list _195244) -> _195244) (N -> (list _195244) -> Prop))), (@interpretation _195244 (language (@INSERT form p (@set0 form))) M) -> @interpretation _195244 (language (@INSERT form (bumpform p) (@set0 form))) (@bumpmod _195244 M).
Axiom thm_unbumpterm : forall (x : N) (k : N) (l : list term), ((unbumpterm (V x)) = (V x)) /\ ((unbumpterm (Fn k l)) = (Fn (NUMSND k) (@List.map term term unbumpterm l))).
Axiom thm_unbumpform : forall (p : N) (l : list term) (q : form) (x : N) (r : form), ((unbumpform FFalse) = FFalse) /\ (((unbumpform (Atom p l)) = (Atom p (@List.map term term unbumpterm l))) /\ (((unbumpform (FImp q r)) = (FImp (unbumpform q) (unbumpform r))) /\ ((unbumpform (FAll x r)) = (FAll x (unbumpform r))))).
Axiom thm_UNBUMPTERM : forall t : term, (unbumpterm (bumpterm t)) = t.
Axiom thm_UNBUMPFORM : forall p : form, (unbumpform (bumpform p)) = p.
Axiom thm_unbumpmod : forall {_195355 : Type'}, forall M : prod (_195355 -> Prop) (prod (N -> (list _195355) -> _195355) (N -> (list _195355) -> Prop)), (@unbumpmod _195355 M) = (@pair (_195355 -> Prop) (prod (N -> (list _195355) -> _195355) (N -> (list _195355) -> Prop)) (@Dom _195355 M) (@pair (N -> (list _195355) -> _195355) (N -> (list _195355) -> Prop) (fun k : N => fun zs : list _195355 => @Fun _195355 M (NUMPAIR N0 k) zs) (@Pred _195355 M))).
Axiom thm_UNBUMPMOD_TERM : forall {_195398 : Type'}, forall M : prod (_195398 -> Prop) (prod (N -> (list _195398) -> _195398) (N -> (list _195398) -> Prop)), forall v : N -> _195398, forall t : term, (@termval _195398 M v (bumpterm t)) = (@termval _195398 (@unbumpmod _195398 M) v t).
Axiom thm_UNBUMPMOD : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall p : form, forall v : N -> A, (@holds A M v (bumpform p)) = (@holds A (@unbumpmod A M) v p).
Axiom thm_NUMLIST : forall (h : N) (t : list N), ((NUMLIST (@nil N)) = N0) /\ ((NUMLIST (@cons N h t)) = (N.add (NUMPAIR h (NUMLIST t)) ((BIT1 N0)))).
Axiom thm_NUMLIST_INJ : forall l1 : list N, forall l2 : list N, ((NUMLIST l1) = (NUMLIST l2)) = (l1 = l2).
Axiom thm_NUM_OF_TERM_INJ : forall s : term, forall t : term, ((num_of_term s) = (num_of_term t)) = (s = t).
Axiom thm_num_of_form : forall (p : N) (l : list term) (r : form) (x : N) (q : form), ((num_of_form FFalse) = (NUMPAIR N0 N0)) /\ (((num_of_form (Atom p l)) = (NUMPAIR ((BIT1 N0)) (NUMPAIR p (NUMLIST (@List.map term N num_of_term l))))) /\ (((num_of_form (FImp q r)) = (NUMPAIR ((BIT0 (BIT1 N0))) (NUMPAIR (num_of_form q) (num_of_form r)))) /\ ((num_of_form (FAll x q)) = (NUMPAIR ((BIT1 (BIT1 N0))) (NUMPAIR x (num_of_form q)))))).
Axiom thm_NUMLIST_NUM_OF_TERM : forall l1 : list term, forall l2 : list term, ((NUMLIST (@List.map term N num_of_term l1)) = (NUMLIST (@List.map term N num_of_term l2))) = (l1 = l2).
Axiom thm_NUM_OF_FORM_INJ : forall q : form, forall r : form, ((num_of_form q) = (num_of_form r)) = (q = r).
Axiom thm_form_of_num : forall x : N, (form_of_num x) = (@ε form (fun p : form => (num_of_form p) = x)).
Axiom thm_FORM_OF_NUM : forall (p : form), (form_of_num (num_of_form p)) = p.
Axiom thm_SKOLEMIZE : forall p : form, (SKOLEMIZE p) = (Skopre (N.add (num_of_form (bumpform p)) ((BIT1 N0))) (bumpform p)).
Axiom thm_SKOLEMIZE_WORKS : forall {A : Type'}, forall p : form, (universal (SKOLEMIZE p)) /\ (((free_variables (SKOLEMIZE p)) = (free_variables (bumpform p))) /\ (((predicates_form (SKOLEMIZE p)) = (predicates_form (bumpform p))) /\ ((@subset (prod N N) (functions_form (bumpform p)) (functions_form (SKOLEMIZE p))) /\ ((@subset (prod N N) (functions_form (SKOLEMIZE p)) (@setU (prod N N) (@GSPEC (prod N N) (fun GEN_PVAR_470 : prod N N => exists k : N, exists l : N, exists m : N, @SETSPEC (prod N N) GEN_PVAR_470 (k = (N.add (num_of_form (bumpform p)) ((BIT1 N0)))) (@pair N N (NUMPAIR k l) m))) (functions_form (bumpform p)))) /\ ((forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form (bumpform p) (@set0 form))) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (forall v : N -> A, (@valuation A M v) -> @holds A M v (bumpform p)))) -> exists M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@Dom A M') = (@Dom A M)) /\ (((@Pred A M') = (@Pred A M)) /\ ((forall g : N, forall zs : list A, (~ ((@Fun A M' g zs) = (@Fun A M g zs))) -> exists l : N, g = (NUMPAIR (N.add (num_of_form (bumpform p)) ((BIT1 N0))) l)) /\ ((@interpretation A (language (@INSERT form (SKOLEMIZE p) (@set0 form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (SKOLEMIZE p)))))) /\ (forall N' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@interpretation A (language (@INSERT form (SKOLEMIZE p) (@set0 form))) N') /\ (~ ((@Dom A N') = (@set0 A)))) -> forall v : N -> A, ((@valuation A N' v) /\ (@holds A N' v (SKOLEMIZE p))) -> @holds A N' v (bumpform p))))))).
Axiom thm_FUNCTIONS_FORM_SKOLEMIZE : forall p : form, forall f : N, forall m : N, (@IN (prod N N) (@pair N N f m) (functions_form (SKOLEMIZE p))) -> (exists k : N, (f = (NUMPAIR N0 k)) /\ (@IN (prod N N) (@pair N N k m) (functions_form p))) \/ (exists l : N, f = (NUMPAIR (N.add (num_of_form (bumpform p)) ((BIT1 N0))) l)).
Axiom thm_SKOMOD1 : forall {A : Type'}, forall p : form, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@SKOMOD1 A p M) = (@COND (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (forall v : N -> A, (@valuation A M v) -> @holds A M v p) (@ε (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (fun M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => ((@Dom A M') = (@Dom A (@bumpmod A M))) /\ (((@Pred A M') = (@Pred A (@bumpmod A M))) /\ ((forall g : N, forall zs : list A, (~ ((@Fun A M' g zs) = (@Fun A (@bumpmod A M) g zs))) -> exists l : N, g = (NUMPAIR (N.add (num_of_form (bumpform p)) ((BIT1 N0))) l)) /\ ((@interpretation A (language (@INSERT form (SKOLEMIZE p) (@set0 form))) M') /\ (forall v : N -> A, (@valuation A M' v) -> @holds A M' v (SKOLEMIZE p))))))) (@pair (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) (@Dom A M) (@pair (N -> (list A) -> A) (N -> (list A) -> Prop) (fun g : N => fun zs : list A => @ε A (fun a : A => @IN A a (@Dom A M))) (@Pred A M)))).
Axiom thm_SKOMOD1_WORKS : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall p : form, ((@interpretation A (language (@INSERT form p (@set0 form))) M) /\ (~ ((@Dom A M) = (@set0 A)))) -> ((@Dom A (@SKOMOD1 A p M)) = (@Dom A (@bumpmod A M))) /\ (((@Pred A (@SKOMOD1 A p M)) = (@Pred A (@bumpmod A M))) /\ ((@interpretation A (language (@INSERT form (SKOLEMIZE p) (@set0 form))) (@SKOMOD1 A p M)) /\ ((forall v : N -> A, (@valuation A M v) -> @holds A M v p) -> (forall g : N, forall zs : list A, (~ ((@Fun A (@SKOMOD1 A p M) g zs) = (@Fun A (@bumpmod A M) g zs))) -> exists l : N, g = (NUMPAIR (N.add (num_of_form (bumpform p)) ((BIT1 N0))) l)) /\ (forall v : N -> A, (@valuation A (@SKOMOD1 A p M) v) -> @holds A (@SKOMOD1 A p M) v (SKOLEMIZE p))))).
Axiom thm_SKOMOD : forall {_196408 : Type'}, forall M : prod (_196408 -> Prop) (prod (N -> (list _196408) -> _196408) (N -> (list _196408) -> Prop)), (@SKOMOD _196408 M) = (@pair (_196408 -> Prop) (prod (N -> (list _196408) -> _196408) (N -> (list _196408) -> Prop)) (@Dom _196408 M) (@pair (N -> (list _196408) -> _196408) (N -> (list _196408) -> Prop) (fun g : N => fun zs : list _196408 => @COND _196408 ((NUMFST g) = N0) (@Fun _196408 M (NUMSND g) zs) (@Fun _196408 (@SKOMOD1 _196408 (unbumpform (form_of_num (N.pred (NUMFST g)))) M) g zs)) (@Pred _196408 M))).
Axiom thm_SKOMOD_INTERPRETATION : forall {A : Type'} (p : form) (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))), ((@interpretation A (language (@INSERT form p (@set0 form))) M) /\ (~ ((@Dom A M) = (@set0 A)))) -> @interpretation A (language (@INSERT form (SKOLEMIZE p) (@set0 form))) (@SKOMOD A M).
Axiom thm_SKOMOD_WORKS : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (p : form), ((@interpretation A (language (@INSERT form p (@set0 form))) M) /\ (~ ((@Dom A M) = (@set0 A)))) -> (forall v : N -> A, (@valuation A M v) -> @holds A M v p) = (forall v : N -> A, (@valuation A (@SKOMOD A M) v) -> @holds A (@SKOMOD A M) v (SKOLEMIZE p)).
Axiom thm_SKOLEMIZE_SATISFIABLE : forall {A : Type'} (s : form -> Prop), (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) /\ ((@interpretation A (language s) M) /\ (@satisfies A M s))) = (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) /\ ((@interpretation A (language (@GSPEC form (fun GEN_PVAR_472 : form => exists p : form, @SETSPEC form GEN_PVAR_472 (@IN form p s) (SKOLEMIZE p)))) M) /\ (@satisfies A M (@GSPEC form (fun GEN_PVAR_473 : form => exists p : form, @SETSPEC form GEN_PVAR_473 (@IN form p s) (SKOLEMIZE p)))))).
Axiom thm_specialize : forall (p : N) (l : list term) (q : form) (x : N) (r : form), ((specialize FFalse) = FFalse) /\ (((specialize (Atom p l)) = (Atom p l)) /\ (((specialize (FImp q r)) = (FImp q r)) /\ ((specialize (FAll x r)) = (specialize r)))).
Axiom thm_SPECIALIZE_SATISFIES : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall s : form -> Prop, (~ ((@Dom A M) = (@set0 A))) -> (@satisfies A M s) = (@satisfies A M (@GSPEC form (fun GEN_PVAR_474 : form => exists p : form, @SETSPEC form GEN_PVAR_474 (@IN form p s) (specialize p)))).
Axiom thm_SPECIALIZE_QFREE : forall p : form, (universal p) -> qfree (specialize p).
Axiom thm_SPECIALIZE_LANGUAGE : forall s : form -> Prop, (language (@GSPEC form (fun GEN_PVAR_475 : form => exists p : form, @SETSPEC form GEN_PVAR_475 (@IN form p s) (specialize p)))) = (language s).
Axiom thm_SKOLEM : forall p : form, (SKOLEM p) = (specialize (SKOLEMIZE p)).
Axiom thm_SKOLEM_QFREE : forall p : form, qfree (SKOLEM p).
Axiom thm_SKOLEM_SATISFIABLE : forall {A : Type'} (s : form -> Prop), (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) /\ ((@interpretation A (language s) M) /\ (@satisfies A M s))) = (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) /\ ((@interpretation A (language (@GSPEC form (fun GEN_PVAR_476 : form => exists p : form, @SETSPEC form GEN_PVAR_476 (@IN form p s) (SKOLEM p)))) M) /\ (@satisfies A M (@GSPEC form (fun GEN_PVAR_477 : form => exists p : form, @SETSPEC form GEN_PVAR_477 (@IN form p s) (SKOLEM p)))))).
Axiom thm_pholds : forall (p : N) (l : list term) (r : form) (v : form -> Prop) (x : N) (q : form), ((pholds v FFalse) = False) /\ (((pholds v (Atom p l)) = (v (Atom p l))) /\ (((pholds v (FImp q r)) = ((pholds v q) -> pholds v r)) /\ ((pholds v (FAll x q)) = (v (FAll x q))))).
Axiom thm_PHOLDS : forall (p : N) (l : list term) (q : form) (v : form -> Prop) (r : form), ((pholds v FFalse) = False) /\ (((pholds v FTrue) = True) /\ (((pholds v (Atom p l)) = (v (Atom p l))) /\ (((pholds v (Not q)) = (~ (pholds v q))) /\ (((pholds v (FOr q r)) = ((pholds v q) \/ (pholds v r))) /\ (((pholds v (FAnd q r)) = ((pholds v q) /\ (pholds v r))) /\ (((pholds v (FImp q r)) = ((pholds v q) -> pholds v r)) /\ ((pholds v (FEquiv q r)) = ((pholds v q) = (pholds v r))))))))).
Axiom thm_psatisfies : forall s : form -> Prop, forall v : form -> Prop, (psatisfies v s) = (forall p : form, (@IN form p s) -> pholds v p).
Axiom thm_psatisfiable : forall s : form -> Prop, (psatisfiable s) = (exists v : form -> Prop, forall p : form, (@IN form p s) -> pholds v p).
Axiom thm_PSATISFIABLE_MONO : forall A : form -> Prop, forall B : form -> Prop, ((psatisfiable A) /\ (@subset form B A)) -> psatisfiable B.
Axiom thm_finsat : forall A : form -> Prop, (finsat A) = (forall B : form -> Prop, ((@subset form B A) /\ (@finite_set form B)) -> psatisfiable B).
Axiom thm_FINSAT_MONO : forall A : form -> Prop, forall B : form -> Prop, ((finsat A) /\ (@subset form B A)) -> finsat B.
Axiom thm_SATISFIABLE_MONO : forall A : form -> Prop, forall B : form -> Prop, ((psatisfiable A) /\ (@subset form B A)) -> psatisfiable B.
Axiom thm_FINSAT_SATISFIABLE : forall (B : form -> Prop), (psatisfiable B) -> finsat B.
Axiom thm_FINSAT_MAX : forall A : form -> Prop, (finsat A) -> exists B : form -> Prop, (@subset form A B) /\ ((finsat B) /\ (forall C : form -> Prop, ((@subset form B C) /\ (finsat C)) -> C = B)).
Axiom thm_FINSAT_EXTEND : forall (p : form) (B : form -> Prop), (finsat B) -> (finsat (@INSERT form p B)) \/ (finsat (@INSERT form (Not p) B)).
Axiom thm_FINSAT_MAX_COMPLETE : forall (B : form -> Prop), ((finsat B) /\ (forall C : form -> Prop, ((@subset form B C) /\ (finsat C)) -> C = B)) -> forall p : form, (@IN form p B) \/ (@IN form (Not p) B).
Axiom thm_FINSAT_MAX_COMPLETE_STRONG : forall (B : form -> Prop), ((finsat B) /\ (forall C : form -> Prop, ((@subset form B C) /\ (finsat C)) -> C = B)) -> forall p : form, (@IN form (Not p) B) = (~ (@IN form p B)).
Axiom thm_FINSAT_DEDUCTION : forall (B : form -> Prop), ((finsat B) /\ (forall C : form -> Prop, ((@subset form B C) /\ (finsat C)) -> C = B)) -> forall p : form, (@IN form p B) = (exists A : form -> Prop, (@finite_set form A) /\ ((@subset form A B) /\ (forall v : form -> Prop, (forall q : form, (@IN form q A) -> pholds v q) -> pholds v p))).
Axiom thm_FINSAT_MAX_CONSISTENT : forall (B : form -> Prop), ((finsat B) /\ (forall C : form -> Prop, ((@subset form B C) /\ (finsat C)) -> C = B)) -> ~ (@IN form FFalse B).
Axiom thm_FINSAT_MAX_HOMO : forall (B : form -> Prop), ((finsat B) /\ (forall C : form -> Prop, ((@subset form B C) /\ (finsat C)) -> C = B)) -> forall p : form, forall q : form, (@IN form (FImp p q) B) = ((@IN form p B) -> @IN form q B).
Axiom thm_COMPACT_PROP : forall (A : form -> Prop), (forall B : form -> Prop, ((@finite_set form B) /\ (@subset form B A)) -> exists d : form -> Prop, forall r : form, (@IN form r B) -> pholds d r) -> exists d : form -> Prop, forall r : form, (@IN form r A) -> pholds d r.
Axiom thm_COMPACT_PROP_ALT : forall A : form -> Prop, (forall d : form -> Prop, exists p : form, (@IN form p A) /\ (pholds d p)) -> exists B : form -> Prop, (@finite_set form B) /\ ((@subset form B A) /\ (forall d : form -> Prop, exists p : form, (@IN form p B) /\ (pholds d p))).
Axiom thm_FINITE_DISJ_LEMMA : forall A : form -> Prop, (@finite_set form A) -> exists ps : list form, (@List.Forall form (fun p : form => @IN form p A) ps) /\ (forall d : form -> Prop, (pholds d (@fold_right_with_perm_args form form FOr ps FFalse)) = (exists p : form, (@IN form p A) /\ (pholds d p))).
Axiom thm_COMPACT_DISJ : forall A : form -> Prop, (forall d : form -> Prop, exists p : form, (@IN form p A) /\ (pholds d p)) -> exists ps : list form, (@List.Forall form (fun p : form => @IN form p A) ps) /\ (forall d : form -> Prop, pholds d (@fold_right_with_perm_args form form FOr ps FFalse)).
Axiom thm_terms_CASES : forall fns : (prod N N) -> Prop, forall a : term, (terms fns a) = ((exists x : N, a = (V x)) \/ (exists f : N, exists l : list term, (a = (Fn f l)) /\ ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term (terms fns) l)))).
Axiom thm_terms_INDUCT : forall fns : (prod N N) -> Prop, forall terms' : term -> Prop, ((forall x : N, terms' (V x)) /\ (forall f : N, forall l : list term, ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term terms' l)) -> terms' (Fn f l))) -> forall a : term, (terms fns a) -> terms' a.
Axiom thm_terms_RULES : forall fns : (prod N N) -> Prop, (forall x : N, terms fns (V x)) /\ (forall f : N, forall l : list term, ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term (terms fns) l)) -> terms fns (Fn f l)).
Axiom thm_STUPID_CANONDOM_LEMMA : forall {_198415 : Type'} (L : prod ((prod N N) -> Prop) _198415), forall t : term, (@IN term t (terms (@fst ((prod N N) -> Prop) _198415 L))) -> @subset (prod N N) (functions_term t) (@fst ((prod N N) -> Prop) _198415 L).
Axiom thm_FINITE_SUBSET_INSTANCE : forall (s : form -> Prop) (P : (N -> term) -> Prop), forall t' : form -> Prop, (@finite_set form t') -> (@subset form t' (@GSPEC form (fun GEN_PVAR_483 : form => exists v : N -> term, exists p : form, @SETSPEC form GEN_PVAR_483 ((P v) /\ (@IN form p s)) (formsubst v p)))) -> exists t : form -> Prop, (@finite_set form t) /\ ((@subset form t s) /\ (@subset form t' (@GSPEC form (fun GEN_PVAR_484 : form => exists v : N -> term, exists p : form, @SETSPEC form GEN_PVAR_484 ((P v) /\ (@IN form p t)) (formsubst v p))))).
Axiom thm_FINITE_SUBSET_SKOLEM : forall s : form -> Prop, forall u : form -> Prop, (@finite_set form u) -> (@subset form u (@GSPEC form (fun GEN_PVAR_487 : form => exists p : form, @SETSPEC form GEN_PVAR_487 (@IN form p s) (SKOLEM p)))) -> exists t : form -> Prop, (@finite_set form t) /\ ((@subset form t s) /\ (u = (@GSPEC form (fun GEN_PVAR_488 : form => exists p : form, @SETSPEC form GEN_PVAR_488 (@IN form p t) (SKOLEM p))))).
Axiom thm_VALUATION_EXISTS : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) -> exists v : N -> A, @valuation A M v.
Axiom thm_HOLDS_ITLIST_EXISTS : forall {A : Type'} (p : form), forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall xs : list N, forall v : N -> A, (@holds A M v (@fold_right_with_perm_args N form FEx xs p)) = (exists _as : list A, ((@lengthN A _as) = (@lengthN N xs)) /\ ((@List.Forall A (@Dom A M) _as) /\ (@holds A M (@fold_right_with_perm_args (prod N A) (N -> A) (@valmod A N) (@List.rev (prod N A) (@map2 N A (prod N A) (fun x : N => fun a : A => @pair N A x a) xs _as)) v) p))).
Axiom thm_canonical : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (canonical L M) = (((@Dom term M) = (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) L))) /\ (forall f : N, (@Fun term M f) = (Fn f))).
Axiom thm_prop_of_model : forall {_198913 : Type'}, forall M : prod (_198913 -> Prop) (prod (N -> (list _198913) -> _198913) (N -> (list _198913) -> Prop)), forall v : N -> _198913, forall p : N, forall l : list term, (@holds _198913 M v (Atom p l)) = (@holds _198913 M v (Atom p l)).
Axiom thm_canon_of_prop : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall d : form -> Prop, (canon_of_prop L d) = (@pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) L)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun l : list term => d (Atom p l)))).
Axiom thm_PHOLDS_PROP_OF_MODEL : forall {_198955 : Type'} (M : prod (_198955 -> Prop) (prod (N -> (list _198955) -> _198955) (N -> (list _198955) -> Prop))) (v : N -> _198955), forall p : form, (qfree p) -> (pholds (@holds _198955 M v) p) = (@holds _198955 M v p).
Axiom thm_PROP_OF_CANON_OF_PROP : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop), forall p : N, forall l : list term, (@holds term (canon_of_prop L d) V (Atom p l)) = (d (Atom p l)).
Axiom thm_HOLDS_CANON_OF_PROP : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop), forall p : form, (qfree p) -> (@holds term (canon_of_prop L d) V p) = (pholds d p).
Axiom thm_HOLDS_CANON_OF_PROP_GENERAL : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop) (v : N -> term) (p : form), (qfree p) -> (@holds term (canon_of_prop L d) v p) = (pholds d (formsubst v p)).
Axiom thm_CANONICAL_CANON_OF_PROP : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)), forall d : form -> Prop, canonical L (canon_of_prop L d).
Axiom thm_INTERPRETATION_CANON_OF_PROP : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall d : form -> Prop, @interpretation term L (canon_of_prop L d).
Axiom thm_PROP_VALID_IMP_FOL_VALID : forall {_199075 : Type'}, forall p : form, ((qfree p) /\ (forall d : form -> Prop, pholds d p)) -> forall M : prod (_199075 -> Prop) (prod (N -> (list _199075) -> _199075) (N -> (list _199075) -> Prop)), forall v : N -> _199075, @holds _199075 M v p.
Axiom thm_FOL_VALID_IMP_PROP_VALID : forall p : form, ((qfree p) /\ (forall C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), forall v : N -> term, (canonical (language (@INSERT form p (@set0 form))) C) -> @holds term C v p)) -> forall d : form -> Prop, pholds d p.
Axiom thm_SATISFIES_PSATISFIES : forall {_199132 : Type'} (M : prod (_199132 -> Prop) (prod (N -> (list _199132) -> _199132) (N -> (list _199132) -> Prop))) (v : N -> _199132) (s : form -> Prop), ((forall p : form, (@IN form p s) -> qfree p) /\ ((@satisfies _199132 M s) /\ (@valuation _199132 M v))) -> psatisfies (@holds _199132 M v) s.
Axiom thm_PSATISFIES_INSTANCES : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop) (s : form -> Prop), ((forall p : form, (@IN form p s) -> qfree p) /\ (psatisfies d (@GSPEC form (fun GEN_PVAR_489 : form => exists v : N -> term, exists p : form, @SETSPEC form GEN_PVAR_489 ((forall x : N, @IN term (v x) (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) L))) /\ (@IN form p s)) (formsubst v p))))) -> @satisfies term (canon_of_prop L d) s.
Axiom thm_SATISFIES_INSTANCES : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall s : form -> Prop, forall t : form -> Prop, (@interpretation A (language t) M) -> (@satisfies A M (@GSPEC form (fun GEN_PVAR_490 : form => exists i : N -> term, exists p : form, @SETSPEC form GEN_PVAR_490 ((@IN form p s) /\ (forall x : N, @IN term (i x) (terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) (language t))))) (formsubst i p)))) = (@satisfies A M s).
Axiom thm_COMPACT_CANON_QFREE : forall {A : Type'} (ss : form -> Prop) (s : form -> Prop), ((forall p : form, (@IN form p s) -> qfree p) /\ (forall t : form -> Prop, ((@finite_set form t) /\ (@subset form t s)) -> exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language ss) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M t)))) -> exists C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (@interpretation term (language ss) C) /\ ((canonical (language ss) C) /\ (@satisfies term C s)).
Axiom thm_INTERPRETATION_RESTRICTLANGUAGE : forall {_199574 : Type'}, forall M : prod (_199574 -> Prop) (prod (N -> (list _199574) -> _199574) (N -> (list _199574) -> Prop)), forall s : form -> Prop, forall t : form -> Prop, ((@subset form t s) /\ (@interpretation _199574 (language s) M)) -> @interpretation _199574 (language t) M.
Axiom thm_INTERPRETATION_EXTENDLANGUAGE : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall s : form -> Prop, forall t : form -> Prop, ((@interpretation A (language t) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M t))) -> exists M' : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), ((@Dom A M') = (@Dom A M)) /\ (((@Pred A M') = (@Pred A M)) /\ ((@interpretation A (language s) M') /\ (@satisfies A M' t))).
Axiom thm_COMPACT_LS : forall {A : Type'} (s : form -> Prop), (forall t : form -> Prop, ((@finite_set form t) /\ (@subset form t s)) -> exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M t))) -> exists C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (@interpretation term (language s) C) /\ ((~ ((@Dom term C) = (@set0 term))) /\ (@satisfies term C s)).
Axiom thm_CANON : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall s : form -> Prop, ((@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ ((forall p : form, (@IN form p s) -> qfree p) /\ (@satisfies A M s)))) -> exists C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (@interpretation term (language s) C) /\ ((~ ((@Dom term C) = (@set0 term))) /\ (@satisfies term C s)).
Axiom thm_term_of_num : forall n : N, (term_of_num n) = (@ε term (fun t : term => (num_of_term t) = n)).
Axiom thm_TERM_OF_NUM : forall (t : term), (term_of_num (num_of_term t)) = t.
Axiom thm_LOWMOD : forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (LOWMOD M) = (@pair (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) (@GSPEC N (fun GEN_PVAR_501 : N => exists t : term, @SETSPEC N GEN_PVAR_501 (@IN term t (@Dom term M)) (num_of_term t))) (@pair (N -> (list N) -> N) (N -> (list N) -> Prop) (fun g : N => fun zs : list N => num_of_term (@Fun term M g (@List.map N term term_of_num zs))) (fun p : N => fun zs : list N => @Pred term M p (@List.map N term term_of_num zs)))).
Axiom thm_LOWMOD_DOM_EMPTY : forall (M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop))), ((@Dom N (LOWMOD M)) = (@set0 N)) = ((@Dom term M) = (@set0 term)).
Axiom thm_LOWMOD_TERMVAL : forall (M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop))), forall v : N -> N, (@valuation N (LOWMOD M) v) -> forall t : term, (@termval N (LOWMOD M) v t) = (num_of_term (@termval term M (@o N N term term_of_num v) t)).
Axiom thm_LOWMOD_HOLDS : forall (M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop))), forall p : form, forall v : N -> N, (@valuation N (LOWMOD M) v) -> (@holds N (LOWMOD M) v p) = (@holds term M (@o N N term term_of_num v) p).
Axiom thm_LOWMOD_INTERPRETATION : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (@interpretation N L (LOWMOD M)) = (@interpretation term L M).
Axiom thm_LS : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall s : form -> Prop, ((@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ ((forall p : form, (@IN form p s) -> qfree p) /\ (@satisfies A M s)))) -> exists N' : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), (@interpretation N (language s) N') /\ ((~ ((@Dom N N') = (@set0 N))) /\ (@satisfies N N' s)).
Axiom thm_UNIFORMITY : forall (xs : list N) (p : form), ((qfree p) /\ (forall C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), forall v : N -> term, ((~ ((@Dom term C) = (@set0 term))) /\ (@valuation term C v)) -> @holds term C v (@fold_right_with_perm_args N form FEx xs p))) -> exists is : list (N -> term), (forall i : N -> term, forall x : N, (@List.In (N -> term) i is) -> terms (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) (language (@INSERT form p (@set0 form)))) (i x)) /\ (forall d : form -> Prop, pholds d (@fold_right_with_perm_args form form FOr (@List.map (N -> term) form (fun i : N -> term => formsubst i p) is) FFalse)).
Axiom thm_herbase_CASES : forall fns : (prod N N) -> Prop, forall a : term, (herbase fns a) = (((a = (V N0)) /\ (~ (exists c : N, @IN (prod N N) (@pair N N c N0) fns))) \/ (exists f : N, exists l : list term, (a = (Fn f l)) /\ ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term (herbase fns) l)))).
Axiom thm_herbase_INDUCT : forall fns : (prod N N) -> Prop, forall herbase' : term -> Prop, (((~ (exists c : N, @IN (prod N N) (@pair N N c N0) fns)) -> herbase' (V N0)) /\ (forall f : N, forall l : list term, ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term herbase' l)) -> herbase' (Fn f l))) -> forall a : term, (herbase fns a) -> herbase' a.
Axiom thm_herbase_RULES : forall fns : (prod N N) -> Prop, ((~ (exists c : N, @IN (prod N N) (@pair N N c N0) fns)) -> herbase fns (V N0)) /\ (forall f : N, forall l : list term, ((@IN (prod N N) (@pair N N f (@lengthN term l)) fns) /\ (@List.Forall term (herbase fns) l)) -> herbase fns (Fn f l)).
Axiom thm_herbrand : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (herbrand L M) = (((@Dom term M) = (herbase (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) L))) /\ (forall f : N, (@Fun term M f) = (Fn f))).
Axiom thm_HERBRAND_INTERPRETATION : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (herbrand L M) -> @interpretation term L M.
Axiom thm_HERBASE_FUNCTIONS : forall fns : (prod N N) -> Prop, forall t : term, (@IN term t (herbase fns)) -> @subset (prod N N) (functions_term t) fns.
Axiom thm_HERBASE_NONEMPTY : forall fns : (prod N N) -> Prop, exists t : term, @IN term t (herbase fns).
Axiom thm_HERBRAND_NONEMPTY : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (herbrand L M) -> ~ ((@Dom term M) = (@set0 term)).
Axiom thm_herbrand_of_prop : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall d : form -> Prop, (herbrand_of_prop L d) = (@pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (herbase (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) L)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun l : list term => d (Atom p l)))).
Axiom thm_PROP_OF_HERBRAND_OF_PROP : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop), forall p : N, forall l : list term, (@holds term (herbrand_of_prop L d) V (Atom p l)) = (d (Atom p l)).
Axiom thm_HOLDS_HERBRAND_OF_PROP : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop), forall p : form, (qfree p) -> (@holds term (herbrand_of_prop L d) V p) = (pholds d p).
Axiom thm_HOLDS_HERBRAND_OF_PROP_GENERAL : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop) (v : N -> term) (p : form), (qfree p) -> (@holds term (herbrand_of_prop L d) v p) = (pholds d (formsubst v p)).
Axiom thm_HERBRAND_HERBRAND_OF_PROP : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)), forall d : form -> Prop, herbrand L (herbrand_of_prop L d).
Axiom thm_INTERPRETATION_HERBRAND_OF_PROP : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), forall d : form -> Prop, @interpretation term L (herbrand_of_prop L d).
Axiom thm_PSATISFIES_HERBRAND_INSTANCES : forall (L : prod ((prod N N) -> Prop) ((prod N N) -> Prop)) (d : form -> Prop) (s : form -> Prop), ((forall p : form, (@IN form p s) -> qfree p) /\ (psatisfies d (@GSPEC form (fun GEN_PVAR_506 : form => exists v : N -> term, exists p : form, @SETSPEC form GEN_PVAR_506 ((forall x : N, @IN term (v x) (herbase (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) L))) /\ (@IN form p s)) (formsubst v p))))) -> @satisfies term (herbrand_of_prop L d) s.
Axiom thm_SATISFIES_SUBSET : forall {_201125 : Type'}, forall M : prod (_201125 -> Prop) (prod (N -> (list _201125) -> _201125) (N -> (list _201125) -> Prop)), forall s : form -> Prop, forall t : form -> Prop, ((@subset form s t) /\ (@satisfies _201125 M t)) -> @satisfies _201125 M s.
Axiom thm_HERBASE_SUBSET_TERMS : forall (fns : (prod N N) -> Prop), forall t : term, (@IN term t (herbase fns)) -> @IN term t (terms fns).
Axiom thm_HERBRAND_THEOREM : forall s : form -> Prop, (forall p : form, (@IN form p s) -> qfree p) -> (exists M : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (@interpretation term (language s) M) /\ ((~ ((@Dom term M) = (@set0 term))) /\ (@satisfies term M s))) = (exists d : form -> Prop, psatisfies d (@GSPEC form (fun GEN_PVAR_507 : form => exists v : N -> term, exists p : form, @SETSPEC form GEN_PVAR_507 ((forall x : N, @IN term (v x) (herbase (functions s))) /\ (@IN form p s)) (formsubst v p)))).
Axiom thm_Equal_DEF : forall s : term, forall t : term, (FEq s t) = (Atom N0 (@cons term s (@cons term t (@nil term)))).
Axiom thm_uclose : forall p : form, (uclose p) = (@fold_right_with_perm_args N form FAll (@list_of_set N (free_variables p)) p).
Axiom thm_normal : forall {_201285 : Type'}, forall fns : (prod N N) -> Prop, forall M : prod (_201285 -> Prop) (prod (N -> (list _201285) -> _201285) (N -> (list _201285) -> Prop)), (@normal _201285 fns M) = (forall s : term, forall t : term, forall v : N -> _201285, ((@valuation _201285 M v) /\ ((@IN term s (terms fns)) /\ (@IN term t (terms fns)))) -> (@holds _201285 M v (FEq s t)) = ((@termval _201285 M v s) = (@termval _201285 M v t))).
Axiom thm_Varpairs_DEF : forall (n : N), ((Varpairs N0) = (@nil (prod term term))) /\ ((Varpairs (N.succ n)) = (@cons (prod term term) (@pair term term (V (N.mul ((BIT0 (BIT1 N0))) n)) (V (N.add (N.mul ((BIT0 (BIT1 N0))) n) ((BIT1 N0))))) (Varpairs n))).
Axiom thm_Eqaxiom_Func : forall f : N, forall n : N, (Eqaxiom_Func (@pair N N f n)) = (uclose (FImp (@fold_right_with_perm_args form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f' : (prod term term) -> form => forall s : term, forall t : term, @eq form (f' (@pair term term s t)) (FEq s t))) (Varpairs n)) FTrue) (FEq (Fn f (@List.map (prod term term) term (@fst term term) (Varpairs n))) (Fn f (@List.map (prod term term) term (@snd term term) (Varpairs n)))))).
Axiom thm_Eqaxiom_Pred : forall p : N, forall n : N, (Eqaxiom_Pred (@pair N N p n)) = (uclose (FImp (@fold_right_with_perm_args form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs n)) FTrue) (FEquiv (Atom p (@List.map (prod term term) term (@fst term term) (Varpairs n))) (Atom p (@List.map (prod term term) term (@snd term term) (Varpairs n)))))).
Axiom thm_Eqaxioms_DEF : forall L : prod ((prod N N) -> Prop) ((prod N N) -> Prop), (Eqaxioms L) = (@setU form (@INSERT form (FAll N0 (FEq (V N0) (V N0))) (@set0 form)) (@setU form (@INSERT form (FAll N0 (FAll ((BIT1 N0)) (FAll ((BIT0 (BIT1 N0))) (FImp (FEq (V N0) (V ((BIT1 N0)))) (FImp (FEq (V ((BIT0 (BIT1 N0)))) (V ((BIT1 N0)))) (FEq (V N0) (V ((BIT0 (BIT1 N0)))))))))) (@set0 form)) (@setU form (@GSPEC form (fun GEN_PVAR_508 : form => exists fa : prod N N, @SETSPEC form GEN_PVAR_508 (@IN (prod N N) fa (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) L)) (Eqaxiom_Func fa))) (@GSPEC form (fun GEN_PVAR_509 : form => exists pa : prod N N, @SETSPEC form GEN_PVAR_509 (@IN (prod N N) pa (@snd ((prod N N) -> Prop) ((prod N N) -> Prop) L)) (Eqaxiom_Pred pa)))))).
Axiom thm_DOWNFROM : forall (n : N), ((DOWNFROM N0) = (@nil N)) /\ ((DOWNFROM (N.succ n)) = (@cons N n (DOWNFROM n))).
Axiom thm_SATISFIES_UNION : forall {_201569 : Type'}, forall M : prod (_201569 -> Prop) (prod (N -> (list _201569) -> _201569) (N -> (list _201569) -> Prop)), forall s : form -> Prop, forall t : form -> Prop, (@satisfies _201569 M (@setU form s t)) = ((@satisfies _201569 M s) /\ (@satisfies _201569 M t)).
Axiom thm_HOLDS_UCLOSE_ALL : forall {_201594 A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall x : _201594, forall p : form, (forall v : N -> A, (@valuation A M v) -> @holds A M v p) -> forall v : N -> A, (@valuation A M v) -> @holds A M v (uclose p).
Axiom thm_HOLDS_UCLOSE_ALL_EQ : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) -> forall p : form, (forall v : N -> A, (@valuation A M v) -> @holds A M v (uclose p)) = (forall v : N -> A, (@valuation A M v) -> @holds A M v p).
Axiom thm_UCLOSE_FV_LEMMA : forall l : list N, forall p : form, (free_variables (@fold_right_with_perm_args N form FAll l p)) = (@setD N (free_variables p) (@set_of_list N l)).
Axiom thm_UCLOSE_CLOSED : forall p : form, (free_variables (uclose p)) = (@set0 N).
Axiom thm_HOLDS_UCLOSE_ANY : forall {A : Type'}, forall M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), forall v : N -> A, forall p : form, (@holds A M v (uclose p)) -> (~ ((@Dom A M) = (@set0 A))) -> forall w : N -> A, (@valuation A M w) -> @holds A M w p.
Axiom thm_SATISFIES_NOT : forall {A : Type'} (M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) (p : form) (E : form -> Prop), (~ ((@Dom A M) = (@set0 A))) -> ((@satisfies A M E) /\ (~ (@satisfies A M (@INSERT form p (@set0 form))))) = (@satisfies A M (@INSERT form (Not (uclose p)) E)).
Axiom thm_PREDICATES_FORM_UCLOSE : forall (p : form), (predicates_form (uclose p)) = (predicates_form p).
Axiom thm_HOLDS_ANDS : forall {_201869 : Type'} (M : prod (_201869 -> Prop) (prod (N -> (list _201869) -> _201869) (N -> (list _201869) -> Prop))) (v : N -> _201869), forall l : list form, (@holds _201869 M v (@fold_right_with_perm_args form form FAnd l FTrue)) = (@List.Forall form (@holds _201869 M v) l).
Axiom thm_LENGTH_VARPAIRS : forall n : N, (@lengthN (prod term term) (Varpairs n)) = n.
Axiom thm_MAP_FST_VARPAIRS : forall n : N, (@List.map (prod term term) term (@fst term term) (Varpairs n)) = (@List.map N term (fun n' : N => V (N.mul ((BIT0 (BIT1 N0))) n')) (DOWNFROM n)).
Axiom thm_MAP_SND_VARPAIRS : forall n : N, (@List.map (prod term term) term (@snd term term) (Varpairs n)) = (@List.map N term (fun n' : N => V (N.add (N.mul ((BIT0 (BIT1 N0))) n') ((BIT1 N0)))) (DOWNFROM n)).
Axiom thm_MULT_DIV_LEMMA : (forall n : N, (N.div (N.mul ((BIT0 (BIT1 N0))) n) ((BIT0 (BIT1 N0)))) = n) /\ (forall n : N, (N.div (N.add (N.mul ((BIT0 (BIT1 N0))) n) ((BIT1 N0))) ((BIT0 (BIT1 N0)))) = n).
Axiom thm_PAIR_LEMMA : forall {_201983 _201993 _201994 : Type'} (P : _201994 -> _201993 -> _201983), forall z : prod _201994 _201993, (@ε ((prod _201994 _201993) -> _201983) (fun f : (prod _201994 _201993) -> _201983 => forall x : _201994, forall y : _201993, @eq _201983 (f (@pair _201994 _201993 x y)) (P x y)) z) = (P (@fst _201994 _201993 z) (@snd _201994 _201993 z)).
Axiom thm_FORALL_VARPAIRS : forall (P : (prod term term) -> Prop), forall n : N, (@List.Forall (prod term term) P (Varpairs n)) = (@List.Forall N (fun n' : N => P (@pair term term (V (N.mul ((BIT0 (BIT1 N0))) n')) (V (N.add (N.mul ((BIT0 (BIT1 N0))) n') ((BIT1 N0)))))) (DOWNFROM n)).
Axiom thm_FORALL2_VARPAIRS : forall {_202112 : Type'} (a : N) (M : prod (_202112 -> Prop) (prod (N -> (list _202112) -> _202112) (N -> (list _202112) -> Prop))) (v : N -> _202112), forall n : N, (@List.Forall (prod term term) (fun p : prod term term => @Pred _202112 M a (@cons _202112 (@termval _202112 M v (@fst term term p)) (@cons _202112 (@termval _202112 M v (@snd term term p)) (@nil _202112)))) (Varpairs n)) = (@List.Forall2 _202112 _202112 (fun x : _202112 => fun y : _202112 => @Pred _202112 M a (@cons _202112 x (@cons _202112 y (@nil _202112)))) (@List.map term _202112 (@termval _202112 M v) (@List.map (prod term term) term (@fst term term) (Varpairs n))) (@List.map term _202112 (@termval _202112 M v) (@List.map (prod term term) term (@snd term term) (Varpairs n)))).
Axiom thm_FORALL2_FORALL : forall {_202151 _202152 _202154 : Type'} (P : _202152 -> _202151 -> Prop) (f : _202154 -> _202152) (g : _202154 -> _202151), forall l : list _202154, (@List.Forall2 _202152 _202151 (fun x : _202152 => fun y : _202151 => P x y) (@List.map _202154 _202152 f l) (@List.map _202154 _202151 g l)) = (@List.Forall _202154 (fun x : _202154 => P (f x) (g x)) l).
Axiom thm_FORALL_DOWNFROM : forall (P : N -> Prop), forall n : N, (@List.Forall N P (DOWNFROM n)) = (forall k : N, (N.lt k n) -> P k).
Axiom thm_MAP_INDEXED : forall {A : Type'}, forall l : list A, (@List.map N A (fun n : N => @Nth A (N.sub (N.sub (@lengthN A l) ((BIT1 N0))) n) l) (DOWNFROM (@lengthN A l))) = l.
Axiom thm_RECONSTRUCT_TERMVAL : forall {_202475 _202501 : Type'} (l : list _202475), forall M : prod (_202501 -> Prop) (prod (N -> (list _202501) -> _202501) (N -> (list _202501) -> Prop)), forall a : _202501, forall f1 : _202475 -> _202501, forall f2 : _202475 -> _202501, ((@List.map term _202501 (@termval _202501 M (fun n : N => @COND _202501 (N.le (N.mul ((BIT0 (BIT1 N0))) (@lengthN _202475 l)) n) a (@COND _202501 (N.Even n) (f1 (@Nth _202475 (N.sub (N.sub (@lengthN _202475 l) ((BIT1 N0))) (N.div n ((BIT0 (BIT1 N0))))) l)) (f2 (@Nth _202475 (N.sub (N.sub (@lengthN _202475 l) ((BIT1 N0))) (N.div n ((BIT0 (BIT1 N0))))) l))))) (@List.map (prod term term) term (@fst term term) (Varpairs (@lengthN _202475 l)))) = (@List.map _202475 _202501 f1 l)) /\ ((@List.map term _202501 (@termval _202501 M (fun n : N => @COND _202501 (N.le (N.mul ((BIT0 (BIT1 N0))) (@lengthN _202475 l)) n) a (@COND _202501 (N.Even n) (f1 (@Nth _202475 (N.sub (N.sub (@lengthN _202475 l) ((BIT1 N0))) (N.div n ((BIT0 (BIT1 N0))))) l)) (f2 (@Nth _202475 (N.sub (N.sub (@lengthN _202475 l) ((BIT1 N0))) (N.div n ((BIT0 (BIT1 N0))))) l))))) (@List.map (prod term term) term (@snd term term) (Varpairs (@lengthN _202475 l)))) = (@List.map _202475 _202501 f2 l)).
Axiom thm_FORALL_TERMS_STRONG : forall s : form -> Prop, forall t : term, (terms (functions s) t) = (@subset (prod N N) (functions_term t) (functions s)).
Axiom thm_FORALL_TERMS_RAW : forall s : form -> Prop, forall t : term, (terms (functions s) t) -> @subset (prod N N) (functions_term t) (functions s).
Axiom thm_FORALL_TERMS_INDEXED : forall (s : form -> Prop), forall l : list term, forall n : N, ((@List.Forall term (terms (functions s)) l) /\ (N.lt n (@lengthN term l))) -> @subset (prod N N) (functions_term (@Nth term n l)) (functions s).
Axiom thm_NORMAL_THM : forall {A : Type'} (s : form -> Prop), (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ ((@normal A (functions s) M) /\ (@satisfies A M s)))) = (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M (@setU form s (Eqaxioms (language s)))))).
Axiom thm_FUNCTIONS_SUBSET : forall s : form -> Prop, forall t : form -> Prop, (@subset form t s) -> @subset (prod N N) (functions t) (functions s).
Axiom thm_INTERPRETATION_MODIFY_LANGUAGE : forall {A : Type'}, forall s : form -> Prop, forall s' : form -> Prop, forall t : form -> Prop, ((@subset form t s) /\ (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M t)))) -> exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s') M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M t)).
Axiom thm_INTERPRETATION_RESTRICT_LANGUAGE : forall {A : Type'}, forall s : form -> Prop, forall s' : form -> Prop, forall t : form -> Prop, ((@subset form s' s) /\ (exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M t)))) -> exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s') M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M t)).
Axiom thm_FUNCTIONS_INSERT : forall (p : form) (s : form -> Prop), (functions (@INSERT form p s)) = (@setU (prod N N) (functions_form p) (functions s)).
Axiom thm_FUNCTIONS_UNION : forall (s : form -> Prop) (t : form -> Prop), (functions (@setU form s t)) = (@setU (prod N N) (functions s) (functions t)).
Axiom thm_PREDICATES_UNION : forall (s : form -> Prop) (t : form -> Prop), (predicates (@setU form s t)) = (@setU (prod N N) (predicates s) (predicates t)).
Axiom thm_FUNCTIONS_FORM_UCLOSE : forall (p : form), (functions_form (uclose p)) = (functions_form p).
Axiom thm_FUNCTIONS_TERM_FNV1 : forall (p : N) (n : N), (functions_term (Fn p (@List.map (prod term term) term (@fst term term) (Varpairs n)))) = (@INSERT (prod N N) (@pair N N p n) (@set0 (prod N N))).
Axiom thm_FUNCTIONS_FORM_FNV1 : forall n : N, (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) functions_term (@List.map (prod term term) term (@fst term term) (Varpairs n)))) = (@set0 (prod N N)).
Axiom thm_FUNCTIONS_FORM_FNV2 : forall n : N, (@list_Union (prod N N) (@List.map term ((prod N N) -> Prop) functions_term (@List.map (prod term term) term (@snd term term) (Varpairs n)))) = (@set0 (prod N N)).
Axiom thm_FUNCTIONS_TERM_FNV2 : forall (p : N) (n : N), (functions_term (Fn p (@List.map (prod term term) term (@snd term term) (Varpairs n)))) = (@INSERT (prod N N) (@pair N N p n) (@set0 (prod N N))).
Axiom thm_FUNCTIONS_EQCONJ : forall n : N, (functions_form (@fold_right_with_perm_args form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (Atom N0 (@cons term s (@cons term t (@nil term)))))) (Varpairs n)) FTrue)) = (@set0 (prod N N)).
Axiom thm_FUNCTIONS_EQAXIOM_FUNC : forall fa : prod N N, (functions_form (Eqaxiom_Func fa)) = (@INSERT (prod N N) fa (@set0 (prod N N))).
Axiom thm_FUNCTIONS_EQAXIOM_PRED : forall pa : prod N N, (functions_form (Eqaxiom_Pred pa)) = (@set0 (prod N N)).
Axiom thm_FUNCTIONS_EQAXIOM : forall (s : form -> Prop), (functions (Eqaxioms (language s))) = (functions s).
Axiom thm_INTERPRETATION_EQAXIOMS : forall {_204578 : Type'} (s : form -> Prop) (M : prod (_204578 -> Prop) (prod (N -> (list _204578) -> _204578) (N -> (list _204578) -> Prop))), (@interpretation _204578 (language s) M) = (@interpretation _204578 (language (@setU form s (Eqaxioms (language s)))) M).
Axiom thm_TERMS_SUBSET : forall f1 : (prod N N) -> Prop, forall f2 : (prod N N) -> Prop, (@subset (prod N N) f1 f2) -> @subset term (terms f1) (terms f2).
Axiom thm_EQAXIOMS_UNION : forall (s : form -> Prop) (t : form -> Prop), (Eqaxioms (language (@setU form s t))) = (@setU form (Eqaxioms (language s)) (Eqaxioms (language t))).
Axiom thm_EQAXIOMS_SUBSET : forall (s : form -> Prop) (t : form -> Prop), (@subset form s t) -> @subset form (Eqaxioms (language s)) (Eqaxioms (language t)).
Axiom thm_IN_EQAXIOMS : forall (s : form -> Prop) (p : form), (@IN form p (Eqaxioms (language s))) -> (s = (@set0 form)) \/ (exists q : form, (@IN form q s) /\ (@IN form p (Eqaxioms (language (@INSERT form q (@set0 form)))))).
Axiom thm_COMPACT_LS_NORM_LEMMA1 : forall {A : Type'} (s : form -> Prop), (forall t : form -> Prop, ((@finite_set form t) /\ (@subset form t s)) -> exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ ((@normal A (functions s) M) /\ (@satisfies A M t)))) -> forall t : form -> Prop, ((@finite_set form t) /\ (@subset form t s)) -> exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language t) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ ((@normal A (functions t) M) /\ (@satisfies A M t))).
Axiom thm_COMPACT_LS_NORM_LEMMA2a : forall (s : form -> Prop) (t : form -> Prop), ((@finite_set form t) /\ (@subset form t (Eqaxioms (language s)))) -> exists s0 : form -> Prop, (@finite_set form s0) /\ ((@subset form s0 s) /\ (@subset form t (Eqaxioms (language s0)))).
Axiom thm_COMPACT_LS_NORM_LEMMA2 : forall (s : form -> Prop), forall t : form -> Prop, ((@finite_set form t) /\ (@subset form t (@setU form s (Eqaxioms (language s))))) -> exists u : form -> Prop, (@subset form t (@setU form u (Eqaxioms (language u)))) /\ ((@finite_set form u) /\ (@subset form u s)).
Axiom thm_COMPACT_LS_NORM : forall {A : Type'} (s : form -> Prop), (forall t : form -> Prop, ((@finite_set form t) /\ (@subset form t s)) -> exists M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)), (@interpretation A (language s) M) /\ ((~ ((@Dom A M) = (@set0 A))) /\ ((@normal A (functions s) M) /\ (@satisfies A M t)))) -> exists C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (@interpretation term (language s) C) /\ ((~ ((@Dom term C) = (@set0 term))) /\ ((@normal term (functions s) C) /\ (@satisfies term C s))).
