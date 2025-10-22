Require Import Stdlib.NArith.BinNat Stdlib.Reals.Reals mathcomp.classical.classical_sets mathcomp.classical.cardinality mathcomp.ssreflect.choice mathcomp.ssreflect.ssrbool MathComp_HOLLight_Real_With_N.mappings HOLLight_Unif.mappings.
Definition o {A B C : Type'} : (B -> C) -> (A -> B) -> A -> C := fun f : B -> C => fun g : A -> B => fun x : A => f (g x).
Lemma o_def {A B C : Type'} : (@o A B C) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Proof. exact (REFL (@o A B C)). Qed.
Definition I {A : Type'} : A -> A := fun x : A => x.
Lemma I_def {A : Type'} : (@I A) = (fun x : A => x).
Proof. exact (REFL (@I A)). Qed.
Definition _SEQPATTERN {A B : Type'} : (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop := fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x).
Lemma _SEQPATTERN_def {A B : Type'} : (@_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Proof. exact (REFL (@_SEQPATTERN A B)). Qed.
Definition _GUARDED_PATTERN : Prop -> Prop -> Prop -> Prop := fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r).
Lemma _GUARDED_PATTERN_def : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Proof. exact (REFL _GUARDED_PATTERN). Qed.
Definition _MATCH {A B : Type'} : A -> (A -> B -> Prop) -> B := fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False)).
Lemma _MATCH_def {A B : Type'} : (@_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_MATCH A B)). Qed.
Definition _FUNCTION {A B : Type'} : (A -> B -> Prop) -> A -> B := fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False)).
Lemma _FUNCTION_def {A B : Type'} : (@_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_FUNCTION A B)). Qed.
Definition CURRY {A B C : Type'} : ((prod A B) -> C) -> A -> B -> C := fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285).
Lemma CURRY_def {A B C : Type'} : (@CURRY A B C) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285)).
Proof. exact (REFL (@CURRY A B C)). Qed.
Definition UNCURRY {A B C : Type'} : (A -> B -> C) -> (prod A B) -> C := fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305).
Lemma UNCURRY_def {A B C : Type'} : (@UNCURRY A B C) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305)).
Proof. exact (REFL (@UNCURRY A B C)). Qed.
Definition PASSOC {A B C D : Type'} : ((prod (prod A B) C) -> D) -> (prod A (prod B C)) -> D := fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322))).
Lemma PASSOC_def {A B C D : Type'} : (@PASSOC A B C D) = (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322)))).
Proof. exact (REFL (@PASSOC A B C D)). Qed.
Definition minimal : (N -> Prop) -> N := fun _6536 : N -> Prop => @ε N (fun n : N => (_6536 n) /\ (forall m : N, (N.lt m n) -> ~ (_6536 m))).
Lemma minimal_def : minimal = (fun _6536 : N -> Prop => @ε N (fun n : N => (_6536 n) /\ (forall m : N, (N.lt m n) -> ~ (_6536 m)))).
Proof. exact (REFL minimal). Qed.
Definition FNIL {A : Type'} : N -> A := fun _17624 : N => @ε A (fun x : A => True).
Lemma FNIL_def {A : Type'} : (@FNIL A) = (fun _17624 : N => @ε A (fun x : A => True)).
Proof. exact (REFL (@FNIL A)). Qed.
Definition OUTL {A B : Type'} : (Datatypes.sum A B) -> A := @ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A => forall _17649 : prod N (prod N (prod N N)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))).
Lemma OUTL_def {A B : Type'} : (@OUTL A B) = (@ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A => forall _17649 : prod N (prod N (prod N N)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))).
Proof. exact (REFL (@OUTL A B)). Qed.
Definition OUTR {A B : Type'} : (Datatypes.sum A B) -> B := @ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B => forall _17651 : prod N (prod N (prod N N)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).
Lemma OUTR_def {A B : Type'} : (@OUTR A B) = (@ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B => forall _17651 : prod N (prod N (prod N N)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))).
Proof. exact (REFL (@OUTR A B)). Qed.
Definition _22857 : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) N0 (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7).
Lemma _22857_def : _22857 = (fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) N0 (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (REFL _22857). Qed.
Definition ASCII : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := _22857.
Lemma ASCII_def : ASCII = _22857.
Proof. exact (REFL ASCII). Qed.
Definition sqrt : R -> R := fun _27149 : R => @ε R (fun y : R => ((Rsgn y) = (Rsgn _27149)) /\ ((Rpow y ((BIT0 (BIT1 N0)))) = (Rabs _27149))).
Lemma sqrt_def : sqrt = (fun _27149 : R => @ε R (fun y : R => ((Rsgn y) = (Rsgn _27149)) /\ ((Rpow y ((BIT0 (BIT1 N0)))) = (Rabs _27149)))).
Proof. exact (REFL sqrt). Qed.
Definition DECIMAL : N -> N -> R := fun _27828 : N => fun _27829 : N => Rdiv (R_of_N _27828) (R_of_N _27829).
Lemma DECIMAL_def : DECIMAL = (fun _27828 : N => fun _27829 : N => Rdiv (R_of_N _27828) (R_of_N _27829)).
Proof. exact (REFL DECIMAL). Qed.
Definition eq2 {A : Type'} : A -> A -> (A -> A -> Prop) -> Prop := fun _29602 : A => fun _29603 : A => fun _29604 : A -> A -> Prop => _29604 _29602 _29603.
Lemma eq2_def {A : Type'} : (@eq2 A) = (fun _29602 : A => fun _29603 : A => fun _29604 : A -> A -> Prop => _29604 _29602 _29603).
Proof. exact (REFL (@eq2 A)). Qed.
Definition int_mod : Z -> Z -> Z -> Prop := fun _29664 : Z => fun _29665 : Z => fun _29666 : Z => Z.divide _29664 (Z.sub _29665 _29666).
Lemma int_mod_def : int_mod = (fun _29664 : Z => fun _29665 : Z => fun _29666 : Z => Z.divide _29664 (Z.sub _29665 _29666)).
Proof. exact (REFL int_mod). Qed.
Definition num_of_int : Z -> N := fun _31234 : Z => @ε N (fun n : N => (Z_of_N n) = _31234).
Lemma num_of_int_def : num_of_int = (fun _31234 : Z => @ε N (fun n : N => (Z_of_N n) = _31234)).
Proof. exact (REFL num_of_int). Qed.
Definition num_divides : N -> N -> Prop := fun _31266 : N => fun _31267 : N => Z.divide (Z_of_N _31266) (Z_of_N _31267).
Lemma num_divides_def : num_divides = (fun _31266 : N => fun _31267 : N => Z.divide (Z_of_N _31266) (Z_of_N _31267)).
Proof. exact (REFL num_divides). Qed.
Definition num_mod : N -> N -> N -> Prop := fun _31278 : N => fun _31279 : N => fun _31280 : N => int_mod (Z_of_N _31278) (Z_of_N _31279) (Z_of_N _31280).
Lemma num_mod_def : num_mod = (fun _31278 : N => fun _31279 : N => fun _31280 : N => int_mod (Z_of_N _31278) (Z_of_N _31279) (Z_of_N _31280)).
Proof. exact (REFL num_mod). Qed.
Definition num_coprime : (prod N N) -> Prop := fun _31299 : prod N N => int_coprime (@pair Z Z (Z_of_N (@fst N N _31299)) (Z_of_N (@snd N N _31299))).
Lemma num_coprime_def : num_coprime = (fun _31299 : prod N N => int_coprime (@pair Z Z (Z_of_N (@fst N N _31299)) (Z_of_N (@snd N N _31299)))).
Proof. exact (REFL num_coprime). Qed.
Definition num_gcd : (prod N N) -> N := fun _31308 : prod N N => num_of_int (int_gcd (@pair Z Z (Z_of_N (@fst N N _31308)) (Z_of_N (@snd N N _31308)))).
Lemma num_gcd_def : num_gcd = (fun _31308 : prod N N => num_of_int (int_gcd (@pair Z Z (Z_of_N (@fst N N _31308)) (Z_of_N (@snd N N _31308))))).
Proof. exact (REFL num_gcd). Qed.
Definition num_lcm : (prod N N) -> N := fun _31317 : prod N N => num_of_int (int_lcm (@pair Z Z (Z_of_N (@fst N N _31317)) (Z_of_N (@snd N N _31317)))).
Lemma num_lcm_def : num_lcm = (fun _31317 : prod N N => num_of_int (int_lcm (@pair Z Z (Z_of_N (@fst N N _31317)) (Z_of_N (@snd N N _31317))))).
Proof. exact (REFL num_lcm). Qed.
Definition prime : N -> Prop := fun _32093 : N => (~ (_32093 = ((BIT1 N0)))) /\ (forall x : N, (num_divides x _32093) -> (x = ((BIT1 N0))) \/ (x = _32093)).
Lemma prime_def : prime = (fun _32093 : N => (~ (_32093 = ((BIT1 N0)))) /\ (forall x : N, (num_divides x _32093) -> (x = ((BIT1 N0))) \/ (x = _32093))).
Proof. exact (REFL prime). Qed.
Definition real_zpow : R -> Z -> R := fun _32251 : R => fun _32252 : Z => @COND R (Z.le (Z_of_N N0) _32252) (Rpow _32251 (num_of_int _32252)) (Rinv (Rpow _32251 (num_of_int (Z.opp _32252)))).
Lemma real_zpow_def : real_zpow = (fun _32251 : R => fun _32252 : Z => @COND R (Z.le (Z_of_N N0) _32252) (Rpow _32251 (num_of_int _32252)) (Rinv (Rpow _32251 (num_of_int (Z.opp _32252))))).
Proof. exact (REFL real_zpow). Qed.
Definition INFINITE {A : Type'} : (A -> Prop) -> Prop := fun _32479 : A -> Prop => ~ (@finite_set A _32479).
Lemma INFINITE_def {A : Type'} : (@INFINITE A) = (fun _32479 : A -> Prop => ~ (@finite_set A _32479)).
Proof. exact (REFL (@INFINITE A)). Qed.
Definition INJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32496 : A -> B => fun _32497 : A -> Prop => fun _32498 : B -> Prop => (forall x : A, (@IN A x _32497) -> @IN B (_32496 x) _32498) /\ (forall x : A, forall y : A, ((@IN A x _32497) /\ ((@IN A y _32497) /\ ((_32496 x) = (_32496 y)))) -> x = y).
Lemma INJ_def {A B : Type'} : (@INJ A B) = (fun _32496 : A -> B => fun _32497 : A -> Prop => fun _32498 : B -> Prop => (forall x : A, (@IN A x _32497) -> @IN B (_32496 x) _32498) /\ (forall x : A, forall y : A, ((@IN A x _32497) /\ ((@IN A y _32497) /\ ((_32496 x) = (_32496 y)))) -> x = y)).
Proof. exact (REFL (@INJ A B)). Qed.
Definition SURJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32517 : A -> B => fun _32518 : A -> Prop => fun _32519 : B -> Prop => (forall x : A, (@IN A x _32518) -> @IN B (_32517 x) _32519) /\ (forall x : B, (@IN B x _32519) -> exists y : A, (@IN A y _32518) /\ ((_32517 y) = x)).
Lemma SURJ_def {A B : Type'} : (@SURJ A B) = (fun _32517 : A -> B => fun _32518 : A -> Prop => fun _32519 : B -> Prop => (forall x : A, (@IN A x _32518) -> @IN B (_32517 x) _32519) /\ (forall x : B, (@IN B x _32519) -> exists y : A, (@IN A y _32518) /\ ((_32517 y) = x))).
Proof. exact (REFL (@SURJ A B)). Qed.
Definition BIJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32538 : A -> B => fun _32539 : A -> Prop => fun _32540 : B -> Prop => (@INJ A B _32538 _32539 _32540) /\ (@SURJ A B _32538 _32539 _32540).
Lemma BIJ_def {A B : Type'} : (@BIJ A B) = (fun _32538 : A -> B => fun _32539 : A -> Prop => fun _32540 : B -> Prop => (@INJ A B _32538 _32539 _32540) /\ (@SURJ A B _32538 _32539 _32540)).
Proof. exact (REFL (@BIJ A B)). Qed.
Definition CHOICE {A : Type'} : (A -> Prop) -> A := fun _32559 : A -> Prop => @ε A (fun x : A => @IN A x _32559).
Lemma CHOICE_def {A : Type'} : (@CHOICE A) = (fun _32559 : A -> Prop => @ε A (fun x : A => @IN A x _32559)).
Proof. exact (REFL (@CHOICE A)). Qed.
Definition REST {A : Type'} : (A -> Prop) -> A -> Prop := fun _32564 : A -> Prop => @DELETE A _32564 (@CHOICE A _32564).
Lemma REST_def {A : Type'} : (@REST A) = (fun _32564 : A -> Prop => @DELETE A _32564 (@CHOICE A _32564)).
Proof. exact (REFL (@REST A)). Qed.
Definition FINREC {A B : Type'} : (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop) (fun FINREC' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop => forall _42166 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42166 f b s a N0) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : N, forall a : B, forall f : A -> B -> B, (FINREC' _42166 f b s a (N.succ n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42166 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))).
Lemma FINREC_def {A B : Type'} : (@FINREC A B) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop) (fun FINREC' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop => forall _42166 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42166 f b s a N0) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : N, forall a : B, forall f : A -> B -> B, (FINREC' _42166 f b s a (N.succ n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42166 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (REFL (@FINREC A B)). Qed.
Definition HAS_SIZE {A : Type'} : (A -> Prop) -> N -> Prop := fun _43394 : A -> Prop => fun _43395 : N => (@finite_set A _43394) /\ ((@card A _43394) = _43395).
Lemma HAS_SIZE_def {A : Type'} : (@HAS_SIZE A) = (fun _43394 : A -> Prop => fun _43395 : N => (@finite_set A _43394) /\ ((@card A _43394) = _43395)).
Proof. exact (REFL (@HAS_SIZE A)). Qed.
Definition CROSS {A B : Type'} : (A -> Prop) -> (B -> Prop) -> (prod A B) -> Prop := fun _47313 : A -> Prop => fun _47314 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47313) /\ (@IN B y _47314)) (@pair A B x y)).
Lemma CROSS_def {A B : Type'} : (@CROSS A B) = (fun _47313 : A -> Prop => fun _47314 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47313) /\ (@IN B y _47314)) (@pair A B x y))).
Proof. exact (REFL (@CROSS A B)). Qed.
Definition ARB {A : Type'} : A := @ε A (fun x : A => False).
Lemma ARB_def {A : Type'} : (@ARB A) = (@ε A (fun x : A => False)).
Proof. exact (REFL (@ARB A)). Qed.
Definition EXTENSIONAL {A B : Type'} : (A -> Prop) -> (A -> B) -> Prop := fun _48087 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48087)) -> (f x) = (@ARB B)) f).
Lemma EXTENSIONAL_def {A B : Type'} : (@EXTENSIONAL A B) = (fun _48087 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48087)) -> (f x) = (@ARB B)) f)).
Proof. exact (REFL (@EXTENSIONAL A B)). Qed.
Definition RESTRICTION {A B : Type'} : (A -> Prop) -> (A -> B) -> A -> B := fun _48139 : A -> Prop => fun _48140 : A -> B => fun _48141 : A => @COND B (@IN A _48141 _48139) (_48140 _48141) (@ARB B).
Lemma RESTRICTION_def {A B : Type'} : (@RESTRICTION A B) = (fun _48139 : A -> Prop => fun _48140 : A -> B => fun _48141 : A => @COND B (@IN A _48141 _48139) (_48140 _48141) (@ARB B)).
Proof. exact (REFL (@RESTRICTION A B)). Qed.
Definition cartesian_product {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (K -> A) -> Prop := fun _48334 : K -> Prop => fun _48335 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48334 f) /\ (forall i : K, (@IN K i _48334) -> @IN A (f i) (_48335 i))) f).
Lemma cartesian_product_def {A K : Type'} : (@cartesian_product A K) = (fun _48334 : K -> Prop => fun _48335 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48334 f) /\ (forall i : K, (@IN K i _48334) -> @IN A (f i) (_48335 i))) f)).
Proof. exact (REFL (@cartesian_product A K)). Qed.
Definition product_map {A B K : Type'} : (K -> Prop) -> (K -> A -> B) -> (K -> A) -> K -> B := fun _49383 : K -> Prop => fun _49384 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49383 (fun i : K => _49384 i (x i)).
Lemma product_map_def {A B K : Type'} : (@product_map A B K) = (fun _49383 : K -> Prop => fun _49384 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49383 (fun i : K => _49384 i (x i))).
Proof. exact (REFL (@product_map A B K)). Qed.
Definition disjoint_union {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop := fun _49519 : K -> Prop => fun _49520 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49519) /\ (@IN A x (_49520 i))) (@pair K A i x)).
Lemma disjoint_union_def {A K : Type'} : (@disjoint_union A K) = (fun _49519 : K -> Prop => fun _49520 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49519) /\ (@IN A x (_49520 i))) (@pair K A i x))).
Proof. exact (REFL (@disjoint_union A K)). Qed.
Definition pairwise {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _56607 : A -> A -> Prop => fun _56608 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56608) /\ ((@IN A y _56608) /\ (~ (x = y)))) -> _56607 x y.
Lemma pairwise_def {A : Type'} : (@pairwise A) = (fun _56607 : A -> A -> Prop => fun _56608 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56608) /\ ((@IN A y _56608) /\ (~ (x = y)))) -> _56607 x y).
Proof. exact (REFL (@pairwise A)). Qed.
Definition UNION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57320 : ((A -> Prop) -> Prop) -> Prop => fun _57321 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57320 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57321 c) /\ ((@UNIONS A u) = s)).
Lemma UNION_OF_def {A : Type'} : (@UNION_OF A) = (fun _57320 : ((A -> Prop) -> Prop) -> Prop => fun _57321 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57320 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57321 c) /\ ((@UNIONS A u) = s))).
Proof. exact (REFL (@UNION_OF A)). Qed.
Definition INTERSECTION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57332 : ((A -> Prop) -> Prop) -> Prop => fun _57333 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57332 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57333 c) /\ ((@INTERS A u) = s)).
Lemma INTERSECTION_OF_def {A : Type'} : (@INTERSECTION_OF A) = (fun _57332 : ((A -> Prop) -> Prop) -> Prop => fun _57333 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57332 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57333 c) /\ ((@INTERS A u) = s))).
Proof. exact (REFL (@INTERSECTION_OF A)). Qed.
Definition ARBITRARY {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _57468 : (A -> Prop) -> Prop => True.
Lemma ARBITRARY_def {A : Type'} : (@ARBITRARY A) = (fun _57468 : (A -> Prop) -> Prop => True).
Proof. exact (REFL (@ARBITRARY A)). Qed.
Definition le_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64062 : A -> Prop => fun _64063 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64062) -> @IN B (f x) _64063) /\ (forall x : A, forall y : A, ((@IN A x _64062) /\ ((@IN A y _64062) /\ ((f x) = (f y)))) -> x = y).
Lemma le_c_def {A B : Type'} : (@le_c A B) = (fun _64062 : A -> Prop => fun _64063 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64062) -> @IN B (f x) _64063) /\ (forall x : A, forall y : A, ((@IN A x _64062) /\ ((@IN A y _64062) /\ ((f x) = (f y)))) -> x = y)).
Proof. exact (REFL (@le_c A B)). Qed.
Definition lt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64074 : A -> Prop => fun _64075 : B -> Prop => (@le_c A B _64074 _64075) /\ (~ (@le_c B A _64075 _64074)).
Lemma lt_c_def {A B : Type'} : (@lt_c A B) = (fun _64074 : A -> Prop => fun _64075 : B -> Prop => (@le_c A B _64074 _64075) /\ (~ (@le_c B A _64075 _64074))).
Proof. exact (REFL (@lt_c A B)). Qed.
Definition eq_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64086 : A -> Prop => fun _64087 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64086) -> @IN B (f x) _64087) /\ (forall y : B, (@IN B y _64087) -> @ex1 A (fun x : A => (@IN A x _64086) /\ ((f x) = y))).
Lemma eq_c_def {A B : Type'} : (@eq_c A B) = (fun _64086 : A -> Prop => fun _64087 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64086) -> @IN B (f x) _64087) /\ (forall y : B, (@IN B y _64087) -> @ex1 A (fun x : A => (@IN A x _64086) /\ ((f x) = y)))).
Proof. exact (REFL (@eq_c A B)). Qed.
Definition ge_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64098 : A -> Prop => fun _64099 : B -> Prop => @le_c B A _64099 _64098.
Lemma ge_c_def {A B : Type'} : (@ge_c A B) = (fun _64098 : A -> Prop => fun _64099 : B -> Prop => @le_c B A _64099 _64098).
Proof. exact (REFL (@ge_c A B)). Qed.
Definition gt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64110 : A -> Prop => fun _64111 : B -> Prop => @lt_c B A _64111 _64110.
Lemma gt_c_def {A B : Type'} : (@gt_c A B) = (fun _64110 : A -> Prop => fun _64111 : B -> Prop => @lt_c B A _64111 _64110).
Proof. exact (REFL (@gt_c A B)). Qed.
Definition COUNTABLE {A : Type'} : (A -> Prop) -> Prop := fun _64261 : A -> Prop => @ge_c N A (@setT N) _64261.
Lemma COUNTABLE_def {A : Type'} : (@COUNTABLE A) = (fun _64261 : A -> Prop => @ge_c N A (@setT N) _64261).
Proof. exact (REFL (@COUNTABLE A)). Qed.
Definition sup : (R -> Prop) -> R := fun _64266 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64266) -> Rle x a) /\ (forall b : R, (forall x : R, (@IN R x _64266) -> Rle x b) -> Rle a b)).
Lemma sup_def : sup = (fun _64266 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64266) -> Rle x a) /\ (forall b : R, (forall x : R, (@IN R x _64266) -> Rle x b) -> Rle a b))).
Proof. exact (REFL sup). Qed.
Definition inf : (R -> Prop) -> R := fun _65125 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65125) -> Rle a x) /\ (forall b : R, (forall x : R, (@IN R x _65125) -> Rle b x) -> Rle b a)).
Lemma inf_def : inf = (fun _65125 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65125) -> Rle a x) /\ (forall b : R, (forall x : R, (@IN R x _65125) -> Rle b x) -> Rle b a))).
Proof. exact (REFL inf). Qed.
Definition has_inf : (R -> Prop) -> R -> Prop := fun _66475 : R -> Prop => fun _66476 : R => forall c : R, (forall x : R, (@IN R x _66475) -> Rle c x) = (Rle c _66476).
Lemma has_inf_def : has_inf = (fun _66475 : R -> Prop => fun _66476 : R => forall c : R, (forall x : R, (@IN R x _66475) -> Rle c x) = (Rle c _66476)).
Proof. exact (REFL has_inf). Qed.
Definition has_sup : (R -> Prop) -> R -> Prop := fun _66487 : R -> Prop => fun _66488 : R => forall c : R, (forall x : R, (@IN R x _66487) -> Rle x c) = (Rle _66488 c).
Lemma has_sup_def : has_sup = (fun _66487 : R -> Prop => fun _66488 : R => forall c : R, (forall x : R, (@IN R x _66487) -> Rle x c) = (Rle _66488 c)).
Proof. exact (REFL has_sup). Qed.
Definition neutral {A : Type'} : (A -> A -> A) -> A := fun _68825 : A -> A -> A => @ε A (fun x : A => forall y : A, ((_68825 x y) = y) /\ ((_68825 y x) = y)).
Lemma neutral_def {A : Type'} : (@neutral A) = (fun _68825 : A -> A -> A => @ε A (fun x : A => forall y : A, ((_68825 x y) = y) /\ ((_68825 y x) = y))).
Proof. exact (REFL (@neutral A)). Qed.
Definition monoidal {A : Type'} : (A -> A -> A) -> Prop := fun _68830 : A -> A -> A => (forall x : A, forall y : A, (_68830 x y) = (_68830 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68830 x (_68830 y z)) = (_68830 (_68830 x y) z)) /\ (forall x : A, (_68830 (@neutral A _68830) x) = x)).
Lemma monoidal_def {A : Type'} : (@monoidal A) = (fun _68830 : A -> A -> A => (forall x : A, forall y : A, (_68830 x y) = (_68830 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68830 x (_68830 y z)) = (_68830 (_68830 x y) z)) /\ (forall x : A, (_68830 (@neutral A _68830) x) = x))).
Proof. exact (REFL (@monoidal A)). Qed.
Definition support {A B : Type'} : (B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop := fun _68915 : B -> B -> B => fun _68916 : A -> B => fun _68917 : A -> Prop => @GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x _68917) /\ (~ ((_68916 x) = (@neutral B _68915)))) x).
Lemma support_def {A B : Type'} : (@support A B) = (fun _68915 : B -> B -> B => fun _68916 : A -> B => fun _68917 : A -> Prop => @GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x _68917) /\ (~ ((_68916 x) = (@neutral B _68915)))) x)).
Proof. exact (REFL (@support A B)). Qed.
Definition iterate {A B : Type'} : (B -> B -> B) -> (A -> Prop) -> (A -> B) -> B := fun _68936 : B -> B -> B => fun _68937 : A -> Prop => fun _68938 : A -> B => @COND B (@finite_set A (@support A B _68936 _68938 _68937)) (@fold_set A B (fun x : A => fun a : B => _68936 (_68938 x) a) (@support A B _68936 _68938 _68937) (@neutral B _68936)) (@neutral B _68936).
Lemma iterate_def {A B : Type'} : (@iterate A B) = (fun _68936 : B -> B -> B => fun _68937 : A -> Prop => fun _68938 : A -> B => @COND B (@finite_set A (@support A B _68936 _68938 _68937)) (@fold_set A B (fun x : A => fun a : B => _68936 (_68938 x) a) (@support A B _68936 _68938 _68937) (@neutral B _68936)) (@neutral B _68936)).
Proof. exact (REFL (@iterate A B)). Qed.
Definition iterato {A K : Type'} : (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A := @ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76692 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76692 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76692 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))).
Lemma iterato_def {A K : Type'} : (@iterato A K) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76692 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76692 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76692 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))).
Proof. exact (REFL (@iterato A K)). Qed.
Definition nproduct {A : Type'} : (A -> Prop) -> (A -> N) -> N := @iterate A N N.mul.
Lemma nproduct_def {A : Type'} : (@nproduct A) = (@iterate A N N.mul).
Proof. exact (REFL (@nproduct A)). Qed.
Definition iproduct {A : Type'} : (A -> Prop) -> (A -> Z) -> Z := @iterate A Z Z.mul.
Lemma iproduct_def {A : Type'} : (@iproduct A) = (@iterate A Z Z.mul).
Proof. exact (REFL (@iproduct A)). Qed.
Definition product {A : Type'} : (A -> Prop) -> (A -> R) -> R := @iterate A R Rmult.
Lemma product_def {A : Type'} : (@product A) = (@iterate A R Rmult).
Proof. exact (REFL (@product A)). Qed.
Definition isum {A : Type'} : (A -> Prop) -> (A -> Z) -> Z := @iterate A Z Z.add.
Lemma isum_def {A : Type'} : (@isum A) = (@iterate A Z Z.add).
Proof. exact (REFL (@isum A)). Qed.
Definition nsum {A : Type'} : (A -> Prop) -> (A -> N) -> N := @iterate A N N.add.
Lemma nsum_def {A : Type'} : (@nsum A) = (@iterate A N N.add).
Proof. exact (REFL (@nsum A)). Qed.
Definition sum {A : Type'} : (A -> Prop) -> (A -> R) -> R := @iterate A R Rplus.
Lemma sum_def {A : Type'} : (@sum A) = (@iterate A R Rplus).
Proof. exact (REFL (@sum A)). Qed.
Definition polynomial_function : (R -> R) -> Prop := fun _94105 : R -> R => exists m : N, exists c : N -> R, forall x : R, (_94105 x) = (@sum N (Ninterval N0 m) (fun i : N => Rmult (c i) (Rpow x i))).
Lemma polynomial_function_def : polynomial_function = (fun _94105 : R -> R => exists m : N, exists c : N -> R, forall x : R, (_94105 x) = (@sum N (Ninterval N0 m) (fun i : N => Rmult (c i) (Rpow x i)))).
Proof. exact (REFL polynomial_function). Qed.
Definition dollar {A N' : Type'} : (cart A N') -> N -> A := fun _94557 : cart A N' => fun _94558 : N => @dest_cart A N' _94557 (@finite_index N' _94558).
Lemma dollar_def {A N' : Type'} : (@dollar A N') = (fun _94557 : cart A N' => fun _94558 : N => @dest_cart A N' _94557 (@finite_index N' _94558)).
Proof. exact (REFL (@dollar A N')). Qed.
Definition lambda {A B : Type'} : (N -> A) -> cart A B := fun _94593 : N -> A => @ε (cart A B) (fun f : cart A B => forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94593 i)).
Lemma lambda_def {A B : Type'} : (@lambda A B) = (fun _94593 : N -> A => @ε (cart A B) (fun f : cart A B => forall i : N, ((N.le ((BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94593 i))).
Proof. exact (REFL (@lambda A B)). Qed.
Definition pastecart {A M N' : Type'} : (cart A M) -> (cart A N') -> cart A (finite_sum M N') := fun _94884 : cart A M => fun _94885 : cart A N' => @lambda A (finite_sum M N') (fun i : N => @COND A (N.le i (@dimindex M (@setT M))) (@dollar A M _94884 i) (@dollar A N' _94885 (N.sub i (@dimindex M (@setT M))))).
Lemma pastecart_def {A M N' : Type'} : (@pastecart A M N') = (fun _94884 : cart A M => fun _94885 : cart A N' => @lambda A (finite_sum M N') (fun i : N => @COND A (N.le i (@dimindex M (@setT M))) (@dollar A M _94884 i) (@dollar A N' _94885 (N.sub i (@dimindex M (@setT M)))))).
Proof. exact (REFL (@pastecart A M N')). Qed.
Definition fstcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A M := fun _94896 : cart A (finite_sum M N') => @lambda A M (fun i : N => @dollar A (finite_sum M N') _94896 i).
Lemma fstcart_def {A M N' : Type'} : (@fstcart A M N') = (fun _94896 : cart A (finite_sum M N') => @lambda A M (fun i : N => @dollar A (finite_sum M N') _94896 i)).
Proof. exact (REFL (@fstcart A M N')). Qed.
Definition sndcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A N' := fun _94901 : cart A (finite_sum M N') => @lambda A N' (fun i : N => @dollar A (finite_sum M N') _94901 (N.add i (@dimindex M (@setT M)))).
Lemma sndcart_def {A M N' : Type'} : (@sndcart A M N') = (fun _94901 : cart A (finite_sum M N') => @lambda A N' (fun i : N => @dollar A (finite_sum M N') _94901 (N.add i (@dimindex M (@setT M))))).
Proof. exact (REFL (@sndcart A M N')). Qed.
Definition _100311 {A : Type'} : (finite_sum A A) -> tybit0 A := fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) N0 a' (fun n : N => @BOTTOM (finite_sum A A))) a).
Lemma _100311_def {A : Type'} : (@_100311 A) = (fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) N0 a' (fun n : N => @BOTTOM (finite_sum A A))) a)).
Proof. exact (REFL (@_100311 A)). Qed.
Definition mktybit0 {A : Type'} : (finite_sum A A) -> tybit0 A := @_100311 A.
Lemma mktybit0_def {A : Type'} : (@mktybit0 A) = (@_100311 A).
Proof. exact (REFL (@mktybit0 A)). Qed.
Definition _100330 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) N0 a' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a).
Lemma _100330_def {A : Type'} : (@_100330 A) = (fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) N0 a' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a)).
Proof. exact (REFL (@_100330 A)). Qed.
Definition mktybit1 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := @_100330 A.
Lemma mktybit1_def {A : Type'} : (@mktybit1 A) = (@_100330 A).
Proof. exact (REFL (@mktybit1 A)). Qed.
Definition vector {A N' : Type'} : (list A) -> cart A N' := fun _102024 : list A => @lambda A N' (fun i : N => @Nth A (N.sub i ((BIT1 N0))) _102024).
Lemma vector_def {A N' : Type'} : (@vector A N') = (fun _102024 : list A => @lambda A N' (fun i : N => @Nth A (N.sub i ((BIT1 N0))) _102024)).
Proof. exact (REFL (@vector A N')). Qed.
Definition PCROSS {A M N' : Type'} : ((cart A M) -> Prop) -> ((cart A N') -> Prop) -> (cart A (finite_sum M N')) -> Prop := fun _102051 : (cart A M) -> Prop => fun _102052 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102051) /\ (@IN (cart A N') y _102052)) (@pastecart A M N' x y)).
Lemma PCROSS_def {A M N' : Type'} : (@PCROSS A M N') = (fun _102051 : (cart A M) -> Prop => fun _102052 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102051) /\ (@IN (cart A N') y _102052)) (@pastecart A M N' x y))).
Proof. exact (REFL (@PCROSS A M N')). Qed.
Definition CASEWISE {_137244 _137280 _137284 _137285 : Type'} : (list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) -> _137285 -> _137284 -> _137244 := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) -> _137285 -> _137284 -> _137244) (fun CASEWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) -> _137285 -> _137284 -> _137244 => forall _102656 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall f : _137285, forall x : _137284, (CASEWISE' _102656 (@nil (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) f x) = (@ε _137244 (fun y : _137244 => True))) /\ (forall h : prod (_137280 -> _137284) (_137285 -> _137280 -> _137244), forall t : list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244)), forall f : _137285, forall x : _137284, (CASEWISE' _102656 (@cons (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244)) h t) f x) = (@COND _137244 (exists y : _137280, (@fst (_137280 -> _137284) (_137285 -> _137280 -> _137244) h y) = x) (@snd (_137280 -> _137284) (_137285 -> _137280 -> _137244) h f (@ε _137280 (fun y : _137280 => (@fst (_137280 -> _137284) (_137285 -> _137280 -> _137244) h y) = x))) (CASEWISE' _102656 t f x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Lemma CASEWISE_def {_137244 _137280 _137284 _137285 : Type'} : (@CASEWISE _137244 _137280 _137284 _137285) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) -> _137285 -> _137284 -> _137244) (fun CASEWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) -> _137285 -> _137284 -> _137244 => forall _102656 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall f : _137285, forall x : _137284, (CASEWISE' _102656 (@nil (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244))) f x) = (@ε _137244 (fun y : _137244 => True))) /\ (forall h : prod (_137280 -> _137284) (_137285 -> _137280 -> _137244), forall t : list (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244)), forall f : _137285, forall x : _137284, (CASEWISE' _102656 (@cons (prod (_137280 -> _137284) (_137285 -> _137280 -> _137244)) h t) f x) = (@COND _137244 (exists y : _137280, (@fst (_137280 -> _137284) (_137285 -> _137280 -> _137244) h y) = x) (@snd (_137280 -> _137284) (_137285 -> _137280 -> _137244) h f (@ε _137280 (fun y : _137280 => (@fst (_137280 -> _137284) (_137285 -> _137280 -> _137244) h y) = x))) (CASEWISE' _102656 t f x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))))).
Proof. exact (REFL (@CASEWISE _137244 _137280 _137284 _137285)). Qed.
Definition admissible {_137575 _137578 _137582 _137583 _137588 : Type'} : (_137582 -> _137575 -> Prop) -> ((_137582 -> _137578) -> _137588 -> Prop) -> (_137588 -> _137575) -> ((_137582 -> _137578) -> _137588 -> _137583) -> Prop := fun _103723 : _137582 -> _137575 -> Prop => fun _103724 : (_137582 -> _137578) -> _137588 -> Prop => fun _103725 : _137588 -> _137575 => fun _103726 : (_137582 -> _137578) -> _137588 -> _137583 => forall f : _137582 -> _137578, forall g : _137582 -> _137578, forall a : _137588, ((_103724 f a) /\ ((_103724 g a) /\ (forall z : _137582, (_103723 z (_103725 a)) -> (f z) = (g z)))) -> (_103726 f a) = (_103726 g a).
Lemma admissible_def {_137575 _137578 _137582 _137583 _137588 : Type'} : (@admissible _137575 _137578 _137582 _137583 _137588) = (fun _103723 : _137582 -> _137575 -> Prop => fun _103724 : (_137582 -> _137578) -> _137588 -> Prop => fun _103725 : _137588 -> _137575 => fun _103726 : (_137582 -> _137578) -> _137588 -> _137583 => forall f : _137582 -> _137578, forall g : _137582 -> _137578, forall a : _137588, ((_103724 f a) /\ ((_103724 g a) /\ (forall z : _137582, (_103723 z (_103725 a)) -> (f z) = (g z)))) -> (_103726 f a) = (_103726 g a)).
Proof. exact (REFL (@admissible _137575 _137578 _137582 _137583 _137588)). Qed.
Definition tailadmissible {A B P : Type'} : (A -> A -> Prop) -> ((A -> B) -> P -> Prop) -> (P -> A) -> ((A -> B) -> P -> B) -> Prop := fun _103755 : A -> A -> Prop => fun _103756 : (A -> B) -> P -> Prop => fun _103757 : P -> A => fun _103758 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103755 y (G f a))) -> _103755 y (_103757 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103755 z (_103757 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103756 f a) -> (_103758 f a) = (@COND B (P' f a) (f (G f a)) (H f a)))).
Lemma tailadmissible_def {A B P : Type'} : (@tailadmissible A B P) = (fun _103755 : A -> A -> Prop => fun _103756 : (A -> B) -> P -> Prop => fun _103757 : P -> A => fun _103758 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103755 y (G f a))) -> _103755 y (_103757 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103755 z (_103757 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103756 f a) -> (_103758 f a) = (@COND B (P' f a) (f (G f a)) (H f a))))).
Proof. exact (REFL (@tailadmissible A B P)). Qed.
Definition superadmissible {_137732 _137734 _137740 : Type'} : (_137732 -> _137732 -> Prop) -> ((_137732 -> _137734) -> _137740 -> Prop) -> (_137740 -> _137732) -> ((_137732 -> _137734) -> _137740 -> _137734) -> Prop := fun _103787 : _137732 -> _137732 -> Prop => fun _103788 : (_137732 -> _137734) -> _137740 -> Prop => fun _103789 : _137740 -> _137732 => fun _103790 : (_137732 -> _137734) -> _137740 -> _137734 => (@admissible _137732 _137734 _137732 Prop _137740 _103787 (fun f : _137732 -> _137734 => fun a : _137740 => True) _103789 _103788) -> @tailadmissible _137732 _137734 _137740 _103787 _103788 _103789 _103790.
Lemma superadmissible_def {_137732 _137734 _137740 : Type'} : (@superadmissible _137732 _137734 _137740) = (fun _103787 : _137732 -> _137732 -> Prop => fun _103788 : (_137732 -> _137734) -> _137740 -> Prop => fun _103789 : _137740 -> _137732 => fun _103790 : (_137732 -> _137734) -> _137740 -> _137734 => (@admissible _137732 _137734 _137732 Prop _137740 _103787 (fun f : _137732 -> _137734 => fun a : _137740 => True) _103789 _103788) -> @tailadmissible _137732 _137734 _137740 _103787 _103788 _103789 _103790).
Proof. exact (REFL (@superadmissible _137732 _137734 _137740)). Qed.
Definition psum : (prod N N) -> (N -> R) -> R := @ε ((prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R) (fun sum' : (prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R => forall _114449 : prod N (prod N (prod N N)), (forall f : N -> R, forall n : N, (sum' _114449 (@pair N N n N0) f) = (R_of_N N0)) /\ (forall f : N -> R, forall m : N, forall n : N, (sum' _114449 (@pair N N n (N.succ m)) f) = (Rplus (sum' _114449 (@pair N N n m) f) (f (N.add n m))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))).
Lemma psum_def : psum = (@ε ((prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R) (fun sum' : (prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R => forall _114449 : prod N (prod N (prod N N)), (forall f : N -> R, forall n : N, (sum' _114449 (@pair N N n N0) f) = (R_of_N N0)) /\ (forall f : N -> R, forall m : N, forall n : N, (sum' _114449 (@pair N N n (N.succ m)) f) = (Rplus (sum' _114449 (@pair N N n m) f) (f (N.add n m))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))).
Proof. exact (REFL psum). Qed.
Definition re_Union {A : Type'} : ((A -> Prop) -> Prop) -> A -> Prop := fun _114496 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114496 s) /\ (s x).
Lemma re_Union_def {A : Type'} : (@re_Union A) = (fun _114496 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114496 s) /\ (s x)).
Proof. exact (REFL (@re_Union A)). Qed.
Definition re_union {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114501 : A -> Prop => fun _114502 : A -> Prop => fun x : A => (_114501 x) \/ (_114502 x).
Lemma re_union_def {A : Type'} : (@re_union A) = (fun _114501 : A -> Prop => fun _114502 : A -> Prop => fun x : A => (_114501 x) \/ (_114502 x)).
Proof. exact (REFL (@re_union A)). Qed.
Definition re_intersect {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114513 : A -> Prop => fun _114514 : A -> Prop => fun x : A => (_114513 x) /\ (_114514 x).
Lemma re_intersect_def {A : Type'} : (@re_intersect A) = (fun _114513 : A -> Prop => fun _114514 : A -> Prop => fun x : A => (_114513 x) /\ (_114514 x)).
Proof. exact (REFL (@re_intersect A)). Qed.
Definition re_null {A : Type'} : A -> Prop := fun x : A => False.
Lemma re_null_def {A : Type'} : (@re_null A) = (fun x : A => False).
Proof. exact (REFL (@re_null A)). Qed.
Definition re_universe {A : Type'} : A -> Prop := fun x : A => True.
Lemma re_universe_def {A : Type'} : (@re_universe A) = (fun x : A => True).
Proof. exact (REFL (@re_universe A)). Qed.
Definition re_subset {A : Type'} : (A -> Prop) -> (A -> Prop) -> Prop := fun _114525 : A -> Prop => fun _114526 : A -> Prop => forall x : A, (_114525 x) -> _114526 x.
Lemma re_subset_def {A : Type'} : (@re_subset A) = (fun _114525 : A -> Prop => fun _114526 : A -> Prop => forall x : A, (_114525 x) -> _114526 x).
Proof. exact (REFL (@re_subset A)). Qed.
Definition re_compl {A : Type'} : (A -> Prop) -> A -> Prop := fun _114537 : A -> Prop => fun x : A => ~ (_114537 x).
Lemma re_compl_def {A : Type'} : (@re_compl A) = (fun _114537 : A -> Prop => fun x : A => ~ (_114537 x)).
Proof. exact (REFL (@re_compl A)). Qed.
Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _114546 : (A -> Prop) -> Prop => (_114546 (@re_null A)) /\ ((_114546 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114546 a) /\ (_114546 b)) -> _114546 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114546) -> _114546 (@re_Union A P)))).
Lemma istopology_def {A : Type'} : (@istopology A) = (fun _114546 : (A -> Prop) -> Prop => (_114546 (@re_null A)) /\ ((_114546 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114546 a) /\ (_114546 b)) -> _114546 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114546) -> _114546 (@re_Union A P))))).
Proof. exact (REFL (@istopology A)). Qed.
Definition neigh {A : Type'} : (Topology A) -> (prod (A -> Prop) A) -> Prop := fun _114559 : Topology A => fun _114560 : prod (A -> Prop) A => exists P : A -> Prop, (@open A _114559 P) /\ ((@re_subset A P (@fst (A -> Prop) A _114560)) /\ (P (@snd (A -> Prop) A _114560))).
Lemma neigh_def {A : Type'} : (@neigh A) = (fun _114559 : Topology A => fun _114560 : prod (A -> Prop) A => exists P : A -> Prop, (@open A _114559 P) /\ ((@re_subset A P (@fst (A -> Prop) A _114560)) /\ (P (@snd (A -> Prop) A _114560)))).
Proof. exact (REFL (@neigh A)). Qed.
Definition closed {A : Type'} : (Topology A) -> (A -> Prop) -> Prop := fun _114580 : Topology A => fun _114581 : A -> Prop => @open A _114580 (@re_compl A _114581).
Lemma closed_def {A : Type'} : (@closed A) = (fun _114580 : Topology A => fun _114581 : A -> Prop => @open A _114580 (@re_compl A _114581)).
Proof. exact (REFL (@closed A)). Qed.
Definition limpt {A : Type'} : (Topology A) -> A -> (A -> Prop) -> Prop := fun _114592 : Topology A => fun _114593 : A => fun _114594 : A -> Prop => forall N' : A -> Prop, (@neigh A _114592 (@pair (A -> Prop) A N' _114593)) -> exists y : A, (~ (_114593 = y)) /\ ((_114594 y) /\ (N' y)).
Lemma limpt_def {A : Type'} : (@limpt A) = (fun _114592 : Topology A => fun _114593 : A => fun _114594 : A -> Prop => forall N' : A -> Prop, (@neigh A _114592 (@pair (A -> Prop) A N' _114593)) -> exists y : A, (~ (_114593 = y)) /\ ((_114594 y) /\ (N' y))).
Proof. exact (REFL (@limpt A)). Qed.
Definition mtop {A : Type'} : (Metric A) -> Topology A := fun _114740 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N N0) e) /\ (forall y : A, (Rlt (@mdist A _114740 (@pair A A x y)) e) -> S' y)).
Lemma mtop_def {A : Type'} : (@mtop A) = (fun _114740 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N N0) e) /\ (forall y : A, (Rlt (@mdist A _114740 (@pair A A x y)) e) -> S' y))).
Proof. exact (REFL (@mtop A)). Qed.
Definition ball {A : Type'} : (Metric A) -> (prod A R) -> A -> Prop := fun _114751 : Metric A => fun _114752 : prod A R => fun y : A => Rlt (@mdist A _114751 (@pair A A (@fst A R _114752) y)) (@snd A R _114752).
Lemma ball_def {A : Type'} : (@ball A) = (fun _114751 : Metric A => fun _114752 : prod A R => fun y : A => Rlt (@mdist A _114751 (@pair A A (@fst A R _114752) y)) (@snd A R _114752)).
Proof. exact (REFL (@ball A)). Qed.
Definition mr1 : Metric R := @metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x)))).
Lemma mr1_def : mr1 = (@metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x))))).
Proof. exact (REFL mr1). Qed.
Definition dorder {A : Type'} : (A -> A -> Prop) -> Prop := fun _114833 : A -> A -> Prop => forall x : A, forall y : A, ((_114833 x x) /\ (_114833 y y)) -> exists z : A, (_114833 z z) /\ (forall w : A, (_114833 w z) -> (_114833 w x) /\ (_114833 w y)).
Lemma dorder_def {A : Type'} : (@dorder A) = (fun _114833 : A -> A -> Prop => forall x : A, forall y : A, ((_114833 x x) /\ (_114833 y y)) -> exists z : A, (_114833 z z) /\ (forall w : A, (_114833 w z) -> (_114833 w x) /\ (_114833 w y))).
Proof. exact (REFL (@dorder A)). Qed.
Definition tends {A B : Type'} : (B -> A) -> A -> (prod (Topology A) (B -> B -> Prop)) -> Prop := fun _114838 : B -> A => fun _114839 : A => fun _114840 : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) _114840) (@pair (A -> Prop) A N' _114839)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) _114840 n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) _114840 m n) -> N' (_114838 m)).
Lemma tends_def {A B : Type'} : (@tends A B) = (fun _114838 : B -> A => fun _114839 : A => fun _114840 : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) _114840) (@pair (A -> Prop) A N' _114839)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) _114840 n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) _114840 m n) -> N' (_114838 m))).
Proof. exact (REFL (@tends A B)). Qed.
Definition bounded {A B : Type'} : (prod (Metric A) (B -> B -> Prop)) -> (B -> A) -> Prop := fun _114865 : prod (Metric A) (B -> B -> Prop) => fun _114866 : B -> A => exists k : R, exists x : A, exists N' : B, (@snd (Metric A) (B -> B -> Prop) _114865 N' N') /\ (forall n : B, (@snd (Metric A) (B -> B -> Prop) _114865 n N') -> Rlt (@mdist A (@fst (Metric A) (B -> B -> Prop) _114865) (@pair A A (_114866 n) x)) k).
Lemma bounded_def {A B : Type'} : (@bounded A B) = (fun _114865 : prod (Metric A) (B -> B -> Prop) => fun _114866 : B -> A => exists k : R, exists x : A, exists N' : B, (@snd (Metric A) (B -> B -> Prop) _114865 N' N') /\ (forall n : B, (@snd (Metric A) (B -> B -> Prop) _114865 n N') -> Rlt (@mdist A (@fst (Metric A) (B -> B -> Prop) _114865) (@pair A A (_114866 n) x)) k)).
Proof. exact (REFL (@bounded A B)). Qed.
Definition tendsto {A : Type'} : (prod (Metric A) A) -> A -> A -> Prop := fun _114882 : prod (Metric A) A => fun _114883 : A => fun _114884 : A => (Rlt (R_of_N N0) (@mdist A (@fst (Metric A) A _114882) (@pair A A (@snd (Metric A) A _114882) _114883))) /\ (Rle (@mdist A (@fst (Metric A) A _114882) (@pair A A (@snd (Metric A) A _114882) _114883)) (@mdist A (@fst (Metric A) A _114882) (@pair A A (@snd (Metric A) A _114882) _114884))).
Lemma tendsto_def {A : Type'} : (@tendsto A) = (fun _114882 : prod (Metric A) A => fun _114883 : A => fun _114884 : A => (Rlt (R_of_N N0) (@mdist A (@fst (Metric A) A _114882) (@pair A A (@snd (Metric A) A _114882) _114883))) /\ (Rle (@mdist A (@fst (Metric A) A _114882) (@pair A A (@snd (Metric A) A _114882) _114883)) (@mdist A (@fst (Metric A) A _114882) (@pair A A (@snd (Metric A) A _114882) _114884)))).
Proof. exact (REFL (@tendsto A)). Qed.
Definition tends_num_real : (N -> R) -> R -> Prop := fun _114973 : N -> R => fun _114974 : R => @tends R N _114973 _114974 (@pair (Topology R) (N -> N -> Prop) (@mtop R mr1) N.ge).
Lemma tends_num_real_def : tends_num_real = (fun _114973 : N -> R => fun _114974 : R => @tends R N _114973 _114974 (@pair (Topology R) (N -> N -> Prop) (@mtop R mr1) N.ge)).
Proof. exact (REFL tends_num_real). Qed.
Definition convergent : (N -> R) -> Prop := fun _115029 : N -> R => exists l : R, tends_num_real _115029 l.
Lemma convergent_def : convergent = (fun _115029 : N -> R => exists l : R, tends_num_real _115029 l).
Proof. exact (REFL convergent). Qed.
Definition cauchy : (N -> R) -> Prop := fun _115034 : N -> R => forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, forall m : N, forall n : N, ((N.ge m N') /\ (N.ge n N')) -> Rlt (Rabs (Rminus (_115034 m) (_115034 n))) e.
Lemma cauchy_def : cauchy = (fun _115034 : N -> R => forall e : R, (Rlt (R_of_N N0) e) -> exists N' : N, forall m : N, forall n : N, ((N.ge m N') /\ (N.ge n N')) -> Rlt (Rabs (Rminus (_115034 m) (_115034 n))) e).
Proof. exact (REFL cauchy). Qed.
Definition lim : (N -> R) -> R := fun _115039 : N -> R => @ε R (fun l : R => tends_num_real _115039 l).
Lemma lim_def : lim = (fun _115039 : N -> R => @ε R (fun l : R => tends_num_real _115039 l)).
Proof. exact (REFL lim). Qed.
Definition subseq : (N -> N) -> Prop := fun _115044 : N -> N => forall m : N, forall n : N, (N.lt m n) -> N.lt (_115044 m) (_115044 n).
Lemma subseq_def : subseq = (fun _115044 : N -> N => forall m : N, forall n : N, (N.lt m n) -> N.lt (_115044 m) (_115044 n)).
Proof. exact (REFL subseq). Qed.
Definition mono : (N -> R) -> Prop := fun _115051 : N -> R => (forall m : N, forall n : N, (N.le m n) -> Rle (_115051 m) (_115051 n)) \/ (forall m : N, forall n : N, (N.le m n) -> Rge (_115051 m) (_115051 n)).
Lemma mono_def : mono = (fun _115051 : N -> R => (forall m : N, forall n : N, (N.le m n) -> Rle (_115051 m) (_115051 n)) \/ (forall m : N, forall n : N, (N.le m n) -> Rge (_115051 m) (_115051 n))).
Proof. exact (REFL mono). Qed.
Definition sums : (N -> R) -> R -> Prop := fun _115331 : N -> R => fun _115332 : R => tends_num_real (fun n : N => psum (@pair N N N0 n) _115331) _115332.
Lemma sums_def : sums = (fun _115331 : N -> R => fun _115332 : R => tends_num_real (fun n : N => psum (@pair N N N0 n) _115331) _115332).
Proof. exact (REFL sums). Qed.
Definition summable : (N -> R) -> Prop := fun _115343 : N -> R => exists s : R, sums _115343 s.
Lemma summable_def : summable = (fun _115343 : N -> R => exists s : R, sums _115343 s).
Proof. exact (REFL summable). Qed.
Definition suminf : (N -> R) -> R := fun _115348 : N -> R => @ε R (fun s : R => sums _115348 s).
Lemma suminf_def : suminf = (fun _115348 : N -> R => @ε R (fun s : R => sums _115348 s)).
Proof. exact (REFL suminf). Qed.
Definition tends_real_real : (R -> R) -> R -> R -> Prop := fun _115416 : R -> R => fun _115417 : R => fun _115418 : R => @tends R R _115416 _115417 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115418))).
Lemma tends_real_real_def : tends_real_real = (fun _115416 : R -> R => fun _115417 : R => fun _115418 : R => @tends R R _115416 _115417 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115418)))).
Proof. exact (REFL tends_real_real). Qed.
Definition diffl : (R -> R) -> R -> R -> Prop := fun _115446 : R -> R => fun _115447 : R => fun _115448 : R => tends_real_real (fun h : R => Rdiv (Rminus (_115446 (Rplus _115448 h)) (_115446 _115448)) h) _115447 (R_of_N N0).
Lemma diffl_def : diffl = (fun _115446 : R -> R => fun _115447 : R => fun _115448 : R => tends_real_real (fun h : R => Rdiv (Rminus (_115446 (Rplus _115448 h)) (_115446 _115448)) h) _115447 (R_of_N N0)).
Proof. exact (REFL diffl). Qed.
Definition contl : (R -> R) -> R -> Prop := fun _115467 : R -> R => fun _115468 : R => tends_real_real (fun h : R => _115467 (Rplus _115468 h)) (_115467 _115468) (R_of_N N0).
Lemma contl_def : contl = (fun _115467 : R -> R => fun _115468 : R => tends_real_real (fun h : R => _115467 (Rplus _115468 h)) (_115467 _115468) (R_of_N N0)).
Proof. exact (REFL contl). Qed.
Definition differentiable : (R -> R) -> R -> Prop := fun _115479 : R -> R => fun _115480 : R => exists l : R, diffl _115479 l _115480.
Lemma differentiable_def : differentiable = (fun _115479 : R -> R => fun _115480 : R => exists l : R, diffl _115479 l _115480).
Proof. exact (REFL differentiable). Qed.
Definition fld {A : Type'} : (A -> A -> Prop) -> A -> Prop := fun _117610 : A -> A -> Prop => @GSPEC A (fun GEN_PVAR_377 : A => exists x : A, @SETSPEC A GEN_PVAR_377 (exists y : A, (_117610 x y) \/ (_117610 y x)) x).
Lemma fld_def {A : Type'} : (@fld A) = (fun _117610 : A -> A -> Prop => @GSPEC A (fun GEN_PVAR_377 : A => exists x : A, @SETSPEC A GEN_PVAR_377 (exists y : A, (_117610 x y) \/ (_117610 y x)) x)).
Proof. exact (REFL (@fld A)). Qed.
Definition qoset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117665 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117665)) -> _117665 x x) /\ (forall x : A, forall y : A, forall z : A, ((_117665 x y) /\ (_117665 y z)) -> _117665 x z).
Lemma qoset_def {A : Type'} : (@qoset A) = (fun _117665 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117665)) -> _117665 x x) /\ (forall x : A, forall y : A, forall z : A, ((_117665 x y) /\ (_117665 y z)) -> _117665 x z)).
Proof. exact (REFL (@qoset A)). Qed.
Definition poset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117670 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117670)) -> _117670 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117670 x y) /\ (_117670 y z)) -> _117670 x z) /\ (forall x : A, forall y : A, ((_117670 x y) /\ (_117670 y x)) -> x = y)).
Lemma poset_def {A : Type'} : (@poset A) = (fun _117670 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117670)) -> _117670 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117670 x y) /\ (_117670 y z)) -> _117670 x z) /\ (forall x : A, forall y : A, ((_117670 x y) /\ (_117670 y x)) -> x = y))).
Proof. exact (REFL (@poset A)). Qed.
Definition toset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117675 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117675)) -> _117675 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117675 x y) /\ (_117675 y z)) -> _117675 x z) /\ ((forall x : A, forall y : A, ((_117675 x y) /\ (_117675 y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A _117675)) /\ (@IN A y (@fld A _117675))) -> (_117675 x y) \/ (_117675 y x)))).
Lemma toset_def {A : Type'} : (@toset A) = (fun _117675 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117675)) -> _117675 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117675 x y) /\ (_117675 y z)) -> _117675 x z) /\ ((forall x : A, forall y : A, ((_117675 x y) /\ (_117675 y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A _117675)) /\ (@IN A y (@fld A _117675))) -> (_117675 x y) \/ (_117675 y x))))).
Proof. exact (REFL (@toset A)). Qed.
Definition woset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117680 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117680)) -> _117680 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117680 x y) /\ (_117680 y z)) -> _117680 x z) /\ ((forall x : A, forall y : A, ((_117680 x y) /\ (_117680 y x)) -> x = y) /\ ((forall x : A, forall y : A, ((@IN A x (@fld A _117680)) /\ (@IN A y (@fld A _117680))) -> (_117680 x y) \/ (_117680 y x)) /\ (forall s : A -> Prop, ((@subset A s (@fld A _117680)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> _117680 x y))))).
Lemma woset_def {A : Type'} : (@woset A) = (fun _117680 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117680)) -> _117680 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117680 x y) /\ (_117680 y z)) -> _117680 x z) /\ ((forall x : A, forall y : A, ((_117680 x y) /\ (_117680 y x)) -> x = y) /\ ((forall x : A, forall y : A, ((@IN A x (@fld A _117680)) /\ (@IN A y (@fld A _117680))) -> (_117680 x y) \/ (_117680 y x)) /\ (forall s : A -> Prop, ((@subset A s (@fld A _117680)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> _117680 x y)))))).
Proof. exact (REFL (@woset A)). Qed.
Definition wqoset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117685 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117685)) -> _117685 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117685 x y) /\ (_117685 y z)) -> _117685 x z) /\ (forall s : A -> Prop, (@subset A s (@fld A _117685)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (_117685 x y))))).
Lemma wqoset_def {A : Type'} : (@wqoset A) = (fun _117685 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117685)) -> _117685 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117685 x y) /\ (_117685 y z)) -> _117685 x z) /\ (forall s : A -> Prop, (@subset A s (@fld A _117685)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (_117685 x y)))))).
Proof. exact (REFL (@wqoset A)). Qed.
Definition chain {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _117690 : A -> A -> Prop => fun _117691 : A -> Prop => forall x : A, forall y : A, ((@IN A x _117691) /\ (@IN A y _117691)) -> (_117690 x y) \/ (_117690 y x).
Lemma chain_def {A : Type'} : (@chain A) = (fun _117690 : A -> A -> Prop => fun _117691 : A -> Prop => forall x : A, forall y : A, ((@IN A x _117691) /\ (@IN A y _117691)) -> (_117690 x y) \/ (_117690 y x)).
Proof. exact (REFL (@chain A)). Qed.
Definition antichain {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _117702 : A -> A -> Prop => fun _117703 : A -> Prop => (@subset A _117703 (@fld A _117702)) /\ (@pairwise A (fun x : A => fun y : A => ~ (_117702 x y)) _117703).
Lemma antichain_def {A : Type'} : (@antichain A) = (fun _117702 : A -> A -> Prop => fun _117703 : A -> Prop => (@subset A _117703 (@fld A _117702)) /\ (@pairwise A (fun x : A => fun y : A => ~ (_117702 x y)) _117703)).
Proof. exact (REFL (@antichain A)). Qed.
Definition strictly {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _118355 : A -> A -> Prop => fun x : A => fun y : A => (_118355 x y) /\ (~ (_118355 y x)).
Lemma strictly_def {A : Type'} : (@strictly A) = (fun _118355 : A -> A -> Prop => fun x : A => fun y : A => (_118355 x y) /\ (~ (_118355 y x))).
Proof. exact (REFL (@strictly A)). Qed.
Definition properly {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _118360 : A -> A -> Prop => fun x : A => fun y : A => (_118360 x y) /\ (~ (x = y)).
Lemma properly_def {A : Type'} : (@properly A) = (fun _118360 : A -> A -> Prop => fun x : A => fun y : A => (_118360 x y) /\ (~ (x = y))).
Proof. exact (REFL (@properly A)). Qed.
Definition inseg {A : Type'} : (A -> A -> Prop) -> (A -> A -> Prop) -> Prop := fun _122621 : A -> A -> Prop => fun _122622 : A -> A -> Prop => forall x : A, forall y : A, (_122621 x y) = ((_122622 x y) /\ (@fld A _122621 y)).
Lemma inseg_def {A : Type'} : (@inseg A) = (fun _122621 : A -> A -> Prop => fun _122622 : A -> A -> Prop => forall x : A, forall y : A, (_122621 x y) = ((_122622 x y) /\ (@fld A _122621 y))).
Proof. exact (REFL (@inseg A)). Qed.
Definition linseg {A : Type'} : (A -> A -> Prop) -> A -> A -> A -> Prop := fun _122693 : A -> A -> Prop => fun _122694 : A => fun x : A => fun y : A => (_122693 x y) /\ (@properly A _122693 y _122694).
Lemma linseg_def {A : Type'} : (@linseg A) = (fun _122693 : A -> A -> Prop => fun _122694 : A => fun x : A => fun y : A => (_122693 x y) /\ (@properly A _122693 y _122694)).
Proof. exact (REFL (@linseg A)). Qed.
Definition ordinal {A : Type'} : (A -> A -> Prop) -> Prop := fun _122705 : A -> A -> Prop => (@woset A _122705) /\ (forall x : A, (@fld A _122705 x) -> x = (@ε A (fun y : A => ~ (@properly A _122705 y x)))).
Lemma ordinal_def {A : Type'} : (@ordinal A) = (fun _122705 : A -> A -> Prop => (@woset A _122705) /\ (forall x : A, (@fld A _122705 x) -> x = (@ε A (fun y : A => ~ (@properly A _122705 y x))))).
Proof. exact (REFL (@ordinal A)). Qed.
Definition RC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall RC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (a1' = a0')) -> RC' a0' a1') -> RC' a0 a1.
Lemma RC_def {A : Type'} : (@RC A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall RC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (a1' = a0')) -> RC' a0' a1') -> RC' a0 a1).
Proof. exact (REFL (@RC A)). Qed.
Definition SC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall SC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (SC' a1' a0')) -> SC' a0' a1') -> SC' a0 a1.
Lemma SC_def {A : Type'} : (@SC A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall SC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (SC' a1' a0')) -> SC' a0' a1') -> SC' a0 a1).
Proof. exact (REFL (@SC A)). Qed.
Definition RSC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _198671 : A -> A -> Prop => @RC A (@SC A _198671).
Lemma RSC_def {A : Type'} : (@RSC A) = (fun _198671 : A -> A -> Prop => @RC A (@SC A _198671)).
Proof. exact (REFL (@RSC A)). Qed.
Definition RTC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _198795 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A _198795).
Lemma RTC_def {A : Type'} : (@RTC A) = (fun _198795 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A _198795)).
Proof. exact (REFL (@RTC A)). Qed.
Definition STC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _200306 : A -> A -> Prop => @Relation_Operators.clos_trans A (@SC A _200306).
Lemma STC_def {A : Type'} : (@STC A) = (fun _200306 : A -> A -> Prop => @Relation_Operators.clos_trans A (@SC A _200306)).
Proof. exact (REFL (@STC A)). Qed.
Definition RSTC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _200598 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A (@SC A _200598)).
Lemma RSTC_def {A : Type'} : (@RSTC A) = (fun _200598 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A (@SC A _200598))).
Proof. exact (REFL (@RSTC A)). Qed.
Definition INV {A B : Type'} : (B -> A -> Prop) -> A -> B -> Prop := fun _201543 : B -> A -> Prop => fun _201544 : A => fun _201545 : B => _201543 _201545 _201544.
Lemma INV_def {A B : Type'} : (@INV A B) = (fun _201543 : B -> A -> Prop => fun _201544 : A => fun _201545 : B => _201543 _201545 _201544).
Proof. exact (REFL (@INV A B)). Qed.
Definition RELPOW {A : Type'} : N -> (A -> A -> Prop) -> A -> A -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop) (fun RELPOW' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop => forall _201619 : prod N (prod N (prod N (prod N (prod N N)))), (forall R' : A -> A -> Prop, forall x : A, forall y : A, (RELPOW' _201619 N0 R' x y) = (x = y)) /\ (forall n : N, forall x : A, forall R' : A -> A -> Prop, forall y : A, (RELPOW' _201619 (N.succ n) R' x y) = (exists z : A, (RELPOW' _201619 n R' x z) /\ (R' z y)))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))))).
Lemma RELPOW_def {A : Type'} : (@RELPOW A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop) (fun RELPOW' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop => forall _201619 : prod N (prod N (prod N (prod N (prod N N)))), (forall R' : A -> A -> Prop, forall x : A, forall y : A, (RELPOW' _201619 N0 R' x y) = (x = y)) /\ (forall n : N, forall x : A, forall R' : A -> A -> Prop, forall y : A, (RELPOW' _201619 (N.succ n) R' x y) = (exists z : A, (RELPOW' _201619 n R' x z) /\ (R' z y)))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (REFL (@RELPOW A)). Qed.
Definition NORMAL {A : Type'} : (A -> A -> Prop) -> A -> Prop := fun _202277 : A -> A -> Prop => fun _202278 : A => ~ (exists y : A, _202277 _202278 y).
Lemma NORMAL_def {A : Type'} : (@NORMAL A) = (fun _202277 : A -> A -> Prop => fun _202278 : A => ~ (exists y : A, _202277 _202278 y)).
Proof. exact (REFL (@NORMAL A)). Qed.
Definition CR {A : Type'} : (A -> A -> Prop) -> Prop := fun _202289 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202289 x y1) /\ (_202289 x y2)) -> exists z : A, (_202289 y1 z) /\ (_202289 y2 z).
Lemma CR_def {A : Type'} : (@CR A) = (fun _202289 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202289 x y1) /\ (_202289 x y2)) -> exists z : A, (_202289 y1 z) /\ (_202289 y2 z)).
Proof. exact (REFL (@CR A)). Qed.
Definition WCR {A : Type'} : (A -> A -> Prop) -> Prop := fun _202294 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202294 x y1) /\ (_202294 x y2)) -> exists z : A, (@RTC A _202294 y1 z) /\ (@RTC A _202294 y2 z).
Lemma WCR_def {A : Type'} : (@WCR A) = (fun _202294 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202294 x y1) /\ (_202294 x y2)) -> exists z : A, (@RTC A _202294 y1 z) /\ (@RTC A _202294 y2 z)).
Proof. exact (REFL (@WCR A)). Qed.
Definition WN {A : Type'} : (A -> A -> Prop) -> Prop := fun _202299 : A -> A -> Prop => forall x : A, exists y : A, (@RTC A _202299 x y) /\ (@NORMAL A _202299 y).
Lemma WN_def {A : Type'} : (@WN A) = (fun _202299 : A -> A -> Prop => forall x : A, exists y : A, (@RTC A _202299 x y) /\ (@NORMAL A _202299 y)).
Proof. exact (REFL (@WN A)). Qed.
Definition SN {A : Type'} : (A -> A -> Prop) -> Prop := fun _202304 : A -> A -> Prop => ~ (exists seq : N -> A, forall n : N, _202304 (seq n) (seq (N.succ n))).
Lemma SN_def {A : Type'} : (@SN A) = (fun _202304 : A -> A -> Prop => ~ (exists seq : N -> A, forall n : N, _202304 (seq n) (seq (N.succ n)))).
Proof. exact (REFL (@SN A)). Qed.
Definition TREE {A : Type'} : (A -> A -> Prop) -> Prop := fun _202309 : A -> A -> Prop => (forall y : A, ~ (@Relation_Operators.clos_trans A _202309 y y)) /\ (exists a : A, (@IN A a (@fld A _202309)) /\ (forall y : A, (@IN A y (@fld A _202309)) -> (y = a) \/ ((@Relation_Operators.clos_trans A _202309 a y) /\ (@ex1 A (fun x : A => _202309 x y))))).
Lemma TREE_def {A : Type'} : (@TREE A) = (fun _202309 : A -> A -> Prop => (forall y : A, ~ (@Relation_Operators.clos_trans A _202309 y y)) /\ (exists a : A, (@IN A a (@fld A _202309)) /\ (forall y : A, (@IN A y (@fld A _202309)) -> (y = a) \/ ((@Relation_Operators.clos_trans A _202309 a y) /\ (@ex1 A (fun x : A => _202309 x y)))))).
Proof. exact (REFL (@TREE A)). Qed.
Definition LF {A : Type'} : (A -> A -> Prop) -> Prop := fun _202314 : A -> A -> Prop => forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_407 : A => exists y : A, @SETSPEC A GEN_PVAR_407 (_202314 x y) y)).
Lemma LF_def {A : Type'} : (@LF A) = (fun _202314 : A -> A -> Prop => forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_407 : A => exists y : A, @SETSPEC A GEN_PVAR_407 (_202314 x y) y))).
Proof. exact (REFL (@LF A)). Qed.
Definition JOINABLE {_182791 : Type'} : (_182791 -> _182791 -> Prop) -> _182791 -> _182791 -> Prop := fun _203851 : _182791 -> _182791 -> Prop => fun _203852 : _182791 => fun _203853 : _182791 => exists u : _182791, (@RTC _182791 _203851 _203852 u) /\ (@RTC _182791 _203851 _203853 u).
Lemma JOINABLE_def {_182791 : Type'} : (@JOINABLE _182791) = (fun _203851 : _182791 -> _182791 -> Prop => fun _203852 : _182791 => fun _203853 : _182791 => exists u : _182791, (@RTC _182791 _203851 _203852 u) /\ (@RTC _182791 _203851 _203853 u)).
Proof. exact (REFL (@JOINABLE _182791)). Qed.
Definition DOWNFROM : N -> list N := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N) (fun DOWNFROM' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N => forall _232638 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((DOWNFROM' _232638 N0) = (@nil N)) /\ (forall n : N, (DOWNFROM' _232638 (N.succ n)) = (@cons N n (DOWNFROM' _232638 n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Lemma DOWNFROM_def : DOWNFROM = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N) (fun DOWNFROM' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N => forall _232638 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((DOWNFROM' _232638 N0) = (@nil N)) /\ (forall n : N, (DOWNFROM' _232638 (N.succ n)) = (@cons N n (DOWNFROM' _232638 n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))))).
Proof. exact (REFL DOWNFROM). Qed.
