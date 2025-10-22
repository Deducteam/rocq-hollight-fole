(* ========================================================================= *)
(* Basic metatheorems for FOL without and with equality.                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Background theories.                                                      *)
(* ------------------------------------------------------------------------- *)

needs "Library/analysis.ml";;   (* Just for some "subseq" lemmas really      *)
needs "Library/wo.ml";;         (* Well-orders and Zorn's lemma equivalents  *)
needs "Library/rstc.ml";;       (* Reflexive-symmetric-transitive closures   *)
needs "Examples/reduct.ml";;    (* Abstract reduction relations.             *)
needs "Examples/multiwf.ml";;   (* Wellfoundedness of multiset ordering      *)

(* ------------------------------------------------------------------------- *)
(* Model theory of first order logic.                                        *)
(* ------------------------------------------------------------------------- *)

loadt "Logic/fol.ml";;          (* Basic first order logic definitions       *)
loadt "Logic/prenex.ml";;       (* Prenex normal form                        *)
loadt "Logic/skolem.ml";;       (* Skolem normal form                        *)
loadt "Logic/fol_prop.ml";;     (* Compactness etc. for propositional case   *)
loadt "Logic/canon.ml";;        (* First order case via canonical models     *)
loadt "Logic/herbrand.ml";;     (* Refinement to ground terms                *)
loadt "Logic/fole.ml";;         (* First order logic with equality           *)

(* ------------------------------------------------------------------------- *)
(* Completeness of resolution.                                               *)
(* ------------------------------------------------------------------------- *)

loadt "Logic/unif.ml";;         (* Unification algorithms and MGUs           *)
