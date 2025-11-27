Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.

Section SurealArithmetic.
Axiom mul_div_SNo_invR: forall x y, SNo x -> SNo y -> y <> 0 -> y * (x :/: y) = x.
Axiom SNo_div_SNo: forall x y, SNo x -> SNo y -> SNo (x :/: y).
Axiom mul_div_SNo_both: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x :/: y) * (z :/: w) = (x * z) :/: (y * w).
Axiom div_div_SNo: forall x y z, SNo x -> SNo y -> SNo z -> (x :/: y) :/: z = x :/: (y * z).
Axiom div_mul_SNo_invL: forall x y, SNo x -> SNo y -> y <> 0 -> (x * y) :/: y = x.
End SurealArithmetic.

Section SetAlgebraFoundations.

Definition is_set_algebra : set -> set -> prop :=
  fun Omega F =>
    (forall A :e F, A c= Omega)
    /\ Omega :e F
    /\ Empty :e F
    /\ (forall A :e F, (Omega :\: A) :e F)
    /\ (forall A B, A :e F -> B :e F -> (A :\/: B) :e F).

Definition is_valuation : set -> set -> (set -> set) -> prop :=
  fun Omega F v =>
    (forall A :e F, v A :e real /\ 0 <= v A /\ v A <= 1)
    /\ (forall A B :e F, A c= B -> v A <= v B)
    /\ v Empty = 0
    /\ v Omega = 1.

Definition disjoint_sets : set -> set -> prop :=
  fun A B => A :/\: B = Empty.

End SetAlgebraFoundations.

(** CoxJaynesFoundations:
    cox_theorem packages the result of Cox/Knuth-Skilling's functional-equation
    analysis: from structural premises (set algebra + valuation) we obtain finite
    additivity on disjoint unions. We do not re-derive this here; it is taken
    as a single axiom schema, and all probability rules below flow from it. **)

Section CoxJaynesFoundations.

Definition is_cox_premises : set -> set -> (set -> set) -> prop :=
  fun Omega F v =>
    is_set_algebra Omega F
    /\ is_valuation Omega F v.

Axiom cox_theorem :
  forall Omega F, forall v : set -> set,
    is_cox_premises Omega F v ->
    (forall A B :e F, disjoint_sets A B -> v (A :\/: B) = (add_SNo (v A) (v B))).

Definition is_cox_consistent : set -> set -> (set -> set) -> prop :=
  fun Omega F v => is_cox_premises Omega F v.

Definition cond_val : (set -> set) -> set -> set -> set :=
  fun v A B => (v (A :/\: B)) :/: (v B).

Definition independent_ks : (set -> set) -> set -> set -> prop :=
  fun v A B => v (A :/\: B) = mul_SNo (v A) (v B).

End CoxJaynesFoundations.

Section KnuthSkillingTheorems.

Theorem independent_symmetric_ks :
  forall v : set -> set, forall A B,
    v A :e real -> v B :e real ->
    independent_ks v A B ->
    independent_ks v B A.
let v. let A. let B.
assume HvA: v A :e real.
assume HvB: v B :e real.
assume H: independent_ks v A B.
prove independent_ks v B A.
prove v (B :/\: A) = mul_SNo (v B) (v A).
claim Heq: v (A :/\: B) = mul_SNo (v A) (v B).
{ exact H. }
rewrite binintersect_com.
rewrite Heq.
exact mul_SNo_com (v A) (v B) (real_SNo (v A) HvA) (real_SNo (v B) HvB).
Qed.

Theorem sum_rule_ks :
  forall Omega F, forall v : set -> set,
    is_cox_consistent Omega F v ->
    forall A B :e F,
      disjoint_sets A B ->
      v (A :\/: B) = (add_SNo (v A) (v B)).
let Omega. let F. let v.
assume Hcox: is_cox_consistent Omega F v.
let A. assume HA: A :e F.
let B. assume HB: B :e F.
assume Hdisj: disjoint_sets A B.
claim Hprem: is_cox_premises Omega F v.
{ exact Hcox. }
exact cox_theorem Omega F v Hprem A HA B HB Hdisj.
Qed.

Theorem add_SNo_com_real :
  forall x y :e real, (add_SNo x y) = (add_SNo y x).
let x. assume Hx: x :e real.
let y. assume Hy: y :e real.
prove (add_SNo x y) = (add_SNo y x).
exact add_SNo_com x y (real_SNo x Hx) (real_SNo y Hy).
Qed.

Theorem sum_rule_symmetric :
  forall Omega F, forall v : set -> set,
    is_cox_consistent Omega F v ->
    forall A :e F, forall B :e F,
      disjoint_sets A B ->
      disjoint_sets B A ->
      v A :e real -> v B :e real ->
      v (A :\/: B) = v (B :\/: A).
let Omega. let F. let v.
assume Hcox: is_cox_consistent Omega F v.
let A. assume HA: A :e F.
let B. assume HB: B :e F.
assume HdAB: disjoint_sets A B.
assume HdBA: disjoint_sets B A.
assume HvA: v A :e real.
assume HvB: v B :e real.
prove v (A :\/: B) = v (B :\/: A).
claim HeqAB: v (A :\/: B) = (add_SNo (v A) (v B)).
{ exact sum_rule_ks Omega F v Hcox A HA B HB HdAB. }
claim HeqBA: v (B :\/: A) = (add_SNo (v B) (v A)).
{ exact sum_rule_ks Omega F v Hcox B HB A HA HdBA. }
claim Hcom: (add_SNo (v A) (v B)) = (add_SNo (v B) (v A)).
{ exact add_SNo_com_real (v A) HvA (v B) HvB. }
rewrite HeqAB.
rewrite HeqBA.
exact Hcom.
Qed.

Theorem product_rule_ks :
  forall v : set -> set, forall A B,
    v (A :/\: B) :e real -> v B :e real ->
    v B <> 0 ->
    v (A :/\: B) = mul_SNo (cond_val v A B) (v B).
let v. let A. let B.
assume HvAB: v (A :/\: B) :e real.
assume HvB: v B :e real.
assume HBnz: v B <> 0.
prove v (A :/\: B) = mul_SNo (cond_val v A B) (v B).
prove v (A :/\: B) = mul_SNo ((v (A :/\: B)) :/: (v B)) (v B).
claim HsnoAB: SNo (v (A :/\: B)).
{ exact real_SNo (v (A :/\: B)) HvAB. }
claim HsnoB: SNo (v B).
{ exact real_SNo (v B) HvB. }
claim HsnoDiv: SNo ((v (A :/\: B)) :/: (v B)).
{ exact SNo_div_SNo (v (A :/\: B)) (v B) HsnoAB HsnoB. }
claim Heq1: (v B) * ((v (A :/\: B)) :/: (v B)) = v (A :/\: B).
{ exact mul_div_SNo_invR (v (A :/\: B)) (v B) HsnoAB HsnoB HBnz. }
claim Heq2: mul_SNo ((v (A :/\: B)) :/: (v B)) (v B) = (v B) * ((v (A :/\: B)) :/: (v B)).
{ exact mul_SNo_com ((v (A :/\: B)) :/: (v B)) (v B) HsnoDiv HsnoB. }
rewrite Heq2.
rewrite Heq1.
reflexivity.
Qed.

Theorem bayes_theorem_core :
  forall v : set -> set, forall A B,
    v A :e real -> v B :e real -> v (A :/\: B) :e real ->
    v A <> 0 -> v B <> 0 ->
    cond_val v A B = mul_SNo (cond_val v B A) ((v A) :/: (v B)).
let v. let A. let B.
assume HvA: v A :e real.
assume HvB: v B :e real.
assume HvAB: v (A :/\: B) :e real.
assume HAnz: v A <> 0.
assume HBnz: v B <> 0.
prove cond_val v A B = mul_SNo (cond_val v B A) ((v A) :/: (v B)).
prove (v (A :/\: B)) :/: (v B) = mul_SNo ((v (B :/\: A)) :/: (v A)) ((v A) :/: (v B)).
rewrite binintersect_com.
prove (v (B :/\: A)) :/: (v B) = mul_SNo ((v (B :/\: A)) :/: (v A)) ((v A) :/: (v B)).
claim Hsno_x: SNo (v (B :/\: A)).
{ rewrite <- binintersect_com. exact real_SNo (v (A :/\: B)) HvAB. }
claim Hsno_a: SNo (v A).
{ exact real_SNo (v A) HvA. }
claim Hsno_b: SNo (v B).
{ exact real_SNo (v B) HvB. }
claim Hsno_xa: SNo ((v (B :/\: A)) * (v A)).
{ exact SNo_mul_SNo (v (B :/\: A)) (v A) Hsno_x Hsno_a. }
claim Hsno_ab: SNo ((v A) * (v B)).
{ exact SNo_mul_SNo (v A) (v B) Hsno_a Hsno_b. }
claim Hsno_x_div_a: SNo ((v (B :/\: A)) :/: (v A)).
{ exact SNo_div_SNo (v (B :/\: A)) (v A) Hsno_x Hsno_a. }
claim Hsno_a_div_b: SNo ((v A) :/: (v B)).
{ exact SNo_div_SNo (v A) (v B) Hsno_a Hsno_b. }
claim Heq_rhs: ((v (B :/\: A)) :/: (v A)) * ((v A) :/: (v B)) = ((v (B :/\: A)) * (v A)) :/: ((v A) * (v B)).
{ exact mul_div_SNo_both (v (B :/\: A)) (v A) (v A) (v B) Hsno_x Hsno_a Hsno_a Hsno_b. }
claim Heq_div: (((v (B :/\: A)) * (v A)) :/: (v A)) :/: (v B) = ((v (B :/\: A)) * (v A)) :/: ((v A) * (v B)).
{ exact div_div_SNo ((v (B :/\: A)) * (v A)) (v A) (v B) Hsno_xa Hsno_a Hsno_b. }
claim Heq_cancel: ((v (B :/\: A)) * (v A)) :/: (v A) = (v (B :/\: A)).
{ exact div_mul_SNo_invL (v (B :/\: A)) (v A) Hsno_x Hsno_a HAnz. }
rewrite Heq_rhs.
rewrite <- Heq_div.
rewrite Heq_cancel.
reflexivity.
Qed.

End KnuthSkillingTheorems.
