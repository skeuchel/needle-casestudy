Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.
Section Namespace.
  Inductive Namespace : Type :=
    | tm .
  Lemma eq_namespace_dec (a : Namespace) (b : Namespace) :
    (sumbool (a = b) (not (a = b))).
  Proof.
    decide equality .
  Defined.
End Namespace.

Section HVarlist.
  Inductive Hvl : Type :=
    | H0 
    | HS (a : Namespace) (k : Hvl).
  
  Fixpoint appendHvl (k : Hvl) (k0 : Hvl) {struct k0} :
  Hvl :=
    match k0 with
      | (H0) => k
      | (HS a k0) => (HS a (appendHvl k k0))
    end.
  
  Lemma appendHvl_assoc  :
    (forall (k : Hvl) (k0 : Hvl) (k1 : Hvl) ,
      ((appendHvl (appendHvl k k0) k1) = (appendHvl k (appendHvl k0 k1)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End HVarlist.

Section Index.
  Inductive Index (a : Namespace) : Type :=
    | I0 
    | IS : (Index a) -> (Index a).
  
  Global Arguments I0 [a] .
  Global Arguments IS [a] _ .
  
  Lemma eq_index_dec {a : Namespace} (i : (Index a)) (j : (Index a)) :
    (sumbool (i = j) (not (i = j))).
  Proof.
    decide equality .
  Qed.
  
  Fixpoint weakenIndextm (x13 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x13
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x13 k))
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x13 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x13 k) k0) = (weakenIndextm x13 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tunit 
    | tarr (T1 : Ty) (T2 : Ty)
    | tprod (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | pprod (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | tt 
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | prod (t1 : Tm) (t2 : Tm)
    | lett (p : Pat) (t1 : Tm)
        (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  Fixpoint bindPat (p17 : Pat) {struct p17} :
  Hvl :=
    match p17 with
      | (pvar T) => (HS tm H0)
      | (pprod p1 p2) => (appendHvl (appendHvl H0 (bindPat p1)) (bindPat p2))
    end.
  Scheme ind_bindPat_Pat := Induction for Pat Sort Prop.
End Functions.

Section Shift.
  Inductive Cutoff (a : Namespace) : Type :=
    | C0 
    | CS : (Cutoff a) -> (Cutoff a).
  
  Global Arguments C0 {a} .
  Global Arguments CS {a} _ .
  Fixpoint weakenCutofftm (c : (Cutoff tm)) (k : Hvl) {struct k} :
  (Cutoff tm) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (tm) => (CS (weakenCutofftm c k))
      end
    end.
  
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) = (weakenCutofftm c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shiftIndex (c : (Cutoff tm)) (x13 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x13)
      | (CS c) => match x13 with
        | (I0) => I0
        | (IS x13) => (IS (shiftIndex c x13))
      end
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x13) => (var (shiftIndex c x13))
      | (tt) => (tt)
      | (abs T35 t21) => (abs T35 (shiftTm (CS c) t21))
      | (app t22 t23) => (app (shiftTm c t22) (shiftTm c t23))
      | (prod t24 t25) => (prod (shiftTm c t24) (shiftTm c t25))
      | (lett p18 t26 t27) => (lett p18 (shiftTm c t26) (shiftTm (weakenCutofftm c (appendHvl H0 (bindPat p18))) t27))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
    end.
  Fixpoint weakenPat (p18 : Pat) (k : Hvl) {struct k} :
  Pat :=
    match k with
      | (H0) => p18
      | (HS tm k) => (weakenPat p18 k)
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS tm k) => (shiftTm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T35 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x13 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x13
      | (HS b k) => (XS b (weakenTrace x13 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x13 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x13 k) k0) = (weakenTrace x13 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x13 : (Index tm)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x13 with
        | (I0) => s
        | (IS x13) => (var x13)
      end
      | (XS tm d) => match x13 with
        | (I0) => (var I0)
        | (IS x13) => (shiftTm C0 (substIndex d s x13))
      end
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x13) => (substIndex d s x13)
      | (tt) => (tt)
      | (abs T35 t21) => (abs T35 (substTm (weakenTrace d (HS tm H0)) s t21))
      | (app t22 t23) => (app (substTm d s t22) (substTm d s t23))
      | (prod t24 t25) => (prod (substTm d s t24) (substTm d s t25))
      | (lett p18 t26 t27) => (lett p18 (substTm d s t26) (substTm (weakenTrace d (appendHvl H0 (bindPat p18))) s t27))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p18 : Pat) ,
    ((bindPat (weakenPat p18 k)) = (bindPat p18))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPat : stability_weaken.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x13 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x13)) = (var x13))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x13) => (substIndex0_shiftIndex0_reflection_ind s k x13)
      | (tt) => eq_refl
      | (abs T35 t21) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t21 (HS tm k) s)))
      | (app t22 t23) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t22 k s) (subst0_shift0_Tm_reflection_ind t23 k s))
      | (prod t22 t23) => (f_equal2 prod (subst0_shift0_Tm_reflection_ind t22 k s) (subst0_shift0_Tm_reflection_ind t23 k s))
      | (lett p18 t22 t23) => (f_equal3 lett eq_refl (subst0_shift0_Tm_reflection_ind t22 k s) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p18))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p18))) eq_refl)) (subst0_shift0_Tm_reflection_ind t23 (appendHvl k (appendHvl H0 (bindPat p18))) s)))
    end.
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x13 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x13)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x13)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x13) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x13))
        | (tt) => eq_refl
        | (abs T35 t21) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t21 (HS tm k) c))
        | (app t22 t23) => (f_equal2 app (shift_shift0_Tm_comm_ind t22 k c) (shift_shift0_Tm_comm_ind t23 k c))
        | (prod t22 t23) => (f_equal2 prod (shift_shift0_Tm_comm_ind t22 k c) (shift_shift0_Tm_comm_ind t23 k c))
        | (lett p18 t22 t23) => (f_equal3 lett eq_refl (shift_shift0_Tm_comm_ind t22 k c) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c) k (appendHvl H0 (bindPat p18))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p18))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bindPat p18))) c) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p18)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c k (appendHvl H0 (bindPat p18)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff tm)) ,
      ((shiftTm (CS c) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c s)))) := (shift_shift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Tm_comm : interaction.
 Hint Rewrite shift_shift0_Tm_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c : (Cutoff tm)) (s : Tm) ,
      ((weakenTm (shiftTm c s) k) = (shiftTm (weakenCutofftm c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c : (Cutoff tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c k) (substIndex (weakenTrace X0 k) s x13)) = (substIndex (weakenTrace X0 k) (shiftTm c s) (shiftIndex (weakenCutofftm (CS c) k) x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x13) => (shiftTm_substIndex0_comm_ind c s k x13)
        | (tt) => eq_refl
        | (abs T35 t21) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t21 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t22 t23) => (f_equal2 app (shift_subst0_Tm_comm_ind t22 k c s) (shift_subst0_Tm_comm_ind t23 k c s))
        | (prod t22 t23) => (f_equal2 prod (shift_subst0_Tm_comm_ind t22 k c s) (shift_subst0_Tm_comm_ind t23 k c s))
        | (lett p18 t22 t23) => (f_equal3 lett eq_refl (shift_subst0_Tm_comm_ind t22 k c s) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c k (appendHvl H0 (bindPat p18))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p18))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bindPat p18))) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p18)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c) k (appendHvl H0 (bindPat p18)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c (substTm X0 s s0)) = (substTm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k) s (shiftIndex (weakenCutofftm C0 k) x13)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d k) s x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x13) => (substIndex_shiftTm0_comm_ind d s k x13)
        | (tt) => eq_refl
        | (abs T35 t21) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t21 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t22 t23) => (f_equal2 app (subst_shift0_Tm_comm_ind t22 k d s) (subst_shift0_Tm_comm_ind t23 k d s))
        | (prod t22 t23) => (f_equal2 prod (subst_shift0_Tm_comm_ind t22 k d s) (subst_shift0_Tm_comm_ind t23 k d s))
        | (lett p18 t22 t23) => (f_equal3 lett eq_refl (subst_shift0_Tm_comm_ind t22 k d s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (appendHvl H0 (bindPat p18))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p18))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bindPat p18))) d s) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p18)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (appendHvl H0 (bindPat p18)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substTm0_shiftTm0_reflection : interaction.
 Hint Rewrite substTm0_shiftTm0_reflection : reflection.
 Hint Rewrite substTm_shiftTm0_comm : interaction.
 Hint Rewrite substTm_shiftTm0_comm : subst_shift0.
 Hint Rewrite shiftTm_substTm0_comm : interaction.
 Hint Rewrite shiftTm_substTm0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d : (Trace tm)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substTm (weakenTrace d k) s (substIndex (weakenTrace X0 k) s0 x13)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substIndex (weakenTrace (XS tm d) k) s x13)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x13) => (substTm_substIndex0_commright_ind d s s0 k x13)
        | (tt) => eq_refl
        | (abs T35 t21) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t21 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t22 t23) => (f_equal2 app (subst_subst0_Tm_comm_ind t22 k d s s0) (subst_subst0_Tm_comm_ind t23 k d s s0))
        | (prod t22 t23) => (f_equal2 prod (subst_subst0_Tm_comm_ind t22 k d s s0) (subst_subst0_Tm_comm_ind t23 k d s s0))
        | (lett p18 t22 t23) => (f_equal3 lett eq_refl (subst_subst0_Tm_comm_ind t22 k d s s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (appendHvl H0 (bindPat p18))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p18))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bindPat p18))) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p18)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (appendHvl H0 (bindPat p18)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d s (substTm X0 s0 s1)) = (substTm X0 (substTm d s s0) (substTm (XS tm d) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d s s0) k) = (substTm (weakenTrace d k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite substTm_substTm0_comm : interaction.
 Hint Rewrite substTm_substTm0_comm : subst_subst0.
 Hint Rewrite weakenTm_shiftTm : weaken_shift.
 Hint Rewrite weakenTm_substTm : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a : Namespace} (k : Hvl) (i : (Index a)) {struct k} :
  Prop :=
    match k with
      | (H0) => False
      | (HS b k) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k i)
        end
        | (right n) => (wfindex k i)
      end
    end.
  Inductive wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tunit :
        (wfTy k (tunit))
    | wfTy_tarr {T35 : Ty}
        (wf : (wfTy k T35)) {T36 : Ty}
        (wf0 : (wfTy k T36)) :
        (wfTy k (tarr T35 T36))
    | wfTy_tprod {T37 : Ty}
        (wf : (wfTy k T37)) {T38 : Ty}
        (wf0 : (wfTy k T38)) :
        (wfTy k (tprod T37 T38)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T35 : Ty}
        (wf : (wfTy k T35)) :
        (wfPat k (pvar T35))
    | wfPat_pprod {p18 : Pat}
        (wf : (wfPat k p18)) {p19 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bindPat p18))) p19))
        : (wfPat k (pprod p18 p19)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x13 : (Index tm))
        (wfi : (wfindex k x13)) :
        (wfTm k (var x13))
    | wfTm_tt : (wfTm k (tt))
    | wfTm_abs {T35 : Ty}
        (wf : (wfTy k T35)) {t21 : Tm}
        (wf0 : (wfTm (HS tm k) t21)) :
        (wfTm k (abs T35 t21))
    | wfTm_app {t22 : Tm}
        (wf : (wfTm k t22)) {t23 : Tm}
        (wf0 : (wfTm k t23)) :
        (wfTm k (app t22 t23))
    | wfTm_prod {t24 : Tm}
        (wf : (wfTm k t24)) {t25 : Tm}
        (wf0 : (wfTm k t25)) :
        (wfTm k (prod t24 t25))
    | wfTm_lett {p18 : Pat}
        (wf : (wfPat k p18)) {t26 : Tm}
        (wf0 : (wfTm k t26)) {t27 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bindPat p18))) t27))
        : (wfTm k (lett p18 t26 t27)).
  Definition inversion_wfTy_tarr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H20 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T1) := match H20 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H1 T2 H2) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H20 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T2) := match H20 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H1 T2 H2) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tprod_0 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k1 (tprod T1 T2))) : (wfTy k1 T1) := match H21 in (wfTy _ S2) return match S2 return Prop with
    | (tprod T1 T2) => (wfTy k1 T1)
    | _ => True
  end with
    | (wfTy_tprod T1 H3 T2 H4) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tprod_1 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k1 (tprod T1 T2))) : (wfTy k1 T2) := match H21 in (wfTy _ S2) return match S2 return Prop with
    | (tprod T1 T2) => (wfTy k1 T2)
    | _ => True
  end with
    | (wfTy_tprod T1 H3 T2 H4) => H4
    | _ => I
  end.
  Definition inversion_wfPat_pvar_1 (k2 : Hvl) (T : Ty) (H22 : (wfPat k2 (pvar T))) : (wfTy k2 T) := match H22 in (wfPat _ p18) return match p18 return Prop with
    | (pvar T) => (wfTy k2 T)
    | _ => True
  end with
    | (wfPat_pvar T H5) => H5
    | _ => I
  end.
  Definition inversion_wfPat_pprod_0 (k3 : Hvl) (p1 : Pat) (p2 : Pat) (H23 : (wfPat k3 (pprod p1 p2))) : (wfPat k3 p1) := match H23 in (wfPat _ p19) return match p19 return Prop with
    | (pprod p1 p2) => (wfPat k3 p1)
    | _ => True
  end with
    | (wfPat_pprod p1 H6 p2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfPat_pprod_1 (k3 : Hvl) (p1 : Pat) (p2 : Pat) (H23 : (wfPat k3 (pprod p1 p2))) : (wfPat (appendHvl k3 (appendHvl H0 (bindPat p1))) p2) := match H23 in (wfPat _ p19) return match p19 return Prop with
    | (pprod p1 p2) => (wfPat (appendHvl k3 (appendHvl H0 (bindPat p1))) p2)
    | _ => True
  end with
    | (wfPat_pprod p1 H6 p2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k4 : Hvl) (x : (Index tm)) (H24 : (wfTm k4 (var x))) : (wfindex k4 x) := match H24 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k4 x)
    | _ => True
  end with
    | (wfTm_var x H8) => H8
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k6 : Hvl) (T : Ty) (t : Tm) (H26 : (wfTm k6 (abs T t))) : (wfTy k6 T) := match H26 in (wfTm _ s1) return match s1 return Prop with
    | (abs T t) => (wfTy k6 T)
    | _ => True
  end with
    | (wfTm_abs T H9 t H10) => H9
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k6 : Hvl) (T : Ty) (t : Tm) (H26 : (wfTm k6 (abs T t))) : (wfTm (HS tm k6) t) := match H26 in (wfTm _ s1) return match s1 return Prop with
    | (abs T t) => (wfTm (HS tm k6) t)
    | _ => True
  end with
    | (wfTm_abs T H9 t H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k7 : Hvl) (t1 : Tm) (t2 : Tm) (H27 : (wfTm k7 (app t1 t2))) : (wfTm k7 t1) := match H27 in (wfTm _ s2) return match s2 return Prop with
    | (app t1 t2) => (wfTm k7 t1)
    | _ => True
  end with
    | (wfTm_app t1 H11 t2 H12) => H11
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k7 : Hvl) (t1 : Tm) (t2 : Tm) (H27 : (wfTm k7 (app t1 t2))) : (wfTm k7 t2) := match H27 in (wfTm _ s2) return match s2 return Prop with
    | (app t1 t2) => (wfTm k7 t2)
    | _ => True
  end with
    | (wfTm_app t1 H11 t2 H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_prod_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H28 : (wfTm k8 (prod t1 t2))) : (wfTm k8 t1) := match H28 in (wfTm _ s3) return match s3 return Prop with
    | (prod t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_prod t1 H13 t2 H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_prod_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H28 : (wfTm k8 (prod t1 t2))) : (wfTm k8 t2) := match H28 in (wfTm _ s3) return match s3 return Prop with
    | (prod t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_prod t1 H13 t2 H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_lett_0 (k9 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H29 : (wfTm k9 (lett p t1 t2))) : (wfPat k9 p) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (lett p t1 t2) => (wfPat k9 p)
    | _ => True
  end with
    | (wfTm_lett p H15 t1 H16 t2 H17) => H15
    | _ => I
  end.
  Definition inversion_wfTm_lett_1 (k9 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H29 : (wfTm k9 (lett p t1 t2))) : (wfTm k9 t1) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (lett p t1 t2) => (wfTm k9 t1)
    | _ => True
  end with
    | (wfTm_lett p H15 t1 H16 t2 H17) => H16
    | _ => I
  end.
  Definition inversion_wfTm_lett_2 (k9 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H29 : (wfTm k9 (lett p t1 t2))) : (wfTm (appendHvl k9 (appendHvl H0 (bindPat p))) t2) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (lett p t1 t2) => (wfTm (appendHvl k9 (appendHvl H0 (bindPat p))) t2)
    | _ => True
  end with
    | (wfTm_lett p H15 t1 H16 t2 H17) => H17
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c : (Cutoff tm)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k10 : Hvl)
        :
        (shifthvl_tm C0 k10 (HS tm k10))
    | shifthvl_tm_there_tm
        (c : (Cutoff tm)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_tm c k10 k11) -> (shifthvl_tm (CS c) (HS tm k10) (HS tm k11)).
  Lemma weaken_shifthvl_tm  :
    (forall (k10 : Hvl) {c : (Cutoff tm)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_tm c k11 k12) -> (shifthvl_tm (weakenCutofftm c k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) (x13 : (Index tm)) ,
      (wfindex k10 x13) -> (wfindex k11 (shiftIndex c x13))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k10 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k10 S3)) ,
      (forall (c : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c k10 k11) -> (wfTy k11 S3)))) := (fun (k10 : Hvl) =>
    (ind_wfTy k10 (fun (S3 : Ty) (wf : (wfTy k10 S3)) =>
      (forall (c : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c k10 k11) -> (wfTy k11 S3))) (fun (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
      (wfTy_tunit k11)) (fun (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
      (wfTy_tarr k11 (IHT1 c k11 (weaken_shifthvl_tm H0 ins)) (IHT2 c k11 (weaken_shifthvl_tm H0 ins)))) (fun (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
      (wfTy_tprod k11 (IHT1 c k11 (weaken_shifthvl_tm H0 ins)) (IHT2 c k11 (weaken_shifthvl_tm H0 ins)))))).
  Definition shift_wfPat : (forall (k10 : Hvl) ,
    (forall (p20 : Pat) (wf : (wfPat k10 p20)) ,
      (forall (c : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c k10 k11) -> (wfPat k11 p20)))) := (ind_wfPat (fun (k10 : Hvl) (p20 : Pat) (wf : (wfPat k10 p20)) =>
    (forall (c : (Cutoff tm)) (k11 : Hvl) ,
      (shifthvl_tm c k10 k11) -> (wfPat k11 p20))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfPat_pvar k11 (shift_wfTy k10 T wf c k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (p1 : Pat) (wf : (wfPat k10 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k10 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfPat_pprod k11 (IHp1 c k11 (weaken_shifthvl_tm H0 ins)) (IHp2 (weakenCutofftm c (appendHvl H0 (bindPat p1))) (appendHvl k11 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p1)) ins))))).
  Definition shift_wfTm : (forall (k10 : Hvl) ,
    (forall (s5 : Tm) (wf : (wfTm k10 s5)) ,
      (forall (c : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c k10 k11) -> (wfTm k11 (shiftTm c s5))))) := (ind_wfTm (fun (k10 : Hvl) (s5 : Tm) (wf : (wfTm k10 s5)) =>
    (forall (c : (Cutoff tm)) (k11 : Hvl) ,
      (shifthvl_tm c k10 k11) -> (wfTm k11 (shiftTm c s5)))) (fun (k10 : Hvl) (x13 : (Index tm)) (wfi : (wfindex k10 x13)) (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_var k11 _ (shift_wfindex_tm c k10 k11 ins x13 wfi))) (fun (k10 : Hvl) (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_tt k11)) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS tm k10) t)) IHt (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_abs k11 (shift_wfTy k10 T wf c k11 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k11) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_app k11 (IHt1 c k11 (weaken_shifthvl_tm H0 ins)) (IHt2 c k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_prod k11 (IHt1 c k11 (weaken_shifthvl_tm H0 ins)) (IHt2 c k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (p : Pat) (wf : (wfPat k10 p)) (t1 : Tm) (wf0 : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k10 (appendHvl H0 (bindPat p))) t2)) IHt2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_lett k11 (shift_wfPat k10 p wf c k11 (weaken_shifthvl_tm H0 ins)) (IHt1 c k11 (weaken_shifthvl_tm H0 ins)) (IHt2 (weakenCutofftm c (appendHvl H0 (bindPat p))) (appendHvl k11 (appendHvl H0 (bindPat p))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p)) ins))))).
  Fixpoint weaken_wfTy (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) ,
    (wfTy (appendHvl k11 k10) (weakenTy S3 k10))) :=
    match k10 return (forall (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) ,
      (wfTy (appendHvl k11 k10) (weakenTy S3 k10))) with
      | (H0) => (fun (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) =>
        wf)
      | (HS tm k10) => (fun (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) =>
        (shift_wfTy (appendHvl k11 k10) (weakenTy S3 k10) (weaken_wfTy k10 k11 S3 wf) C0 (HS tm (appendHvl k11 k10)) (shifthvl_tm_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfPat (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) ,
    (wfPat (appendHvl k11 k10) (weakenPat p20 k10))) :=
    match k10 return (forall (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) ,
      (wfPat (appendHvl k11 k10) (weakenPat p20 k10))) with
      | (H0) => (fun (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) =>
        wf)
      | (HS tm k10) => (fun (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) =>
        (shift_wfPat (appendHvl k11 k10) (weakenPat p20 k10) (weaken_wfPat k10 k11 p20 wf) C0 (HS tm (appendHvl k11 k10)) (shifthvl_tm_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfTm (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) ,
    (wfTm (appendHvl k11 k10) (weakenTm s5 k10))) :=
    match k10 return (forall (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) ,
      (wfTm (appendHvl k11 k10) (weakenTm s5 k10))) with
      | (H0) => (fun (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) =>
        wf)
      | (HS tm k10) => (fun (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) =>
        (shift_wfTm (appendHvl k11 k10) (weakenTm s5 k10) (weaken_wfTm k10 k11 s5 wf) C0 (HS tm (appendHvl k11 k10)) (shifthvl_tm_here (appendHvl k11 k10))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k14 : Hvl) (S4 : Ty) (k15 : Hvl) (S5 : Ty) ,
    (k14 = k15) -> (S4 = S5) -> (wfTy k14 S4) -> (wfTy k15 S5)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k14 : Hvl) (p21 : Pat) (k15 : Hvl) (p22 : Pat) ,
    (k14 = k15) -> (p21 = p22) -> (wfPat k14 p21) -> (wfPat k15 p22)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k14 : Hvl) (s5 : Tm) (k15 : Hvl) (s6 : Tm) ,
    (k14 = k15) -> (s5 = s6) -> (wfTm k14 s5) -> (wfTm k15 s6)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm : infra.
 Hint Resolve shift_wfindex_tm : shift.
 Hint Resolve shift_wfindex_tm : shift_wf.
 Hint Resolve shift_wfindex_tm : wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : infra.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : shift.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : shift_wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : wf.
 Hint Constructors shifthvl_tm : infra.
 Hint Constructors shifthvl_tm : shift.
 Hint Constructors shifthvl_tm : shift_wf.
 Hint Constructors shifthvl_tm : wf.
 Hint Resolve weaken_shifthvl_tm : infra.
 Hint Resolve weaken_shifthvl_tm : shift.
 Hint Resolve weaken_shifthvl_tm : shift_wf.
 Hint Resolve weaken_shifthvl_tm : weaken.
 Hint Resolve weaken_shifthvl_tm : wf.
Section SubstWellFormed.
  Inductive substhvl_tm (k10 : Hvl) : (forall (d : (Trace tm)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k10 X0 (HS tm k10) k10)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_tm k10 d k11 k12) -> (substhvl_tm k10 (XS tm d) (HS tm k11) (HS tm k12)).
  Lemma weaken_substhvl_tm  :
    (forall {k11 : Hvl} (k10 : Hvl) {d : (Trace tm)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (substhvl_tm k11 (weakenTrace d k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k14 : Hvl} {s5 : Tm} (wft : (wfTm k14 s5)) :
    (forall {d : (Trace tm)} {k15 : Hvl} {k16 : Hvl} ,
      (substhvl_tm k14 d k15 k16) -> (forall {x13 : (Index tm)} ,
        (wfindex k15 x13) -> (wfTm k16 (substIndex d s5 x13)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_tm_wfTy {k14 : Hvl} : (forall (k15 : Hvl) ,
    (forall (S4 : Ty) (wf0 : (wfTy k15 S4)) ,
      (forall {d : (Trace tm)} {k16 : Hvl} ,
        (substhvl_tm k14 d k15 k16) -> (wfTy k16 S4)))) := (fun (k15 : Hvl) =>
    (ind_wfTy k15 (fun (S4 : Ty) (wf0 : (wfTy k15 S4)) =>
      (forall {d : (Trace tm)} {k16 : Hvl} ,
        (substhvl_tm k14 d k15 k16) -> (wfTy k16 S4))) (fun {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
      (wfTy_tunit k16)) (fun (T1 : Ty) (wf0 : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k15 T2)) IHT2 {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
      (wfTy_tarr k16 (IHT1 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)))) (fun (T1 : Ty) (wf0 : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k15 T2)) IHT2 {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
      (wfTy_tprod k16 (IHT1 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_tm_wfPat {k14 : Hvl} : (forall (k15 : Hvl) ,
    (forall (p21 : Pat) (wf0 : (wfPat k15 p21)) ,
      (forall {d : (Trace tm)} {k16 : Hvl} ,
        (substhvl_tm k14 d k15 k16) -> (wfPat k16 p21)))) := (ind_wfPat (fun (k15 : Hvl) (p21 : Pat) (wf0 : (wfPat k15 p21)) =>
    (forall {d : (Trace tm)} {k16 : Hvl} ,
      (substhvl_tm k14 d k15 k16) -> (wfPat k16 p21))) (fun (k15 : Hvl) (T : Ty) (wf0 : (wfTy k15 T)) {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (wfPat_pvar k16 (substhvl_tm_wfTy k15 T wf0 (weaken_substhvl_tm H0 del)))) (fun (k15 : Hvl) (p1 : Pat) (wf0 : (wfPat k15 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k15 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (wfPat_pprod k16 (IHp1 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)) (IHp2 (weakenTrace d (appendHvl H0 (bindPat p1))) (appendHvl k16 (appendHvl H0 (bindPat p1))) (weaken_substhvl_tm (appendHvl H0 (bindPat p1)) del))))).
  Definition substhvl_tm_wfTm {k14 : Hvl} {s5 : Tm} (wf : (wfTm k14 s5)) : (forall (k15 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k15 s6)) ,
      (forall {d : (Trace tm)} {k16 : Hvl} ,
        (substhvl_tm k14 d k15 k16) -> (wfTm k16 (substTm d s5 s6))))) := (ind_wfTm (fun (k15 : Hvl) (s6 : Tm) (wf0 : (wfTm k15 s6)) =>
    (forall {d : (Trace tm)} {k16 : Hvl} ,
      (substhvl_tm k14 d k15 k16) -> (wfTm k16 (substTm d s5 s6)))) (fun (k15 : Hvl) {x13 : (Index tm)} (wfi : (wfindex k15 x13)) {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k15 : Hvl) {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (wfTm_tt k16)) (fun (k15 : Hvl) (T : Ty) (wf0 : (wfTy k15 T)) (t : Tm) (wf1 : (wfTm (HS tm k15) t)) IHt {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (wfTm_abs k16 (substhvl_tm_wfTy k15 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k16) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k15 : Hvl) (t1 : Tm) (wf0 : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k15 t2)) IHt2 {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (wfTm_app k16 (IHt1 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)))) (fun (k15 : Hvl) (t1 : Tm) (wf0 : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k15 t2)) IHt2 {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (wfTm_prod k16 (IHt1 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)))) (fun (k15 : Hvl) (p : Pat) (wf0 : (wfPat k15 p)) (t1 : Tm) (wf1 : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k15 (appendHvl H0 (bindPat p))) t2)) IHt2 {d : (Trace tm)} {k16 : Hvl} (del : (substhvl_tm k14 d k15 k16)) =>
    (wfTm_lett k16 (substhvl_tm_wfPat k15 p wf0 (weaken_substhvl_tm H0 del)) (IHt1 (weakenTrace d H0) k16 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d (appendHvl H0 (bindPat p))) (appendHvl k16 (appendHvl H0 (bindPat p))) (weaken_substhvl_tm (appendHvl H0 (bindPat p)) del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm : infra.
 Hint Resolve substhvl_tm_wfindex_tm : subst.
 Hint Resolve substhvl_tm_wfindex_tm : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm : wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : infra.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : subst.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : wf.
 Hint Constructors substhvl_tm : infra.
 Hint Constructors substhvl_tm : subst.
 Hint Constructors substhvl_tm : subst_wf.
 Hint Constructors substhvl_tm : wf.
Fixpoint subhvl_tm (k14 : Hvl) {struct k14} :
Prop :=
  match k14 with
    | (H0) => True
    | (HS a k14) => match a with
      | (tm) => (subhvl_tm k14)
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k14 : Hvl) (k15 : Hvl) ,
    (subhvl_tm k14) -> (subhvl_tm k15) -> (subhvl_tm (appendHvl k14 k15))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k11 : Hvl) (k10 : Hvl) (p20 : Pat) ,
    (subhvl_tm k11) -> (wfPat (appendHvl k10 k11) (weakenPat p20 k11)) -> (wfPat k10 p20)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k13 : Hvl) (k12 : Hvl) (S3 : Ty) ,
    (subhvl_tm k13) -> (wfTy (appendHvl k12 k13) (weakenTy S3 k13)) -> (wfTy k12 S3)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H33 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_tm) in H33
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H34 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H34
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G2 : Env) (T : Ty).
  Fixpoint appendEnv (G2 : Env) (G3 : Env) :
  Env :=
    match G3 with
      | (empty) => G2
      | (evar G4 T) => (evar (appendEnv G2 G4) T)
    end.
  Fixpoint domainEnv (G2 : Env) :
  Hvl :=
    match G2 with
      | (empty) => H0
      | (evar G3 T) => (HS tm (domainEnv G3))
    end.
  Lemma appendEnv_assoc  :
    (forall (G2 : Env) (G3 : Env) (G4 : Env) ,
      ((appendEnv G2 (appendEnv G3 G4)) = (appendEnv (appendEnv G2 G3) G4))).
  Proof.
    needleGenericAppendEnvAssoc .
  Qed.
  Lemma domainEnv_appendEnv  :
    (forall (G2 : Env) (G3 : Env) ,
      ((domainEnv (appendEnv G2 G3)) = (appendHvl (domainEnv G2) (domainEnv G3)))).
  Proof.
    needleGenericDomainEnvAppendEnv .
  Qed.
  Fixpoint shiftEnv (c : (Cutoff tm)) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (shiftEnv c G3) T)
    end.
  Fixpoint weakenEnv (G2 : Env) (k14 : Hvl) {struct k14} :
  Env :=
    match k14 with
      | (H0) => G2
      | (HS tm k14) => (weakenEnv G2 k14)
    end.
  Fixpoint substEnv (d : (Trace tm)) (s5 : Tm) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (substEnv d s5 G3) T)
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c : (Cutoff tm)) (G2 : Env) ,
      ((domainEnv (shiftEnv c G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d : (Trace tm)) (s5 : Tm) (G2 : Env) ,
      ((domainEnv (substEnv d s5 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c : (Cutoff tm)) (G2 : Env) (G3 : Env) ,
        ((shiftEnv c (appendEnv G2 G3)) = (appendEnv (shiftEnv c G2) (shiftEnv (weakenCutofftm c (domainEnv G2)) G3)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d : (Trace tm)) (s5 : Tm) (G2 : Env) (G3 : Env) ,
        ((substEnv d s5 (appendEnv G2 G3)) = (appendEnv (substEnv d s5 G2) (substEnv (weakenTrace d (domainEnv G2)) s5 G3)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S4 : Ty) (k14 : Hvl) (k15 : Hvl) ,
      ((weakenTy (weakenTy S4 k14) k15) = (weakenTy S4 (appendHvl k14 k15)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p21 : Pat) (k14 : Hvl) (k15 : Hvl) ,
      ((weakenPat (weakenPat p21 k14) k15) = (weakenPat p21 (appendHvl k14 k15)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s5 : Tm) (k14 : Hvl) (k15 : Hvl) ,
      ((weakenTm (weakenTm s5 k14) k15) = (weakenTm s5 (appendHvl k14 k15)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G2 : Env}
          (T35 : Ty) :
          (wfTy (domainEnv G2) T35) -> (lookup_evar (evar G2 T35) I0 T35)
      | lookup_evar_there_evar
          {G2 : Env} {x13 : (Index tm)}
          (T36 : Ty) (T37 : Ty) :
          (lookup_evar G2 x13 T36) -> (lookup_evar (evar G2 T37) (IS x13) T36).
    Lemma lookup_evar_inversion_here  :
      (forall (G2 : Env) (T36 : Ty) (T37 : Ty) ,
        (lookup_evar (evar G2 T36) I0 T37) -> (T36 = T37)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G2 : Env} {x13 : (Index tm)} ,
        (forall (T36 : Ty) ,
          (lookup_evar G2 x13 T36) -> (forall (T37 : Ty) ,
            (lookup_evar G2 x13 T37) -> (T36 = T37)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G2 : Env} {x13 : (Index tm)} (T36 : Ty) ,
        (lookup_evar G2 x13 T36) -> (wfTy (domainEnv G2) T36)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G2 : Env} (G3 : Env) {x13 : (Index tm)} (T36 : Ty) ,
        (lookup_evar G2 x13 T36) -> (lookup_evar (appendEnv G2 G3) (weakenIndextm x13 (domainEnv G3)) (weakenTy T36 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G2 : Env} {x13 : (Index tm)} (T38 : Ty) ,
        (lookup_evar G2 x13 T38) -> (wfindex (domainEnv G2) x13)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G2 : Env}
        {T36 : Ty} :
        (shift_evar C0 G2 (evar G2 T36))
    | shiftevar_there_evar
        {c : (Cutoff tm)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_evar c G2 G3) -> (shift_evar (CS c) (evar G2 T) (evar G3 T)).
  Lemma weaken_shift_evar  :
    (forall (G2 : Env) {c : (Cutoff tm)} {G3 : Env} {G4 : Env} ,
      (shift_evar c G3 G4) -> (shift_evar (weakenCutofftm c (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 G2))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c : (Cutoff tm)} {G2 : Env} {G3 : Env} ,
      (shift_evar c G2 G3) -> (shifthvl_tm c (domainEnv G2) (domainEnv G3))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G2 : Env) (T36 : Ty) (s5 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G2 T36 s5 X0 (evar G2 T36) G2)
    | subst_evar_there_evar
        {d : (Trace tm)} {G3 : Env}
        {G4 : Env} (T37 : Ty) :
        (subst_evar G2 T36 s5 d G3 G4) -> (subst_evar G2 T36 s5 (XS tm d) (evar G3 T37) (evar G4 T37)).
  Lemma weaken_subst_evar {G2 : Env} (T36 : Ty) {s5 : Tm} :
    (forall (G3 : Env) {d : (Trace tm)} {G4 : Env} {G5 : Env} ,
      (subst_evar G2 T36 s5 d G4 G5) -> (subst_evar G2 T36 s5 (weakenTrace d (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 G3))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G2 : Env} {s5 : Tm} (T36 : Ty) :
    (forall {d : (Trace tm)} {G3 : Env} {G4 : Env} ,
      (subst_evar G2 T36 s5 d G3 G4) -> (substhvl_tm (domainEnv G2) d (domainEnv G3) (domainEnv G4))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Constructors lookup_evar : infra.
 Hint Constructors lookup_evar : lookup.
 Hint Constructors lookup_evar : shift.
 Hint Constructors lookup_evar : subst.
 Hint Resolve weaken_lookup_evar : infra.
 Hint Resolve weaken_lookup_evar : lookup.
 Hint Resolve weaken_lookup_evar : shift.
 Hint Resolve weaken_lookup_evar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G2 : Env} (G3 : Env) {T36 : Ty} (wf : (wfTy (domainEnv G2) T36)) ,
    (lookup_evar (appendEnv (evar G2 T36) G3) (weakenIndextm I0 (domainEnv G3)) (weakenTy T36 (domainEnv G3)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H33 : (wfTy _ (tunit)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTy _ (tarr _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTy _ (tprod _ _)) |- _ => inversion H33; subst; clear H33
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H33 : (wfPat _ (pvar _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfPat _ (pprod _ _)) |- _ => inversion H33; subst; clear H33
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H33 : (wfTm _ (var _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (tt)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (abs _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (app _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (prod _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (lett _ _ _)) |- _ => inversion H33; subst; clear H33
end : infra wf.
 Hint Resolve lookup_evar_wf : infra.
 Hint Resolve lookup_evar_wf : wf.
 Hint Resolve lookup_evar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex : wf.
 Hint Constructors shift_evar : infra.
 Hint Constructors shift_evar : shift.
 Hint Constructors shift_evar : subst.
 Hint Resolve weaken_shift_evar : infra.
 Hint Resolve weaken_shift_evar : shift.
 Hint Resolve shift_evar_shifthvl_tm : infra.
 Hint Resolve shift_evar_shifthvl_tm : shift.
 Hint Resolve shift_evar_shifthvl_tm : shift_wf.
 Hint Resolve shift_evar_shifthvl_tm : wf.
 Hint Constructors subst_evar : infra.
 Hint Constructors subst_evar : subst.
 Hint Resolve weaken_subst_evar : infra.
 Hint Resolve weaken_subst_evar : subst.
 Hint Resolve subst_evar_substhvl_tm : infra.
 Hint Resolve subst_evar_substhvl_tm : subst.
 Hint Resolve subst_evar_substhvl_tm : subst_wf.
 Hint Resolve subst_evar_substhvl_tm : wf.
 Hint Resolve subst_evar_substhvl_tm : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c : (Cutoff tm)} {G2 : Env} {G3 : Env} (ins : (shift_evar c G2 G3)) {x13 : (Index tm)} {T36 : Ty} ,
    (lookup_evar G2 x13 T36) -> (lookup_evar G3 (shiftIndex c x13) T36)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar : infra.
 Hint Resolve shift_evar_lookup_evar : lookup.
 Hint Resolve shift_evar_lookup_evar : shift.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (tunit) => 1
    | (tarr T35 T36) => (plus 1 (plus (size_Ty T35) (size_Ty T36)))
    | (tprod T37 T38) => (plus 1 (plus (size_Ty T37) (size_Ty T38)))
  end.
Fixpoint size_Pat (p18 : Pat) {struct p18} :
nat :=
  match p18 with
    | (pvar T35) => (plus 1 (size_Ty T35))
    | (pprod p19 p20) => (plus 1 (plus (size_Pat p19) (size_Pat p20)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x13) => 1
    | (tt) => 1
    | (abs T35 t21) => (plus 1 (plus (size_Ty T35) (size_Tm t21)))
    | (app t22 t23) => (plus 1 (plus (size_Tm t22) (size_Tm t23)))
    | (prod t24 t25) => (plus 1 (plus (size_Tm t24) (size_Tm t25)))
    | (lett p18 t26 t27) => (plus 1 (plus (size_Pat p18) (plus (size_Tm t26) (size_Tm t27))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (tt) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (lett p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 (weakenCutofftm c (appendHvl H0 (bindPat p)))))))
  end.
 Hint Rewrite shift_size_Tm : interaction.
 Hint Rewrite shift_size_Tm : shift_size.
Lemma weaken_size_Pat  :
  (forall (k : Hvl) (p18 : Pat) ,
    ((size_Pat (weakenPat p18 k)) = (size_Pat p18))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k : Hvl) (s : Tm) ,
    ((size_Tm (weakenTm s k)) = (size_Tm s))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k : Hvl) (S0 : Ty) ,
    ((size_Ty (weakenTy S0 k)) = (size_Ty S0))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive PTyping (G2 : Env) : Pat -> Ty -> Env -> Prop :=
  | P_Var (T : Ty)
      (H21 : (wfTy (domainEnv G2) T))
      :
      (PTyping G2 (pvar T) T (evar empty T))
  | P_Prod (T1 : Ty) (T2 : Ty)
      (p1 : Pat) (p2 : Pat) (G : Env)
      (G0 : Env)
      (wtp1 : (PTyping G2 p1 T1 G))
      (wtp2 : (PTyping (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0))
      (H23 : (wfTy (domainEnv G2) T2))
      :
      (PTyping G2 (pprod p1 p2) (tprod T1 T2) (appendEnv (appendEnv empty G) G0)).
Inductive Typing (G2 : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index tm))
      (lk : (lookup_evar G2 x T))
      (H21 : (wfTy (domainEnv G2) T))
      (H22 : (wfindex (domainEnv G2) x))
      : (Typing G2 (var x) T)
  | T_Unit :
      (Typing G2 (tt) (tunit))
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G2 T1) t (weakenTy T2 (HS tm H0))))
      (H23 : (wfTy (domainEnv G2) T1))
      (H24 : (wfTy (domainEnv G2) T2))
      :
      (Typing G2 (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm0 : (Typing G2 t1 (tarr T11 T12)))
      (jm1 : (Typing G2 t2 T11)) :
      (Typing G2 (app t1 t2) T12)
  | T_Prod (T1 : Ty) (T2 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm2 : (Typing G2 t1 T1))
      (jm3 : (Typing G2 t2 T2)) :
      (Typing G2 (prod t1 t2) (tprod T1 T2))
  | T_Let (T1 : Ty) (T2 : Ty)
      (p : Pat) (t1 : Tm) (t2 : Tm)
      (G1 : Env)
      (jm4 : (Typing G2 t1 T1))
      (wtp : (PTyping G2 p T1 G1))
      (jm5 : (Typing (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p)))))
      (H35 : (wfTy (domainEnv G2) T2))
      : (Typing G2 (lett p t1 t2) T2).
Fixpoint domain_PTyping_bindPat (G4 : Env) (p23 : Pat) (T41 : Ty) (G5 : Env) (wtp8 : (PTyping G4 p23 T41 G5)) :
((domainEnv G5) = (bindPat p23)) :=
  match wtp8 in (PTyping _ p23 T41 G5) return ((domainEnv G5) = (bindPat p23)) with
    | (P_Var T38 H35) => (eq_refl (HS tm H0))
    | (P_Prod T39 T40 p21 p22 G2 G3 wtp6 wtp7 H37) => (eq_trans (domainEnv_appendEnv (appendEnv empty G2) G3) (f_equal2 appendHvl (eq_trans (domainEnv_appendEnv empty G2) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G4 p21 T39 G2 wtp6))) (domain_PTyping_bindPat (appendEnv G4 (appendEnv empty G2)) p22 (weakenTy T40 (appendHvl H0 (bindPat p21))) G3 wtp7)))
  end.
Lemma PTyping_cast  :
  (forall (G2 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (G3 : Env) (p22 : Pat) (T39 : Ty) (G5 : Env) ,
    (G2 = G3) -> (p21 = p22) -> (T38 = T39) -> (G4 = G5) -> (PTyping G2 p21 T38 G4) -> (PTyping G3 p22 T39 G5)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G2 : Env) (t21 : Tm) (T38 : Ty) (G3 : Env) (t22 : Tm) (T39 : Ty) ,
    (G2 = G3) -> (t21 = t22) -> (T38 = T39) -> (Typing G2 t21 T38) -> (Typing G3 t22 T39)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_PTyping (G9 : Env) (p24 : Pat) (T45 : Ty) (G10 : Env) (wtp9 : (PTyping G9 p24 T45 G10)) :
(forall (c : (Cutoff tm)) (G11 : Env) (H48 : (shift_evar c G9 G11)) ,
  (PTyping G11 p24 T45 G10)) :=
  match wtp9 in (PTyping _ p24 T45 G10) return (forall (c : (Cutoff tm)) (G11 : Env) (H48 : (shift_evar c G9 G11)) ,
    (PTyping G11 p24 T45 G10)) with
    | (P_Var T42 H41) => (fun (c : (Cutoff tm)) (G11 : Env) (H48 : (shift_evar c G9 G11)) =>
      (P_Var G11 T42 (shift_wfTy _ _ H41 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H48)))))
    | (P_Prod T43 T44 p22 p23 G7 G8 wtp7 wtp8 H43) => (fun (c : (Cutoff tm)) (G11 : Env) (H48 : (shift_evar c G9 G11)) =>
      (PTyping_cast G11 _ _ _ G11 (pprod p22 p23) (tprod T43 T44) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G11 T43 T44 p22 p23 G7 G8 (shift_evar_PTyping G9 p22 T43 G7 wtp7 c G11 (weaken_shift_evar empty H48)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (shift_evar_PTyping (appendEnv G9 (appendEnv empty G7)) p23 (weakenTy T44 (appendHvl H0 (bindPat p22))) G8 wtp8 (weakenCutofftm c (domainEnv (appendEnv empty G7))) (appendEnv G11 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H48))) (shift_wfTy _ _ H43 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H48))))))
  end.
Fixpoint shift_evar_Typing (G8 : Env) (t25 : Tm) (T47 : Ty) (jm14 : (Typing G8 t25 T47)) :
(forall (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) ,
  (Typing G9 (shiftTm c t25) T47)) :=
  match jm14 in (Typing _ t25 T47) return (forall (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) ,
    (Typing G9 (shiftTm c t25) T47)) with
    | (T_Var T42 x15 lk H41 H42) => (fun (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Var G9 T42 (shiftIndex c x15) (shift_evar_lookup_evar H61 lk) (shift_wfTy _ _ H41 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61)) _ H42)))
    | (T_Unit) => (fun (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Unit G9))
    | (T_Abs T43 T46 t22 jm7 H43 H44) => (fun (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Abs G9 T43 T46 (shiftTm (CS c) t22) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G8 T43) t22 (weakenTy T46 (HS tm H0)) jm7 (CS c) (evar G9 T43) (weaken_shift_evar (evar empty T43) H61))) (shift_wfTy _ _ H43 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61))) (shift_wfTy _ _ H44 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61)))))
    | (T_App T44 T45 t23 t24 jm8 jm9) => (fun (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_App G9 T44 T45 (shiftTm c t23) (shiftTm c t24) (shift_evar_Typing G8 t23 (tarr T44 T45) jm8 c G9 (weaken_shift_evar empty H61)) (shift_evar_Typing G8 t24 T44 jm9 c G9 (weaken_shift_evar empty H61))))
    | (T_Prod T43 T46 t23 t24 jm10 jm11) => (fun (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Prod G9 T43 T46 (shiftTm c t23) (shiftTm c t24) (shift_evar_Typing G8 t23 T43 jm10 c G9 (weaken_shift_evar empty H61)) (shift_evar_Typing G8 t24 T46 jm11 c G9 (weaken_shift_evar empty H61))))
    | (T_Let T43 T46 p22 t23 t24 G7 jm12 wtp7 jm13 H55) => (fun (c : (Cutoff tm)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Let G9 T43 T46 p22 (shiftTm c t23) (shiftTm (weakenCutofftm c (appendHvl H0 (bindPat p22))) t24) G7 (shift_evar_Typing G8 t23 T43 jm12 c G9 (weaken_shift_evar empty H61)) (shift_evar_PTyping G8 p22 T43 G7 wtp7 c G9 (weaken_shift_evar empty H61)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal2 shiftTm (f_equal2 weakenCutofftm eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G8 p22 T43 G7 wtp7)))) eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (shift_evar_Typing (appendEnv G8 (appendEnv empty G7)) t24 (weakenTy T46 (appendHvl H0 (bindPat p22))) jm13 (weakenCutofftm c (domainEnv (appendEnv empty G7))) (appendEnv G9 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H61))) (shift_wfTy _ _ H55 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61)))))
  end.
 Hint Resolve shift_evar_PTyping shift_evar_Typing : infra.
 Hint Resolve shift_evar_PTyping shift_evar_Typing : shift.
Fixpoint weaken_PTyping (G2 : Env) :
(forall (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) ,
  (PTyping (appendEnv G3 G2) (weakenPat p21 (domainEnv G2)) (weakenTy T38 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) :=
  match G2 return (forall (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) ,
    (PTyping (appendEnv G3 G2) (weakenPat p21 (domainEnv G2)) (weakenTy T38 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) with
    | (empty) => (fun (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) =>
      wtp6)
    | (evar G2 T39) => (fun (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) =>
      (shift_evar_PTyping (appendEnv G3 G2) (weakenPat p21 (domainEnv G2)) (weakenTy T38 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)) (weaken_PTyping G2 G3 p21 T38 G4 wtp6) C0 (evar (appendEnv G3 G2) T39) shift_evar_here))
  end.
Fixpoint weaken_Typing (G5 : Env) :
(forall (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) ,
  (Typing (appendEnv G6 G5) (weakenTm t21 (domainEnv G5)) (weakenTy T40 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) ,
    (Typing (appendEnv G6 G5) (weakenTm t21 (domainEnv G5)) (weakenTy T40 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) =>
      jm6)
    | (evar G5 T41) => (fun (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) =>
      (shift_evar_Typing (appendEnv G6 G5) (weakenTm t21 (domainEnv G5)) (weakenTy T40 (domainEnv G5)) (weaken_Typing G5 G6 t21 T40 jm6) C0 (evar (appendEnv G6 G5) T41) shift_evar_here))
  end.
Fixpoint PTyping_wf_0 (G2 : Env) (p22 : Pat) (T42 : Ty) (G7 : Env) (wtp7 : (PTyping G2 p22 T42 G7)) {struct wtp7} :
(wfPat (domainEnv G2) p22) :=
  match wtp7 in (PTyping _ p22 T42 G7) return (wfPat (domainEnv G2) p22) with
    | (P_Var T H21) => (wfPat_pvar (domainEnv G2) H21)
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H23) => (wfPat_pprod (domainEnv G2) (PTyping_wf_0 G2 p1 T1 G wtp1) (wfPat_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p1 T1 G wtp1))))) eq_refl (PTyping_wf_0 (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0 wtp2)))
  end
with PTyping_wf_1 (G2 : Env) (p22 : Pat) (T42 : Ty) (G8 : Env) (wtp8 : (PTyping G2 p22 T42 G8)) {struct wtp8} :
(wfTy (domainEnv G2) T42) :=
  match wtp8 in (PTyping _ p22 T42 G8) return (wfTy (domainEnv G2) T42) with
    | (P_Var T H21) => H21
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H23) => (wfTy_tprod (domainEnv G2) (PTyping_wf_1 G2 p1 T1 G wtp1) H23)
  end.
Fixpoint Typing_wf_0 (G2 : Env) (t22 : Tm) (T43 : Ty) (jm7 : (Typing G2 t22 T43)) {struct jm7} :
(wfTm (domainEnv G2) t22) :=
  match jm7 in (Typing _ t22 T43) return (wfTm (domainEnv G2) t22) with
    | (T_Var T x lk H21 H22) => (wfTm_var (domainEnv G2) _ H22)
    | (T_Unit) => (wfTm_tt (domainEnv G2))
    | (T_Abs T1 T2 t jm H23 H24) => (wfTm_abs (domainEnv G2) H23 (Typing_wf_0 (evar G2 T1) t (weakenTy T2 (HS tm H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_app (domainEnv G2) (Typing_wf_0 G2 t1 (tarr T11 T12) jm0) (Typing_wf_0 G2 t2 T11 jm1))
    | (T_Prod T1 T2 t1 t2 jm2 jm3) => (wfTm_prod (domainEnv G2) (Typing_wf_0 G2 t1 T1 jm2) (Typing_wf_0 G2 t2 T2 jm3))
    | (T_Let T1 T2 p t1 t2 G1 jm4 wtp jm5 H35) => (wfTm_lett (domainEnv G2) (PTyping_wf_0 G2 p T1 G1 wtp) (Typing_wf_0 G2 t1 T1 jm4) (wfTm_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G1)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G1) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p T1 G1 wtp))))) eq_refl (Typing_wf_0 (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p))) jm5)))
  end
with Typing_wf_1 (G2 : Env) (t22 : Tm) (T43 : Ty) (jm8 : (Typing G2 t22 T43)) {struct jm8} :
(wfTy (domainEnv G2) T43) :=
  match jm8 in (Typing _ t22 T43) return (wfTy (domainEnv G2) T43) with
    | (T_Var T x lk H21 H22) => H21
    | (T_Unit) => (wfTy_tunit (domainEnv G2))
    | (T_Abs T1 T2 t jm H23 H24) => (wfTy_tarr (domainEnv G2) H23 H24)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_tarr_1 (domainEnv G2) T11 T12 (Typing_wf_1 G2 t1 (tarr T11 T12) jm0))
    | (T_Prod T1 T2 t1 t2 jm2 jm3) => (wfTy_tprod (domainEnv G2) (Typing_wf_1 G2 t1 T1 jm2) (Typing_wf_1 G2 t2 T2 jm3))
    | (T_Let T1 T2 p t1 t2 G1 jm4 wtp jm5 H35) => H35
  end.
 Hint Extern 8 => match goal with
  | H45 : (PTyping _ _ _ _) |- _ => pose proof ((PTyping_wf_0 _ _ _ _ H45)); pose proof ((PTyping_wf_1 _ _ _ _ H45)); clear H45
end : wf.
 Hint Extern 8 => match goal with
  | H46 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H46)); pose proof ((Typing_wf_1 _ _ _ H46)); clear H46
end : wf.
Class Obligation_Env_var_tm : Prop := { Env_var_tm (G9 : Env) (x15 : (Index tm)) (T : Ty) : (lookup_evar G9 x15 T) -> (Typing G9 (var x15) T) }.
Context {obligation_Env_var_tm : Obligation_Env_var_tm} .
Lemma subst_evar_lookup_evar (G10 : Env) (s5 : Tm) (T44 : Ty) (jm9 : (Typing G10 s5 T44)) :
  (forall (d : (Trace tm)) (G11 : Env) (G13 : Env) (sub : (subst_evar G10 T44 s5 d G11 G13)) (x16 : (Index tm)) (T45 : Ty) ,
    (lookup_evar G11 x16 T45) -> (Typing G13 (substIndex d s5 x16) T45)).
Proof.
  needleGenericSubstEnvLookupHom (Env_var_tm).
Qed.
Class Obligation_Env_reg_Typing : Prop := { Env_reg_T_Var (G2 : Env) (T : Ty) (s5 : Tm) (jm9 : (Typing G2 s5 T)) (H21 : (wfTy (domainEnv G2) T)) (H47 : (wfTm (domainEnv G2) s5)) : (Typing G2 (weakenTm s5 H0) T) }.
Context {obligation_Env_reg_Typing : Obligation_Env_reg_Typing} .
Fixpoint subst_evar_PTyping (G13 : Env) (s6 : Tm) (T44 : Ty) (jm10 : (Typing G13 s6 T44)) (G12 : Env) (p : Pat) (T : Ty) (G14 : Env) (wtp11 : (PTyping G12 p T G14)) :
(forall (G15 : Env) (d : (Trace tm)) (H54 : (subst_evar G13 T44 s6 d G12 G15)) ,
  (PTyping G15 p T G14)) :=
  match wtp11 in (PTyping _ p T G14) return (forall (G15 : Env) (d : (Trace tm)) (H54 : (subst_evar G13 T44 s6 d G12 G15)) ,
    (PTyping G15 p T G14)) with
    | (P_Var T45 H49) => (fun (G15 : Env) (d : (Trace tm)) (H54 : (subst_evar G13 T44 s6 d G12 G15)) =>
      (P_Var G15 T45 (substhvl_tm_wfTy _ _ H49 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H54)))))
    | (P_Prod T46 T47 p23 p24 G10 G11 wtp9 wtp10 H51) => (fun (G15 : Env) (d : (Trace tm)) (H54 : (subst_evar G13 T44 s6 d G12 G15)) =>
      (PTyping_cast G15 _ _ _ G15 (pprod p23 p24) (tprod T46 T47) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G15 T46 T47 p23 p24 G10 G11 (subst_evar_PTyping G13 s6 T44 jm10 G12 p23 T46 G10 wtp9 G15 d (weaken_subst_evar _ empty H54)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (subst_evar_PTyping G13 s6 T44 jm10 (appendEnv G12 (appendEnv empty G10)) p24 (weakenTy T47 (appendHvl H0 (bindPat p23))) G11 wtp10 (appendEnv G15 (appendEnv empty G10)) (weakenTrace d (domainEnv (appendEnv empty G10))) (weaken_subst_evar _ (appendEnv empty G10) H54))) (substhvl_tm_wfTy _ _ H51 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H54))))))
  end.
Fixpoint subst_evar_Typing (G12 : Env) (s6 : Tm) (T45 : Ty) (jm17 : (Typing G12 s6 T45)) (G11 : Env) (t : Tm) (T : Ty) (jm18 : (Typing G11 t T)) :
(forall (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) ,
  (Typing G13 (substTm d s6 t) T)) :=
  match jm18 in (Typing _ t T) return (forall (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) ,
    (Typing G13 (substTm d s6 t) T)) with
    | (T_Var T46 x16 lk H50 H51) => (fun (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) =>
      (Env_reg_T_Var G13 T46 _ (subst_evar_lookup_evar G12 s6 T45 jm17 d _ _ H68 x16 T46 lk) (substhvl_tm_wfTy _ _ H50 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H68))) (substhvl_tm_wfindex_tm (Typing_wf_0 G12 s6 T45 jm17) (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H68)) H51)))
    | (T_Unit) => (fun (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) =>
      (T_Unit G13))
    | (T_Abs T47 T50 t23 jm10 H52 H53) => (fun (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) =>
      (T_Abs G13 T47 T50 (substTm (weakenTrace d (HS tm H0)) s6 t23) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G12 s6 T45 jm17 (evar G11 T47) t23 (weakenTy T50 (HS tm H0)) jm10 (appendEnv G13 (evar empty T47)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T47) H68))) (substhvl_tm_wfTy _ _ H52 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H68))) (substhvl_tm_wfTy _ _ H53 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H68)))))
    | (T_App T48 T49 t24 t25 jm11 jm12) => (fun (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) =>
      (T_App G13 T48 T49 (substTm (weakenTrace d H0) s6 t24) (substTm (weakenTrace d H0) s6 t25) (subst_evar_Typing G12 s6 T45 jm17 G11 t24 (tarr T48 T49) jm11 G13 d (weaken_subst_evar _ empty H68)) (subst_evar_Typing G12 s6 T45 jm17 G11 t25 T48 jm12 G13 d (weaken_subst_evar _ empty H68))))
    | (T_Prod T47 T50 t24 t25 jm13 jm14) => (fun (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) =>
      (T_Prod G13 T47 T50 (substTm (weakenTrace d H0) s6 t24) (substTm (weakenTrace d H0) s6 t25) (subst_evar_Typing G12 s6 T45 jm17 G11 t24 T47 jm13 G13 d (weaken_subst_evar _ empty H68)) (subst_evar_Typing G12 s6 T45 jm17 G11 t25 T50 jm14 G13 d (weaken_subst_evar _ empty H68))))
    | (T_Let T47 T50 p23 t24 t25 G10 jm15 wtp9 jm16 H64) => (fun (G13 : Env) (d : (Trace tm)) (H68 : (subst_evar G12 T45 s6 d G11 G13)) =>
      (T_Let G13 T47 T50 p23 (substTm (weakenTrace d H0) s6 t24) (substTm (weakenTrace d (appendHvl H0 (bindPat p23))) s6 t25) G10 (subst_evar_Typing G12 s6 T45 jm17 G11 t24 T47 jm15 G13 d (weaken_subst_evar _ empty H68)) (subst_evar_PTyping G12 s6 T45 jm17 G11 p23 T47 G10 wtp9 G13 d (weaken_subst_evar _ empty H68)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal3 substTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G10) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G11 p23 T47 G10 wtp9)))) eq_refl eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (subst_evar_Typing G12 s6 T45 jm17 (appendEnv G11 (appendEnv empty G10)) t25 (weakenTy T50 (appendHvl H0 (bindPat p23))) jm16 (appendEnv G13 (appendEnv empty G10)) (weakenTrace d (domainEnv (appendEnv empty G10))) (weaken_subst_evar _ (appendEnv empty G10) H68))) (substhvl_tm_wfTy _ _ H64 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H68)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.