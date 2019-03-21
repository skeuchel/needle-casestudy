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
  
  Fixpoint weakenIndextm (x8 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x8
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x8 k))
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x8 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x8 k) k0) = (weakenIndextm x8 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tunit 
    | tarr (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | tt 
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  
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
  Fixpoint shiftIndex (c : (Cutoff tm)) (x8 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x8)
      | (CS c) => match x8 with
        | (I0) => I0
        | (IS x8) => (IS (shiftIndex c x8))
      end
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x8) => (var (shiftIndex c x8))
      | (tt) => (tt)
      | (abs T15 t9) => (abs T15 (shiftTm (CS c) t9))
      | (app t10 t11) => (app (shiftTm c t10) (shiftTm c t11))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
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
        (T15 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x8 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x8
      | (HS b k) => (XS b (weakenTrace x8 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x8 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x8 k) k0) = (weakenTrace x8 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x8 : (Index tm)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x8 with
        | (I0) => s
        | (IS x8) => (var x8)
      end
      | (XS tm d) => match x8 with
        | (I0) => (var I0)
        | (IS x8) => (shiftTm C0 (substIndex d s x8))
      end
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x8) => (substIndex d s x8)
      | (tt) => (tt)
      | (abs T15 t9) => (abs T15 (substTm (weakenTrace d (HS tm H0)) s t9))
      | (app t10 t11) => (app (substTm d s t10) (substTm d s t11))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x8 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x8)) = (var x8))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x8) => (substIndex0_shiftIndex0_reflection_ind s k x8)
      | (tt) => eq_refl
      | (abs T15 t9) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t9 (HS tm k) s)))
      | (app t10 t11) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t10 k s) (subst0_shift0_Tm_reflection_ind t11 k s))
    end.
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x8 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x8)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x8)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x8) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x8))
        | (tt) => eq_refl
        | (abs T15 t9) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t9 (HS tm k) c))
        | (app t10 t11) => (f_equal2 app (shift_shift0_Tm_comm_ind t10 k c) (shift_shift0_Tm_comm_ind t11 k c))
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
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c k) (substIndex (weakenTrace X0 k) s x8)) = (substIndex (weakenTrace X0 k) (shiftTm c s) (shiftIndex (weakenCutofftm (CS c) k) x8)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x8) => (shiftTm_substIndex0_comm_ind c s k x8)
        | (tt) => eq_refl
        | (abs T15 t9) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t9 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t10 t11) => (f_equal2 app (shift_subst0_Tm_comm_ind t10 k c s) (shift_subst0_Tm_comm_ind t11 k c s))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c (substTm X0 s s0)) = (substTm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k) s (shiftIndex (weakenCutofftm C0 k) x8)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d k) s x8)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x8) => (substIndex_shiftTm0_comm_ind d s k x8)
        | (tt) => eq_refl
        | (abs T15 t9) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t9 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t10 t11) => (f_equal2 app (subst_shift0_Tm_comm_ind t10 k d s) (subst_shift0_Tm_comm_ind t11 k d s))
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
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((substTm (weakenTrace d k) s (substIndex (weakenTrace X0 k) s0 x8)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substIndex (weakenTrace (XS tm d) k) s x8)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x8) => (substTm_substIndex0_commright_ind d s s0 k x8)
        | (tt) => eq_refl
        | (abs T15 t9) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t9 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t10 t11) => (f_equal2 app (subst_subst0_Tm_comm_ind t10 k d s s0) (subst_subst0_Tm_comm_ind t11 k d s s0))
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
    | wfTy_tarr {T15 : Ty}
        (wf : (wfTy k T15)) {T16 : Ty}
        (wf0 : (wfTy k T16)) :
        (wfTy k (tarr T15 T16)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x8 : (Index tm))
        (wfi : (wfindex k x8)) :
        (wfTm k (var x8))
    | wfTm_tt : (wfTm k (tt))
    | wfTm_abs {T15 : Ty}
        (wf : (wfTy k T15)) {t9 : Tm}
        (wf0 : (wfTm (HS tm k) t9)) :
        (wfTm k (abs T15 t9))
    | wfTm_app {t10 : Tm}
        (wf : (wfTm k t10)) {t11 : Tm}
        (wf0 : (wfTm k t11)) :
        (wfTm k (app t10 t11)).
  Definition inversion_wfTy_tarr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H10 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T1) := match H10 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H1 T2 H2) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H10 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T2) := match H10 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H1 T2 H2) => H2
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k1 : Hvl) (x : (Index tm)) (H11 : (wfTm k1 (var x))) : (wfindex k1 x) := match H11 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k1 x)
    | _ => True
  end with
    | (wfTm_var x H3) => H3
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k3 : Hvl) (T : Ty) (t : Tm) (H13 : (wfTm k3 (abs T t))) : (wfTy k3 T) := match H13 in (wfTm _ s1) return match s1 return Prop with
    | (abs T t) => (wfTy k3 T)
    | _ => True
  end with
    | (wfTm_abs T H4 t H5) => H4
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k3 : Hvl) (T : Ty) (t : Tm) (H13 : (wfTm k3 (abs T t))) : (wfTm (HS tm k3) t) := match H13 in (wfTm _ s1) return match s1 return Prop with
    | (abs T t) => (wfTm (HS tm k3) t)
    | _ => True
  end with
    | (wfTm_abs T H4 t H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k4 : Hvl) (t1 : Tm) (t2 : Tm) (H14 : (wfTm k4 (app t1 t2))) : (wfTm k4 t1) := match H14 in (wfTm _ s2) return match s2 return Prop with
    | (app t1 t2) => (wfTm k4 t1)
    | _ => True
  end with
    | (wfTm_app t1 H6 t2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k4 : Hvl) (t1 : Tm) (t2 : Tm) (H14 : (wfTm k4 (app t1 t2))) : (wfTm k4 t2) := match H14 in (wfTm _ s2) return match s2 return Prop with
    | (app t1 t2) => (wfTm k4 t2)
    | _ => True
  end with
    | (wfTm_app t1 H6 t2 H7) => H7
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c : (Cutoff tm)) (k5 : Hvl) (k6 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k5 : Hvl)
        : (shifthvl_tm C0 k5 (HS tm k5))
    | shifthvl_tm_there_tm
        (c : (Cutoff tm)) (k5 : Hvl)
        (k6 : Hvl) :
        (shifthvl_tm c k5 k6) -> (shifthvl_tm (CS c) (HS tm k5) (HS tm k6)).
  Lemma weaken_shifthvl_tm  :
    (forall (k5 : Hvl) {c : (Cutoff tm)} {k6 : Hvl} {k7 : Hvl} ,
      (shifthvl_tm c k6 k7) -> (shifthvl_tm (weakenCutofftm c k5) (appendHvl k6 k5) (appendHvl k7 k5))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k5 : Hvl) (k6 : Hvl) (ins : (shifthvl_tm c k5 k6)) (x8 : (Index tm)) ,
      (wfindex k5 x8) -> (wfindex k6 (shiftIndex c x8))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k5 : Hvl) ,
    (forall (S2 : Ty) (wf : (wfTy k5 S2)) ,
      (forall (c : (Cutoff tm)) (k6 : Hvl) ,
        (shifthvl_tm c k5 k6) -> (wfTy k6 S2)))) := (fun (k5 : Hvl) =>
    (ind_wfTy k5 (fun (S2 : Ty) (wf : (wfTy k5 S2)) =>
      (forall (c : (Cutoff tm)) (k6 : Hvl) ,
        (shifthvl_tm c k5 k6) -> (wfTy k6 S2))) (fun (c : (Cutoff tm)) (k6 : Hvl) (ins : (shifthvl_tm c k5 k6)) =>
      (wfTy_tunit k6)) (fun (T1 : Ty) (wf : (wfTy k5 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k5 T2)) IHT2 (c : (Cutoff tm)) (k6 : Hvl) (ins : (shifthvl_tm c k5 k6)) =>
      (wfTy_tarr k6 (IHT1 c k6 (weaken_shifthvl_tm H0 ins)) (IHT2 c k6 (weaken_shifthvl_tm H0 ins)))))).
  Definition shift_wfTm : (forall (k5 : Hvl) ,
    (forall (s3 : Tm) (wf : (wfTm k5 s3)) ,
      (forall (c : (Cutoff tm)) (k6 : Hvl) ,
        (shifthvl_tm c k5 k6) -> (wfTm k6 (shiftTm c s3))))) := (ind_wfTm (fun (k5 : Hvl) (s3 : Tm) (wf : (wfTm k5 s3)) =>
    (forall (c : (Cutoff tm)) (k6 : Hvl) ,
      (shifthvl_tm c k5 k6) -> (wfTm k6 (shiftTm c s3)))) (fun (k5 : Hvl) (x8 : (Index tm)) (wfi : (wfindex k5 x8)) (c : (Cutoff tm)) (k6 : Hvl) (ins : (shifthvl_tm c k5 k6)) =>
    (wfTm_var k6 _ (shift_wfindex_tm c k5 k6 ins x8 wfi))) (fun (k5 : Hvl) (c : (Cutoff tm)) (k6 : Hvl) (ins : (shifthvl_tm c k5 k6)) =>
    (wfTm_tt k6)) (fun (k5 : Hvl) (T : Ty) (wf : (wfTy k5 T)) (t : Tm) (wf0 : (wfTm (HS tm k5) t)) IHt (c : (Cutoff tm)) (k6 : Hvl) (ins : (shifthvl_tm c k5 k6)) =>
    (wfTm_abs k6 (shift_wfTy k5 T wf c k6 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k6) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k5 : Hvl) (t1 : Tm) (wf : (wfTm k5 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k5 t2)) IHt2 (c : (Cutoff tm)) (k6 : Hvl) (ins : (shifthvl_tm c k5 k6)) =>
    (wfTm_app k6 (IHt1 c k6 (weaken_shifthvl_tm H0 ins)) (IHt2 c k6 (weaken_shifthvl_tm H0 ins))))).
  Fixpoint weaken_wfTy (k5 : Hvl) {struct k5} :
  (forall (k6 : Hvl) (S2 : Ty) (wf : (wfTy k6 S2)) ,
    (wfTy (appendHvl k6 k5) (weakenTy S2 k5))) :=
    match k5 return (forall (k6 : Hvl) (S2 : Ty) (wf : (wfTy k6 S2)) ,
      (wfTy (appendHvl k6 k5) (weakenTy S2 k5))) with
      | (H0) => (fun (k6 : Hvl) (S2 : Ty) (wf : (wfTy k6 S2)) =>
        wf)
      | (HS tm k5) => (fun (k6 : Hvl) (S2 : Ty) (wf : (wfTy k6 S2)) =>
        (shift_wfTy (appendHvl k6 k5) (weakenTy S2 k5) (weaken_wfTy k5 k6 S2 wf) C0 (HS tm (appendHvl k6 k5)) (shifthvl_tm_here (appendHvl k6 k5))))
    end.
  Fixpoint weaken_wfTm (k5 : Hvl) {struct k5} :
  (forall (k6 : Hvl) (s3 : Tm) (wf : (wfTm k6 s3)) ,
    (wfTm (appendHvl k6 k5) (weakenTm s3 k5))) :=
    match k5 return (forall (k6 : Hvl) (s3 : Tm) (wf : (wfTm k6 s3)) ,
      (wfTm (appendHvl k6 k5) (weakenTm s3 k5))) with
      | (H0) => (fun (k6 : Hvl) (s3 : Tm) (wf : (wfTm k6 s3)) =>
        wf)
      | (HS tm k5) => (fun (k6 : Hvl) (s3 : Tm) (wf : (wfTm k6 s3)) =>
        (shift_wfTm (appendHvl k6 k5) (weakenTm s3 k5) (weaken_wfTm k5 k6 s3 wf) C0 (HS tm (appendHvl k6 k5)) (shifthvl_tm_here (appendHvl k6 k5))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k5 : Hvl) (S2 : Ty) (k6 : Hvl) (S3 : Ty) ,
    (k5 = k6) -> (S2 = S3) -> (wfTy k5 S2) -> (wfTy k6 S3)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k5 : Hvl) (s3 : Tm) (k6 : Hvl) (s4 : Tm) ,
    (k5 = k6) -> (s3 = s4) -> (wfTm k5 s3) -> (wfTm k6 s4)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm : infra.
 Hint Resolve shift_wfindex_tm : shift.
 Hint Resolve shift_wfindex_tm : shift_wf.
 Hint Resolve shift_wfindex_tm : wf.
 Hint Resolve shift_wfTm shift_wfTy : infra.
 Hint Resolve shift_wfTm shift_wfTy : shift.
 Hint Resolve shift_wfTm shift_wfTy : shift_wf.
 Hint Resolve shift_wfTm shift_wfTy : wf.
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
  Inductive substhvl_tm (k5 : Hvl) : (forall (d : (Trace tm)) (k6 : Hvl) (k7 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k5 X0 (HS tm k5) k5)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k6 : Hvl}
        {k7 : Hvl} :
        (substhvl_tm k5 d k6 k7) -> (substhvl_tm k5 (XS tm d) (HS tm k6) (HS tm k7)).
  Lemma weaken_substhvl_tm  :
    (forall {k6 : Hvl} (k5 : Hvl) {d : (Trace tm)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_tm k6 d k7 k8) -> (substhvl_tm k6 (weakenTrace d k5) (appendHvl k7 k5) (appendHvl k8 k5))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k5 : Hvl} {s3 : Tm} (wft : (wfTm k5 s3)) :
    (forall {d : (Trace tm)} {k6 : Hvl} {k7 : Hvl} ,
      (substhvl_tm k5 d k6 k7) -> (forall {x8 : (Index tm)} ,
        (wfindex k6 x8) -> (wfTm k7 (substIndex d s3 x8)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_tm_wfTy {k5 : Hvl} : (forall (k6 : Hvl) ,
    (forall (S2 : Ty) (wf0 : (wfTy k6 S2)) ,
      (forall {d : (Trace tm)} {k7 : Hvl} ,
        (substhvl_tm k5 d k6 k7) -> (wfTy k7 S2)))) := (fun (k6 : Hvl) =>
    (ind_wfTy k6 (fun (S2 : Ty) (wf0 : (wfTy k6 S2)) =>
      (forall {d : (Trace tm)} {k7 : Hvl} ,
        (substhvl_tm k5 d k6 k7) -> (wfTy k7 S2))) (fun {d : (Trace tm)} {k7 : Hvl} (del : (substhvl_tm k5 d k6 k7)) =>
      (wfTy_tunit k7)) (fun (T1 : Ty) (wf0 : (wfTy k6 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k6 T2)) IHT2 {d : (Trace tm)} {k7 : Hvl} (del : (substhvl_tm k5 d k6 k7)) =>
      (wfTy_tarr k7 (IHT1 (weakenTrace d H0) k7 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k7 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_tm_wfTm {k5 : Hvl} {s3 : Tm} (wf : (wfTm k5 s3)) : (forall (k6 : Hvl) ,
    (forall (s4 : Tm) (wf0 : (wfTm k6 s4)) ,
      (forall {d : (Trace tm)} {k7 : Hvl} ,
        (substhvl_tm k5 d k6 k7) -> (wfTm k7 (substTm d s3 s4))))) := (ind_wfTm (fun (k6 : Hvl) (s4 : Tm) (wf0 : (wfTm k6 s4)) =>
    (forall {d : (Trace tm)} {k7 : Hvl} ,
      (substhvl_tm k5 d k6 k7) -> (wfTm k7 (substTm d s3 s4)))) (fun (k6 : Hvl) {x8 : (Index tm)} (wfi : (wfindex k6 x8)) {d : (Trace tm)} {k7 : Hvl} (del : (substhvl_tm k5 d k6 k7)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k6 : Hvl) {d : (Trace tm)} {k7 : Hvl} (del : (substhvl_tm k5 d k6 k7)) =>
    (wfTm_tt k7)) (fun (k6 : Hvl) (T : Ty) (wf0 : (wfTy k6 T)) (t : Tm) (wf1 : (wfTm (HS tm k6) t)) IHt {d : (Trace tm)} {k7 : Hvl} (del : (substhvl_tm k5 d k6 k7)) =>
    (wfTm_abs k7 (substhvl_tm_wfTy k6 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k7) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k6 : Hvl) (t1 : Tm) (wf0 : (wfTm k6 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k6 t2)) IHt2 {d : (Trace tm)} {k7 : Hvl} (del : (substhvl_tm k5 d k6 k7)) =>
    (wfTm_app k7 (IHt1 (weakenTrace d H0) k7 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k7 (weaken_substhvl_tm H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm : infra.
 Hint Resolve substhvl_tm_wfindex_tm : subst.
 Hint Resolve substhvl_tm_wfindex_tm : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm : wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : infra.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : subst.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : wf.
 Hint Constructors substhvl_tm : infra.
 Hint Constructors substhvl_tm : subst.
 Hint Constructors substhvl_tm : subst_wf.
 Hint Constructors substhvl_tm : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
    end.
  Lemma appendEnv_assoc  :
    (forall (G : Env) (G0 : Env) (G1 : Env) ,
      ((appendEnv G (appendEnv G0 G1)) = (appendEnv (appendEnv G G0) G1))).
  Proof.
    needleGenericAppendEnvAssoc .
  Qed.
  Lemma domainEnv_appendEnv  :
    (forall (G : Env) (G0 : Env) ,
      ((domainEnv (appendEnv G G0)) = (appendHvl (domainEnv G) (domainEnv G0)))).
  Proof.
    needleGenericDomainEnvAppendEnv .
  Qed.
  Fixpoint shiftEnv (c : (Cutoff tm)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c G0) T)
    end.
  Fixpoint weakenEnv (G : Env) (k5 : Hvl) {struct k5} :
  Env :=
    match k5 with
      | (H0) => G
      | (HS tm k5) => (weakenEnv G k5)
    end.
  Fixpoint substEnv (d : (Trace tm)) (s3 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s3 G0) T)
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d : (Trace tm)) (s3 : Tm) (G : Env) ,
      ((domainEnv (substEnv d s3 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c (appendEnv G G0)) = (appendEnv (shiftEnv c G) (shiftEnv (weakenCutofftm c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d : (Trace tm)) (s3 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d s3 (appendEnv G G0)) = (appendEnv (substEnv d s3 G) (substEnv (weakenTrace d (domainEnv G)) s3 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S2 : Ty) (k5 : Hvl) (k6 : Hvl) ,
      ((weakenTy (weakenTy S2 k5) k6) = (weakenTy S2 (appendHvl k5 k6)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s3 : Tm) (k5 : Hvl) (k6 : Hvl) ,
      ((weakenTm (weakenTm s3 k5) k6) = (weakenTm s3 (appendHvl k5 k6)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T15 : Ty) :
          (wfTy (domainEnv G) T15) -> (lookup_evar (evar G T15) I0 T15)
      | lookup_evar_there_evar
          {G : Env} {x8 : (Index tm)}
          (T16 : Ty) (T17 : Ty) :
          (lookup_evar G x8 T16) -> (lookup_evar (evar G T17) (IS x8) T16).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T16 : Ty) (T17 : Ty) ,
        (lookup_evar (evar G T16) I0 T17) -> (T16 = T17)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x8 : (Index tm)} ,
        (forall (T16 : Ty) ,
          (lookup_evar G x8 T16) -> (forall (T17 : Ty) ,
            (lookup_evar G x8 T17) -> (T16 = T17)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x8 : (Index tm)} (T16 : Ty) ,
        (lookup_evar G x8 T16) -> (wfTy (domainEnv G) T16)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x8 : (Index tm)} (T16 : Ty) ,
        (lookup_evar G x8 T16) -> (lookup_evar (appendEnv G G0) (weakenIndextm x8 (domainEnv G0)) (weakenTy T16 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x8 : (Index tm)} (T18 : Ty) ,
        (lookup_evar G x8 T18) -> (wfindex (domainEnv G) x8)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T16 : Ty} :
        (shift_evar C0 G (evar G T16))
    | shiftevar_there_evar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutofftm c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c G G0) -> (shifthvl_tm c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T16 : Ty) (s3 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T16 s3 X0 (evar G T16) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T17 : Ty) :
        (subst_evar G T16 s3 d G0 G1) -> (subst_evar G T16 s3 (XS tm d) (evar G0 T17) (evar G1 T17)).
  Lemma weaken_subst_evar {G : Env} (T16 : Ty) {s3 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T16 s3 d G1 G2) -> (subst_evar G T16 s3 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s3 : Tm} (T16 : Ty) :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T16 s3 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T16 : Ty} (wf : (wfTy (domainEnv G) T16)) ,
    (lookup_evar (appendEnv (evar G T16) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T16 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTm wfTy : infra.
 Hint Constructors wfTm wfTy : wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H18 : (wfTy _ (tunit)) |- _ => inversion H18; subst; clear H18
  | H18 : (wfTy _ (tarr _ _)) |- _ => inversion H18; subst; clear H18
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H18 : (wfTm _ (var _)) |- _ => inversion H18; subst; clear H18
  | H18 : (wfTm _ (tt)) |- _ => inversion H18; subst; clear H18
  | H18 : (wfTm _ (abs _ _)) |- _ => inversion H18; subst; clear H18
  | H18 : (wfTm _ (app _ _)) |- _ => inversion H18; subst; clear H18
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
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x8 : (Index tm)} {T16 : Ty} ,
    (lookup_evar G x8 T16) -> (lookup_evar G0 (shiftIndex c x8) T16)).
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
    | (tarr T15 T16) => (plus 1 (plus (size_Ty T15) (size_Ty T16)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x8) => 1
    | (tt) => 1
    | (abs T15 t9) => (plus 1 (plus (size_Ty T15) (size_Tm t9)))
    | (app t10 t11) => (plus 1 (plus (size_Tm t10) (size_Tm t11)))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (tt) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
  end.
 Hint Rewrite shift_size_Tm : interaction.
 Hint Rewrite shift_size_Tm : shift_size.
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
 Hint Rewrite weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive Typing (G : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index tm))
      (lk : (lookup_evar G x T))
      (H11 : (wfTy (domainEnv G) T))
      (H12 : (wfindex (domainEnv G) x))
      : (Typing G (var x) T)
  | T_Unit :
      (Typing G (tt) (tunit))
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G T1) t (weakenTy T2 (HS tm H0))))
      (H13 : (wfTy (domainEnv G) T1))
      (H14 : (wfTy (domainEnv G) T2))
      :
      (Typing G (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm0 : (Typing G t1 (tarr T11 T12)))
      (jm1 : (Typing G t2 T11)) :
      (Typing G (app t1 t2) T12).
Lemma Typing_cast  :
  (forall (G : Env) (t9 : Tm) (T18 : Ty) (G0 : Env) (t10 : Tm) (T19 : Ty) ,
    (G = G0) -> (t9 = t10) -> (T18 = T19) -> (Typing G t9 T18) -> (Typing G0 t10 T19)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_Typing (G1 : Env) (t13 : Tm) (T25 : Ty) (jm6 : (Typing G1 t13 T25)) :
(forall (c : (Cutoff tm)) (G2 : Env) (H32 : (shift_evar c G1 G2)) ,
  (Typing G2 (shiftTm c t13) T25)) :=
  match jm6 in (Typing _ t13 T25) return (forall (c : (Cutoff tm)) (G2 : Env) (H32 : (shift_evar c G1 G2)) ,
    (Typing G2 (shiftTm c t13) T25)) with
    | (T_Var T20 x9 lk0 H21 H22) => (fun (c : (Cutoff tm)) (G2 : Env) (H32 : (shift_evar c G1 G2)) =>
      (T_Var G2 T20 (shiftIndex c x9) (shift_evar_lookup_evar H32 lk0) (shift_wfTy _ _ H21 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H32))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H32)) _ H22)))
    | (T_Unit) => (fun (c : (Cutoff tm)) (G2 : Env) (H32 : (shift_evar c G1 G2)) =>
      (T_Unit G2))
    | (T_Abs T21 T24 t10 jm3 H23 H24) => (fun (c : (Cutoff tm)) (G2 : Env) (H32 : (shift_evar c G1 G2)) =>
      (T_Abs G2 T21 T24 (shiftTm (CS c) t10) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G1 T21) t10 (weakenTy T24 (HS tm H0)) jm3 (CS c) (evar G2 T21) (weaken_shift_evar (evar empty T21) H32))) (shift_wfTy _ _ H23 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H32))) (shift_wfTy _ _ H24 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H32)))))
    | (T_App T22 T23 t11 t12 jm4 jm5) => (fun (c : (Cutoff tm)) (G2 : Env) (H32 : (shift_evar c G1 G2)) =>
      (T_App G2 T22 T23 (shiftTm c t11) (shiftTm c t12) (shift_evar_Typing G1 t11 (tarr T22 T23) jm4 c G2 (weaken_shift_evar empty H32)) (shift_evar_Typing G1 t12 T22 jm5 c G2 (weaken_shift_evar empty H32))))
  end.
 Hint Resolve shift_evar_Typing : infra.
 Hint Resolve shift_evar_Typing : shift.
Fixpoint weaken_Typing (G : Env) :
(forall (G0 : Env) (t9 : Tm) (T18 : Ty) (jm2 : (Typing G0 t9 T18)) ,
  (Typing (appendEnv G0 G) (weakenTm t9 (domainEnv G)) (weakenTy T18 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (t9 : Tm) (T18 : Ty) (jm2 : (Typing G0 t9 T18)) ,
    (Typing (appendEnv G0 G) (weakenTm t9 (domainEnv G)) (weakenTy T18 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (t9 : Tm) (T18 : Ty) (jm2 : (Typing G0 t9 T18)) =>
      jm2)
    | (evar G T19) => (fun (G0 : Env) (t9 : Tm) (T18 : Ty) (jm2 : (Typing G0 t9 T18)) =>
      (shift_evar_Typing (appendEnv G0 G) (weakenTm t9 (domainEnv G)) (weakenTy T18 (domainEnv G)) (weaken_Typing G G0 t9 T18 jm2) C0 (evar (appendEnv G0 G) T19) shift_evar_here))
  end.
Fixpoint Typing_wf_0 (G : Env) (t10 : Tm) (T20 : Ty) (jm3 : (Typing G t10 T20)) {struct jm3} :
(wfTm (domainEnv G) t10) :=
  match jm3 in (Typing _ t10 T20) return (wfTm (domainEnv G) t10) with
    | (T_Var T x lk0 H11 H12) => (wfTm_var (domainEnv G) _ H12)
    | (T_Unit) => (wfTm_tt (domainEnv G))
    | (T_Abs T1 T2 t jm H13 H14) => (wfTm_abs (domainEnv G) H13 (Typing_wf_0 (evar G T1) t (weakenTy T2 (HS tm H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tarr T11 T12) jm0) (Typing_wf_0 G t2 T11 jm1))
  end
with Typing_wf_1 (G : Env) (t10 : Tm) (T20 : Ty) (jm4 : (Typing G t10 T20)) {struct jm4} :
(wfTy (domainEnv G) T20) :=
  match jm4 in (Typing _ t10 T20) return (wfTy (domainEnv G) T20) with
    | (T_Var T x lk1 H11 H12) => H11
    | (T_Unit) => (wfTy_tunit (domainEnv G))
    | (T_Abs T1 T2 t jm H13 H14) => (wfTy_tarr (domainEnv G) H13 H14)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_tarr_1 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tarr T11 T12) jm0))
  end.
 Hint Extern 8 => match goal with
  | H23 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H23)); pose proof ((Typing_wf_1 _ _ _ H23)); clear H23
end : wf.
Lemma subst_evar_lookup_evar (G1 : Env) (s3 : Tm) (T21 : Ty) (jm5 : (Typing G1 s3 T21)) :
  (forall (d : (Trace tm)) (G2 : Env) (G4 : Env) (sub : (subst_evar G1 T21 s3 d G2 G4)) (x9 : (Index tm)) (T22 : Ty) ,
    (lookup_evar G2 x9 T22) -> (Typing G4 (substIndex d s3 x9) T22)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Fixpoint subst_evar_Typing (G2 : Env) (s3 : Tm) (T21 : Ty) (jm8 : (Typing G2 s3 T21)) (G1 : Env) (t : Tm) (T : Ty) (jm9 : (Typing G1 t T)) :
(forall (G3 : Env) (d : (Trace tm)) (H34 : (subst_evar G2 T21 s3 d G1 G3)) ,
  (Typing G3 (substTm d s3 t) T)) :=
  match jm9 in (Typing _ t T) return (forall (G3 : Env) (d : (Trace tm)) (H34 : (subst_evar G2 T21 s3 d G1 G3)) ,
    (Typing G3 (substTm d s3 t) T)) with
    | (T_Var T22 x9 lk2 H25 H26) => (fun (G3 : Env) (d : (Trace tm)) (H34 : (subst_evar G2 T21 s3 d G1 G3)) =>
      (subst_evar_lookup_evar G2 s3 T21 jm8 d G1 G3 H34 x9 T22 lk2))
    | (T_Unit) => (fun (G3 : Env) (d : (Trace tm)) (H34 : (subst_evar G2 T21 s3 d G1 G3)) =>
      (T_Unit G3))
    | (T_Abs T23 T26 t11 jm5 H27 H28) => (fun (G3 : Env) (d : (Trace tm)) (H34 : (subst_evar G2 T21 s3 d G1 G3)) =>
      (T_Abs G3 T23 T26 (substTm (weakenTrace d (HS tm H0)) s3 t11) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G2 s3 T21 jm8 (evar G1 T23) t11 (weakenTy T26 (HS tm H0)) jm5 (appendEnv G3 (evar empty T23)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T23) H34))) (substhvl_tm_wfTy _ _ H27 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H34))) (substhvl_tm_wfTy _ _ H28 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H34)))))
    | (T_App T24 T25 t12 t13 jm6 jm7) => (fun (G3 : Env) (d : (Trace tm)) (H34 : (subst_evar G2 T21 s3 d G1 G3)) =>
      (T_App G3 T24 T25 (substTm (weakenTrace d H0) s3 t12) (substTm (weakenTrace d H0) s3 t13) (subst_evar_Typing G2 s3 T21 jm8 G1 t12 (tarr T24 T25) jm6 G3 d (weaken_subst_evar _ empty H34)) (subst_evar_Typing G2 s3 T21 jm8 G1 t13 T24 jm7 G3 d (weaken_subst_evar _ empty H34))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenTrace_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.