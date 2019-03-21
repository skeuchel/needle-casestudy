Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.
Section Namespace.
  Inductive Namespace : Type :=
    | tm 
    | ty .
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
        | _ => (weakenIndextm x8 k)
      end
    end.
  Fixpoint weakenIndexty (X12 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X12
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X12 k))
        | _ => (weakenIndexty X12 k)
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x8 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x8 k) k0) = (weakenIndextm x8 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexty_append  :
    (forall (X12 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X12 k) k0) = (weakenIndexty X12 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (t : Tm)
    | tapp (t : Tm) (T : Ty).
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
        | _ => (weakenCutofftm c k)
      end
    end.
  Fixpoint weakenCutoffty (c : (Cutoff ty)) (k : Hvl) {struct k} :
  (Cutoff ty) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (ty) => (CS (weakenCutoffty c k))
        | _ => (weakenCutoffty c k)
      end
    end.
  
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) = (weakenCutofftm c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutoffty_append  :
    (forall (c : (Cutoff ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffty (weakenCutoffty c k) k0) = (weakenCutoffty c (appendHvl k k0)))).
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
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X12 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X12)
      | (CS c) => match X12 with
        | (I0) => I0
        | (IS X12) => (IS (tshiftIndex c X12))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (tvar X12) => (tvar (tshiftIndex c X12))
      | (tarr T23 T24) => (tarr (tshiftTy c T23) (tshiftTy c T24))
      | (tall T25) => (tall (tshiftTy (CS c) T25))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x8) => (var (shiftIndex c x8))
      | (abs T23 t15) => (abs T23 (shiftTm (CS c) t15))
      | (app t16 t17) => (app (shiftTm c t16) (shiftTm c t17))
      | (tabs t18) => (tabs (shiftTm c t18))
      | (tapp t19 T24) => (tapp (shiftTm c t19) T24)
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x8) => (var x8)
      | (abs T23 t15) => (abs (tshiftTy c T23) (tshiftTm c t15))
      | (app t16 t17) => (app (tshiftTm c t16) (tshiftTm c t17))
      | (tabs t18) => (tabs (tshiftTm (CS c) t18))
      | (tapp t19 T24) => (tapp (tshiftTm c t19) (tshiftTy c T24))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S0 k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS tm k) => (shiftTm C0 (weakenTm s k))
      | (HS ty k) => (tshiftTm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T23 : (Trace a)).
  
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
      | (XS ty d) => (tshiftTm C0 (substIndex d s x8))
    end.
  Fixpoint tsubstIndex (d : (Trace ty)) (S0 : Ty) (X12 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X12 with
        | (I0) => S0
        | (IS X12) => (tvar X12)
      end
      | (XS tm d) => (tsubstIndex d S0 X12)
      | (XS ty d) => match X12 with
        | (I0) => (tvar I0)
        | (IS X12) => (tshiftTy C0 (tsubstIndex d S0 X12))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (tvar X12) => (tsubstIndex d S0 X12)
      | (tarr T23 T24) => (tarr (tsubstTy d S0 T23) (tsubstTy d S0 T24))
      | (tall T25) => (tall (tsubstTy (weakenTrace d (HS ty H0)) S0 T25))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x8) => (substIndex d s x8)
      | (abs T23 t15) => (abs T23 (substTm (weakenTrace d (HS tm H0)) s t15))
      | (app t16 t17) => (app (substTm d s t16) (substTm d s t17))
      | (tabs t18) => (tabs (substTm (weakenTrace d (HS ty H0)) s t18))
      | (tapp t19 T24) => (tapp (substTm d s t19) T24)
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x8) => (var x8)
      | (abs T23 t15) => (abs (tsubstTy d S0 T23) (tsubstTm (weakenTrace d (HS tm H0)) S0 t15))
      | (app t16 t17) => (app (tsubstTm d S0 t16) (tsubstTm d S0 t17))
      | (tabs t18) => (tabs (tsubstTm (weakenTrace d (HS ty H0)) S0 t18))
      | (tapp t19 T24) => (tapp (tsubstTm d S0 t19) (tsubstTy d S0 T24))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x8 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x8)) = (var x8))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S0 : Ty) :
    (forall (k : Hvl) (X12 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S0 (tshiftIndex (weakenCutoffty C0 k) X12)) = (tvar X12))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S1 : Ty) (k : Hvl) (S0 : Ty) {struct S1} :
  ((tsubstTy (weakenTrace X0 k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = S1) :=
    match S1 return ((tsubstTy (weakenTrace X0 k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = S1) with
      | (tvar X12) => (tsubstIndex0_tshiftIndex0_reflection_ind S0 k X12)
      | (tarr T24 T25) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T24 k S0) (tsubst0_tshift0_Ty_reflection_ind T25 k S0))
      | (tall T23) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T23 (HS ty k) S0)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x8) => (substIndex0_shiftIndex0_reflection_ind s k x8)
      | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t15 (HS tm k) s)))
      | (app t16 t17) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t16 k s) (subst0_shift0_Tm_reflection_ind t17 k s))
      | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t15 (HS ty k) s)))
      | (tapp t15 T23) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t15 k s) eq_refl)
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S0 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x8) => eq_refl
      | (abs T23 t15) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T23 k S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t15 (HS tm k) S0)))
      | (app t16 t17) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t16 k S0) (tsubst0_tshift0_Tm_reflection_ind t17 k S0))
      | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t15 (HS ty k) S0)))
      | (tapp t15 T23) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t15 k S0) (tsubst0_tshift0_Ty_reflection_ind T23 k S0))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S1 : Ty) : (forall (S0 : Ty) ,
    ((tsubstTy X0 S0 (tshiftTy C0 S1)) = S1)) := (tsubst0_tshift0_Ty_reflection_ind S1 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S0 : Ty) ,
    ((tsubstTm X0 S0 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x8 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x8)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x8)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff ty)) (X12 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c) k) (tshiftIndex (weakenCutoffty C0 k) X12)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c k) X12)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff ty)) {struct S0} :
    ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S0)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S0))) :=
      match S0 return ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S0)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S0))) with
        | (tvar X12) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c X12))
        | (tarr T24 T25) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T24 k c) (tshift_tshift0_Ty_comm_ind T25 k c))
        | (tall T23) => (f_equal tall (tshift_tshift0_Ty_comm_ind T23 (HS ty k) c))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x8) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x8))
        | (abs T23 t15) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t15 (HS tm k) c))
        | (app t16 t17) => (f_equal2 app (shift_shift0_Tm_comm_ind t16 k c) (shift_shift0_Tm_comm_ind t17 k c))
        | (tabs t15) => (f_equal tabs (shift_shift0_Tm_comm_ind t15 (HS ty k) c))
        | (tapp t15 T23) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t15 k c) eq_refl)
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t15 (HS tm k) c))
        | (app t16 t17) => (f_equal2 app (shift_tshift0_Tm_comm_ind t16 k c) (shift_tshift0_Tm_comm_ind t17 k c))
        | (tabs t15) => (f_equal tabs (shift_tshift0_Tm_comm_ind t15 (HS ty k) c))
        | (tapp t15 T23) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t15 k c) eq_refl)
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t15 (HS tm k) c))
        | (app t16 t17) => (f_equal2 app (tshift_shift0_Tm_comm_ind t16 k c) (tshift_shift0_Tm_comm_ind t17 k c))
        | (tabs t15) => (f_equal tabs (tshift_shift0_Tm_comm_ind t15 (HS ty k) c))
        | (tapp t15 T23) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t15 k c) eq_refl)
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T23 k c) (tshift_tshift0_Tm_comm_ind t15 (HS tm k) c))
        | (app t16 t17) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t16 k c) (tshift_tshift0_Tm_comm_ind t17 k c))
        | (tabs t15) => (f_equal tabs (tshift_tshift0_Tm_comm_ind t15 (HS ty k) c))
        | (tapp t15 T23) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t15 k c) (tshift_tshift0_Ty_comm_ind T23 k c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff ty)) ,
      ((tshiftTy (CS c) (tshiftTy C0 S0)) = (tshiftTy C0 (tshiftTy c S0)))) := (tshift_tshift0_Ty_comm_ind S0 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff tm)) ,
      ((shiftTm (CS c) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c : (Cutoff tm)) ,
      ((shiftTm c (tshiftTm C0 s)) = (tshiftTm C0 (shiftTm c s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff ty)) ,
      ((tshiftTm c (shiftTm C0 s)) = (shiftTm C0 (tshiftTm c s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c : (Cutoff ty)) ,
      ((tshiftTm (CS c) (tshiftTm C0 s)) = (tshiftTm C0 (tshiftTm c s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c : (Cutoff ty)) (S0 : Ty) ,
      ((weakenTy (tshiftTy c S0) k) = (tshiftTy (weakenCutoffty c k) (weakenTy S0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c : (Cutoff tm)) (s : Tm) ,
      ((weakenTm (shiftTm c s) k) = (shiftTm (weakenCutofftm c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c : (Cutoff ty)) (s : Tm) ,
      ((weakenTm (tshiftTm c s) k) = (tshiftTm (weakenCutoffty c k) (weakenTm s k)))).
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
    Lemma tshiftTm_substIndex0_comm_ind (c : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c k) (substIndex (weakenTrace X0 k) s x8)) = (substIndex (weakenTrace X0 k) (tshiftTm c s) x8))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c : (Cutoff ty)) (S0 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c k) (tsubstIndex (weakenTrace X0 k) S0 X12)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c S0) (tshiftIndex (weakenCutoffty (CS c) k) X12)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c : (Cutoff ty)) (S0 : Ty) {struct S1} :
    ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S0 S1)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S0) (tshiftTy (weakenCutoffty (CS c) k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S0 S1)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S0) (tshiftTy (weakenCutoffty (CS c) k) S1))) with
        | (tvar X12) => (tshiftTy_tsubstIndex0_comm_ind c S0 k X12)
        | (tarr T24 T25) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T24 k c S0) (tshift_tsubst0_Ty_comm_ind T25 k c S0))
        | (tall T23) => (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T23 (HS ty k) c S0) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x8) => (shiftTm_substIndex0_comm_ind c s k x8)
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t15 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t16 t17) => (f_equal2 app (shift_subst0_Tm_comm_ind t16 k c s) (shift_subst0_Tm_comm_ind t17 k c s))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t15 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t15 T23) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t15 k c s) eq_refl)
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) (S0 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) S0 (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) S0 (shiftTm (weakenCutofftm c k) s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t15 (HS tm k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t16 t17) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t16 k c S0) (shift_tsubst0_Tm_comm_ind t17 k c S0))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t15 (HS ty k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t15 T23) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t15 k c S0) eq_refl)
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) with
        | (var x8) => (tshiftTm_substIndex0_comm_ind c s k x8)
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t15 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t16 t17) => (f_equal2 app (tshift_subst0_Tm_comm_ind t16 k c s) (tshift_subst0_Tm_comm_ind t17 k c s))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t15 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t15 T23) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t15 k c s) eq_refl)
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) (S0 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S0) (tshiftTm (weakenCutoffty (CS c) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S0) (tshiftTm (weakenCutoffty (CS c) k) s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T23 k c S0) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t15 (HS tm k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t16 t17) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t16 k c S0) (tshift_tsubst0_Tm_comm_ind t17 k c S0))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t15 (HS ty k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t15 T23) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t15 k c S0) (tshift_tsubst0_Ty_comm_ind T23 k c S0))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S1 : Ty) : (forall (c : (Cutoff ty)) (S0 : Ty) ,
      ((tshiftTy c (tsubstTy X0 S0 S1)) = (tsubstTy X0 (tshiftTy c S0) (tshiftTy (CS c) S1)))) := (tshift_tsubst0_Ty_comm_ind S1 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c (substTm X0 s s0)) = (substTm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff tm)) (S0 : Ty) ,
      ((shiftTm c (tsubstTm X0 S0 s)) = (tsubstTm X0 S0 (shiftTm c s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c (substTm X0 s s0)) = (substTm X0 (tshiftTm c s) (tshiftTm c s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff ty)) (S0 : Ty) ,
      ((tshiftTm c (tsubstTm X0 S0 s)) = (tsubstTm X0 (tshiftTy c S0) (tshiftTm (CS c) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k) s (shiftIndex (weakenCutofftm C0 k) x8)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d k) s x8)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d) k) s x8) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d k) s x8)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d : (Trace ty)) (S0 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k) S0 X12) = (tsubstIndex (weakenTrace d k) S0 X12))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S0 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k) S0 (tshiftIndex (weakenCutoffty C0 k) X12)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d k) S0 X12)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct S1} :
    ((tsubstTy (weakenTrace (XS ty d) k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S0 S1))) :=
      match S1 return ((tsubstTy (weakenTrace (XS ty d) k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S0 S1))) with
        | (tvar X12) => (tsubstIndex_tshiftTy0_comm_ind d S0 k X12)
        | (tarr T24 T25) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T24 k d S0) (tsubst_tshift0_Ty_comm_ind T25 k d S0))
        | (tall T23) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T23 (HS ty k) d S0) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x8) => (substIndex_shiftTm0_comm_ind d s k x8)
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t15 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (subst_shift0_Tm_comm_ind t16 k d s) (subst_shift0_Tm_comm_ind t17 k d s))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t15 (HS ty k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t15 k d s) eq_refl)
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x8) => (substIndex_tshiftTm0_comm_ind d s k x8)
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t15 (HS tm k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (subst_tshift0_Tm_comm_ind t16 k d s) (subst_tshift0_Tm_comm_ind t17 k d s))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t15 (HS ty k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t15 k d s) eq_refl)
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S0 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S0 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S0 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S0 s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t15 (HS tm k) d S0) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t16 k d S0) (tsubst_shift0_Tm_comm_ind t17 k d S0))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t15 (HS ty k) d S0) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t15 k d S0) eq_refl)
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d) k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S0 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d) k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S0 s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T23 k d S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t15 (HS tm k) d S0) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t16 k d S0) (tsubst_tshift0_Tm_comm_ind t17 k d S0))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t15 (HS ty k) d S0) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t15 k d S0) (tsubst_tshift0_Ty_comm_ind T23 k d S0))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S1 : Ty) : (forall (d : (Trace ty)) (S0 : Ty) ,
      ((tsubstTy (XS ty d) S0 (tshiftTy C0 S1)) = (tshiftTy C0 (tsubstTy d S0 S1)))) := (tsubst_tshift0_Ty_comm_ind S1 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S0 : Ty) ,
      ((tsubstTm d S0 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d S0 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S0 : Ty) ,
      ((tsubstTm (XS ty d) S0 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d S0 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S1 : Ty) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct S1} :
    ((tsubstTy (weakenTrace (XS tm d) k) S0 S1) = (tsubstTy (weakenTrace d k) S0 S1)) :=
      match S1 return ((tsubstTy (weakenTrace (XS tm d) k) S0 S1) = (tsubstTy (weakenTrace d k) S0 S1)) with
        | (tvar X12) => (tsubstIndex_shiftTy0_comm_ind d S0 k X12)
        | (tarr T24 T25) => (f_equal2 tarr (tsubst_tm_Ty_ind T24 k d S0) (tsubst_tm_Ty_ind T25 k d S0))
        | (tall T23) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T23 (HS ty k) d S0) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d) k) S0 s) = (tsubstTm (weakenTrace d k) S0 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d) k) S0 s) = (tsubstTm (weakenTrace d k) S0 s)) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs (tsubst_tm_Ty_ind T23 k d S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t15 (HS tm k) d S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl))))
        | (app t16 t17) => (f_equal2 app (tsubst_tm_Tm_ind t16 k d S0) (tsubst_tm_Tm_ind t17 k d S0))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t15 (HS ty k) d S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t15 T23) => (f_equal2 tapp (tsubst_tm_Tm_ind t15 k d S0) (tsubst_tm_Ty_ind T23 k d S0))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S1 : Ty) : (forall (d : (Trace ty)) (S0 : Ty) ,
      ((tsubstTy (XS tm d) S0 S1) = (tsubstTy d S0 S1))) := (tsubst_tm_Ty_ind S1 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d : (Trace ty)) (S0 : Ty) ,
      ((tsubstTm (XS tm d) S0 s) = (tsubstTm d S0 s))) := (tsubst_tm_Tm_ind s H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d : (Trace tm)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((substTm (weakenTrace d k) s (substIndex (weakenTrace X0 k) s0 x8)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substIndex (weakenTrace (XS tm d) k) s x8)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d : (Trace ty)) (S0 : Ty) (s : Tm) :
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((tsubstTm (weakenTrace d k) S0 (substIndex (weakenTrace X0 k) s x8)) = (substIndex (weakenTrace X0 k) (tsubstTm d S0 s) x8))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d : (Trace ty)) (S0 : Ty) (S1 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstTy (weakenTrace d k) S0 (tsubstIndex (weakenTrace X0 k) S1 X12)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstIndex (weakenTrace (XS ty d) k) S0 X12)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d : (Trace tm)) (s : Tm) (S0 : Ty) :
      (forall (k : Hvl) (x8 : (Index tm)) ,
        ((substIndex (weakenTrace d k) s x8) = (tsubstTm (weakenTrace X0 k) S0 (substIndex (weakenTrace (XS ty d) k) s x8)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace d k) S0 (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTy (weakenTrace (XS ty d) k) S0 S2))) :=
      match S2 return ((tsubstTy (weakenTrace d k) S0 (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTy (weakenTrace (XS ty d) k) S0 S2))) with
        | (tvar X12) => (tsubstTy_tsubstIndex0_commright_ind d S0 S1 k X12)
        | (tarr T24 T25) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T24 k d S0 S1) (tsubst_tsubst0_Ty_comm_ind T25 k d S0 S1))
        | (tall T23) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T23 (HS ty k) d S0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x8) => (substTm_substIndex0_commright_ind d s s0 k x8)
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t15 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (subst_subst0_Tm_comm_ind t16 k d s s0) (subst_subst0_Tm_comm_ind t17 k d s s0))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t15 (HS ty k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t15 k d s s0) eq_refl)
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (S0 : Ty) {struct s0} :
    ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S0 s0)) = (tsubstTm (weakenTrace X0 k) S0 (substTm (weakenTrace (XS ty d) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S0 s0)) = (tsubstTm (weakenTrace X0 k) S0 (substTm (weakenTrace (XS ty d) k) s s0))) with
        | (var x8) => (substTy_tsubstIndex0_commleft_ind d s S0 k x8)
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t15 (HS tm k) d s S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t16 k d s S0) (subst_tsubst0_Tm_comm_ind t17 k d s S0))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t15 (HS ty k) d s S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t15 k d s S0) eq_refl)
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d k) S0 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S0 s) (tsubstTm (weakenTrace d k) S0 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d k) S0 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S0 s) (tsubstTm (weakenTrace d k) S0 s0))) with
        | (var x8) => (tsubstTm_substIndex0_commright_ind d S0 s k x8)
        | (abs T23 t15) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t15 (HS tm k) d S0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t16 k d S0 s) (tsubst_subst0_Tm_comm_ind t17 k d S0 s))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t15 (HS ty k) d S0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t15 k d S0 s) eq_refl)
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S0 (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTm (weakenTrace (XS ty d) k) S0 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S0 (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTm (weakenTrace (XS ty d) k) S0 s))) with
        | (var x8) => eq_refl
        | (abs T23 t15) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T23 k d S0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t15 (HS tm k) d S0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t16 t17) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t16 k d S0 S1) (tsubst_tsubst0_Tm_comm_ind t17 k d S0 S1))
        | (tabs t15) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t15 (HS ty k) d S0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t15 T23) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t15 k d S0 S1) (tsubst_tsubst0_Ty_comm_ind T23 k d S0 S1))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S2 : Ty) : (forall (d : (Trace ty)) (S0 : Ty) (S1 : Ty) ,
      ((tsubstTy d S0 (tsubstTy X0 S1 S2)) = (tsubstTy X0 (tsubstTy d S0 S1) (tsubstTy (XS ty d) S0 S2)))) := (tsubst_tsubst0_Ty_comm_ind S2 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d s (substTm X0 s0 s1)) = (substTm X0 (substTm d s s0) (substTm (XS tm d) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) (S0 : Ty) ,
      ((substTm d s (tsubstTm X0 S0 s0)) = (tsubstTm X0 S0 (substTm (XS ty d) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d : (Trace ty)) (S0 : Ty) (s : Tm) ,
      ((tsubstTm d S0 (substTm X0 s s0)) = (substTm X0 (tsubstTm d S0 s) (tsubstTm d S0 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S0 : Ty) (S1 : Ty) ,
      ((tsubstTm d S0 (tsubstTm X0 S1 s)) = (tsubstTm X0 (tsubstTy d S0 S1) (tsubstTm (XS ty d) S0 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d : (Trace ty)) (S0 : Ty) (S1 : Ty) ,
        ((weakenTy (tsubstTy d S0 S1) k) = (tsubstTy (weakenTrace d k) S0 (weakenTy S1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d s s0) k) = (substTm (weakenTrace d k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d : (Trace ty)) (S0 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d S0 s) k) = (tsubstTm (weakenTrace d k) S0 (weakenTm s k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
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
    | wfTy_tvar (X12 : (Index ty))
        (wfi : (wfindex k X12)) :
        (wfTy k (tvar X12))
    | wfTy_tarr {T23 : Ty}
        (wf : (wfTy k T23)) {T24 : Ty}
        (wf0 : (wfTy k T24)) :
        (wfTy k (tarr T23 T24))
    | wfTy_tall {T25 : Ty}
        (wf : (wfTy (HS ty k) T25)) :
        (wfTy k (tall T25)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x8 : (Index tm))
        (wfi : (wfindex k x8)) :
        (wfTm k (var x8))
    | wfTm_abs {T23 : Ty}
        (wf : (wfTy k T23)) {t15 : Tm}
        (wf0 : (wfTm (HS tm k) t15)) :
        (wfTm k (abs T23 t15))
    | wfTm_app {t16 : Tm}
        (wf : (wfTm k t16)) {t17 : Tm}
        (wf0 : (wfTm k t17)) :
        (wfTm k (app t16 t17))
    | wfTm_tabs {t18 : Tm}
        (wf : (wfTm (HS ty k) t18)) :
        (wfTm k (tabs t18))
    | wfTm_tapp {t19 : Tm}
        (wf : (wfTm k t19)) {T24 : Ty}
        (wf0 : (wfTy k T24)) :
        (wfTm k (tapp t19 T24)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H14 : (wfTy k (tvar X))) : (wfindex k X) := match H14 in (wfTy _ S0) return match S0 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H15 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T1) := match H15 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H15 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T2) := match H15 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k1 : Hvl) (T : Ty) (H16 : (wfTy k1 (tall T))) : (wfTy (HS ty k1) T) := match H16 in (wfTy _ S2) return match S2 return Prop with
    | (tall T) => (wfTy (HS ty k1) T)
    | _ => True
  end with
    | (wfTy_tall T H4) => H4
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k2 : Hvl) (x : (Index tm)) (H17 : (wfTm k2 (var x))) : (wfindex k2 x) := match H17 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k2 x)
    | _ => True
  end with
    | (wfTm_var x H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k3 : Hvl) (T : Ty) (t : Tm) (H18 : (wfTm k3 (abs T t))) : (wfTy k3 T) := match H18 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k3 T)
    | _ => True
  end with
    | (wfTm_abs T H6 t H7) => H6
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k3 : Hvl) (T : Ty) (t : Tm) (H18 : (wfTm k3 (abs T t))) : (wfTm (HS tm k3) t) := match H18 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k3) t)
    | _ => True
  end with
    | (wfTm_abs T H6 t H7) => H7
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k4 : Hvl) (t1 : Tm) (t2 : Tm) (H19 : (wfTm k4 (app t1 t2))) : (wfTm k4 t1) := match H19 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k4 t1)
    | _ => True
  end with
    | (wfTm_app t1 H8 t2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k4 : Hvl) (t1 : Tm) (t2 : Tm) (H19 : (wfTm k4 (app t1 t2))) : (wfTm k4 t2) := match H19 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k4 t2)
    | _ => True
  end with
    | (wfTm_app t1 H8 t2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k5 : Hvl) (t : Tm) (H20 : (wfTm k5 (tabs t))) : (wfTm (HS ty k5) t) := match H20 in (wfTm _ s2) return match s2 return Prop with
    | (tabs t) => (wfTm (HS ty k5) t)
    | _ => True
  end with
    | (wfTm_tabs t H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k6 : Hvl) (t : Tm) (T : Ty) (H21 : (wfTm k6 (tapp t T))) : (wfTm k6 t) := match H21 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k6 t)
    | _ => True
  end with
    | (wfTm_tapp t H11 T H12) => H11
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k6 : Hvl) (t : Tm) (T : Ty) (H21 : (wfTm k6 (tapp t T))) : (wfTy k6 T) := match H21 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k6 T)
    | _ => True
  end with
    | (wfTm_tapp t H11 T H12) => H12
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c : (Cutoff tm)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k7 : Hvl)
        : (shifthvl_tm C0 k7 (HS tm k7))
    | shifthvl_tm_there_tm
        (c : (Cutoff tm)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_tm c k7 k8) -> (shifthvl_tm (CS c) (HS tm k7) (HS tm k8))
    | shifthvl_tm_there_ty
        (c : (Cutoff tm)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_tm c k7 k8) -> (shifthvl_tm c (HS ty k7) (HS ty k8)).
  Inductive shifthvl_ty : (forall (c : (Cutoff ty)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k7 : Hvl)
        : (shifthvl_ty C0 k7 (HS ty k7))
    | shifthvl_ty_there_tm
        (c : (Cutoff ty)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_ty c k7 k8) -> (shifthvl_ty c (HS tm k7) (HS tm k8))
    | shifthvl_ty_there_ty
        (c : (Cutoff ty)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_ty c k7 k8) -> (shifthvl_ty (CS c) (HS ty k7) (HS ty k8)).
  Lemma weaken_shifthvl_tm  :
    (forall (k7 : Hvl) {c : (Cutoff tm)} {k8 : Hvl} {k9 : Hvl} ,
      (shifthvl_tm c k8 k9) -> (shifthvl_tm (weakenCutofftm c k7) (appendHvl k8 k7) (appendHvl k9 k7))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k7 : Hvl) {c : (Cutoff ty)} {k8 : Hvl} {k9 : Hvl} ,
      (shifthvl_ty c k8 k9) -> (shifthvl_ty (weakenCutoffty c k7) (appendHvl k8 k7) (appendHvl k9 k7))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) (x8 : (Index tm)) ,
      (wfindex k7 x8) -> (wfindex k8 (shiftIndex c x8))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c : (Cutoff tm)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) (X12 : (Index ty)) ,
      (wfindex k7 X12) -> (wfindex k8 X12)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c : (Cutoff ty)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) (x8 : (Index tm)) ,
      (wfindex k7 x8) -> (wfindex k8 x8)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c : (Cutoff ty)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) (X12 : (Index ty)) ,
      (wfindex k7 X12) -> (wfindex k8 (tshiftIndex c X12))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k7 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k7 S3)) ,
      (forall (c : (Cutoff tm)) (k8 : Hvl) ,
        (shifthvl_tm c k7 k8) -> (wfTy k8 S3)))) := (ind_wfTy (fun (k7 : Hvl) (S3 : Ty) (wf : (wfTy k7 S3)) =>
    (forall (c : (Cutoff tm)) (k8 : Hvl) ,
      (shifthvl_tm c k7 k8) -> (wfTy k8 S3))) (fun (k7 : Hvl) (X12 : (Index ty)) (wfi : (wfindex k7 X12)) (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTy_tvar k8 _ (shift_wfindex_ty c k7 k8 ins X12 wfi))) (fun (k7 : Hvl) (T1 : Ty) (wf : (wfTy k7 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k7 T2)) IHT2 (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTy_tarr k8 (IHT1 c k8 (weaken_shifthvl_tm H0 ins)) (IHT2 c k8 (weaken_shifthvl_tm H0 ins)))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy (HS ty k7) T)) IHT (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTy_tall k8 (IHT c (HS ty k8) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k7 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k7 S3)) ,
      (forall (c : (Cutoff ty)) (k8 : Hvl) ,
        (shifthvl_ty c k7 k8) -> (wfTy k8 (tshiftTy c S3))))) := (ind_wfTy (fun (k7 : Hvl) (S3 : Ty) (wf : (wfTy k7 S3)) =>
    (forall (c : (Cutoff ty)) (k8 : Hvl) ,
      (shifthvl_ty c k7 k8) -> (wfTy k8 (tshiftTy c S3)))) (fun (k7 : Hvl) (X12 : (Index ty)) (wfi : (wfindex k7 X12)) (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTy_tvar k8 _ (tshift_wfindex_ty c k7 k8 ins X12 wfi))) (fun (k7 : Hvl) (T1 : Ty) (wf : (wfTy k7 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k7 T2)) IHT2 (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTy_tarr k8 (IHT1 c k8 (weaken_shifthvl_ty H0 ins)) (IHT2 c k8 (weaken_shifthvl_ty H0 ins)))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy (HS ty k7) T)) IHT (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTy_tall k8 (IHT (CS c) (HS ty k8) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k7 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k7 s4)) ,
      (forall (c : (Cutoff tm)) (k8 : Hvl) ,
        (shifthvl_tm c k7 k8) -> (wfTm k8 (shiftTm c s4))))) := (ind_wfTm (fun (k7 : Hvl) (s4 : Tm) (wf : (wfTm k7 s4)) =>
    (forall (c : (Cutoff tm)) (k8 : Hvl) ,
      (shifthvl_tm c k7 k8) -> (wfTm k8 (shiftTm c s4)))) (fun (k7 : Hvl) (x8 : (Index tm)) (wfi : (wfindex k7 x8)) (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTm_var k8 _ (shift_wfindex_tm c k7 k8 ins x8 wfi))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) (t : Tm) (wf0 : (wfTm (HS tm k7) t)) IHt (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTm_abs k8 (shift_wfTy k7 T wf c k8 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k8) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k7 : Hvl) (t1 : Tm) (wf : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k7 t2)) IHt2 (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTm_app k8 (IHt1 c k8 (weaken_shifthvl_tm H0 ins)) (IHt2 c k8 (weaken_shifthvl_tm H0 ins)))) (fun (k7 : Hvl) (t : Tm) (wf : (wfTm (HS ty k7) t)) IHt (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTm_tabs k8 (IHt c (HS ty k8) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k7 : Hvl) (t : Tm) (wf : (wfTm k7 t)) IHt (T : Ty) (wf0 : (wfTy k7 T)) (c : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c k7 k8)) =>
    (wfTm_tapp k8 (IHt c k8 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k7 T wf0 c k8 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k7 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k7 s4)) ,
      (forall (c : (Cutoff ty)) (k8 : Hvl) ,
        (shifthvl_ty c k7 k8) -> (wfTm k8 (tshiftTm c s4))))) := (ind_wfTm (fun (k7 : Hvl) (s4 : Tm) (wf : (wfTm k7 s4)) =>
    (forall (c : (Cutoff ty)) (k8 : Hvl) ,
      (shifthvl_ty c k7 k8) -> (wfTm k8 (tshiftTm c s4)))) (fun (k7 : Hvl) (x8 : (Index tm)) (wfi : (wfindex k7 x8)) (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTm_var k8 _ (tshift_wfindex_tm c k7 k8 ins x8 wfi))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) (t : Tm) (wf0 : (wfTm (HS tm k7) t)) IHt (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTm_abs k8 (tshift_wfTy k7 T wf c k8 (weaken_shifthvl_ty H0 ins)) (IHt c (HS tm k8) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k7 : Hvl) (t1 : Tm) (wf : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k7 t2)) IHt2 (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTm_app k8 (IHt1 c k8 (weaken_shifthvl_ty H0 ins)) (IHt2 c k8 (weaken_shifthvl_ty H0 ins)))) (fun (k7 : Hvl) (t : Tm) (wf : (wfTm (HS ty k7) t)) IHt (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTm_tabs k8 (IHt (CS c) (HS ty k8) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k7 : Hvl) (t : Tm) (wf : (wfTm k7 t)) IHt (T : Ty) (wf0 : (wfTy k7 T)) (c : (Cutoff ty)) (k8 : Hvl) (ins : (shifthvl_ty c k7 k8)) =>
    (wfTm_tapp k8 (IHt c k8 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k7 T wf0 c k8 (weaken_shifthvl_ty H0 ins))))).
  Fixpoint weaken_wfTy (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) ,
    (wfTy (appendHvl k8 k7) (weakenTy S3 k7))) :=
    match k7 return (forall (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) ,
      (wfTy (appendHvl k8 k7) (weakenTy S3 k7))) with
      | (H0) => (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
        wf)
      | (HS tm k7) => (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
        (shift_wfTy (appendHvl k8 k7) (weakenTy S3 k7) (weaken_wfTy k7 k8 S3 wf) C0 (HS tm (appendHvl k8 k7)) (shifthvl_tm_here (appendHvl k8 k7))))
      | (HS ty k7) => (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
        (tshift_wfTy (appendHvl k8 k7) (weakenTy S3 k7) (weaken_wfTy k7 k8 S3 wf) C0 (HS ty (appendHvl k8 k7)) (shifthvl_ty_here (appendHvl k8 k7))))
    end.
  Fixpoint weaken_wfTm (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) ,
    (wfTm (appendHvl k8 k7) (weakenTm s4 k7))) :=
    match k7 return (forall (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) ,
      (wfTm (appendHvl k8 k7) (weakenTm s4 k7))) with
      | (H0) => (fun (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) =>
        wf)
      | (HS tm k7) => (fun (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) =>
        (shift_wfTm (appendHvl k8 k7) (weakenTm s4 k7) (weaken_wfTm k7 k8 s4 wf) C0 (HS tm (appendHvl k8 k7)) (shifthvl_tm_here (appendHvl k8 k7))))
      | (HS ty k7) => (fun (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) =>
        (tshift_wfTm (appendHvl k8 k7) (weakenTm s4 k7) (weaken_wfTm k7 k8 s4 wf) C0 (HS ty (appendHvl k8 k7)) (shifthvl_ty_here (appendHvl k8 k7))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k7 : Hvl) (S3 : Ty) (k8 : Hvl) (S4 : Ty) ,
    (k7 = k8) -> (S3 = S4) -> (wfTy k7 S3) -> (wfTy k8 S4)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k7 : Hvl) (s4 : Tm) (k8 : Hvl) (s5 : Tm) ,
    (k7 = k8) -> (s4 = s5) -> (wfTm k7 s4) -> (wfTm k8 s5)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : wf.
 Hint Constructors shifthvl_tm shifthvl_ty : infra.
 Hint Constructors shifthvl_tm shifthvl_ty : shift.
 Hint Constructors shifthvl_tm shifthvl_ty : shift_wf.
 Hint Constructors shifthvl_tm shifthvl_ty : wf.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : infra.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : shift.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : shift_wf.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : weaken.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : wf.
Section SubstWellFormed.
  Inductive substhvl_tm (k7 : Hvl) : (forall (d : (Trace tm)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k7 X0 (HS tm k7) k7)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_tm k7 d k8 k9) -> (substhvl_tm k7 (XS tm d) (HS tm k8) (HS tm k9))
    | substhvl_tm_there_ty
        {d : (Trace tm)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_tm k7 d k8 k9) -> (substhvl_tm k7 (XS ty d) (HS ty k8) (HS ty k9)).
  Inductive substhvl_ty (k7 : Hvl) : (forall (d : (Trace ty)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k7 X0 (HS ty k7) k7)
    | substhvl_ty_there_tm
        {d : (Trace ty)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_ty k7 d k8 k9) -> (substhvl_ty k7 (XS tm d) (HS tm k8) (HS tm k9))
    | substhvl_ty_there_ty
        {d : (Trace ty)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_ty k7 d k8 k9) -> (substhvl_ty k7 (XS ty d) (HS ty k8) (HS ty k9)).
  Lemma weaken_substhvl_tm  :
    (forall {k8 : Hvl} (k7 : Hvl) {d : (Trace tm)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (substhvl_tm k8 (weakenTrace d k7) (appendHvl k9 k7) (appendHvl k10 k7))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k8 : Hvl} (k7 : Hvl) {d : (Trace ty)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (substhvl_ty k8 (weakenTrace d k7) (appendHvl k9 k7) (appendHvl k10 k7))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k7 : Hvl} {s4 : Tm} (wft : (wfTm k7 s4)) :
    (forall {d : (Trace tm)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_tm k7 d k8 k9) -> (forall {x8 : (Index tm)} ,
        (wfindex k8 x8) -> (wfTm k9 (substIndex d s4 x8)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k7 : Hvl} {S3 : Ty} (wft : (wfTy k7 S3)) :
    (forall {d : (Trace ty)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_ty k7 d k8 k9) -> (forall {X12 : (Index ty)} ,
        (wfindex k8 X12) -> (wfTy k9 (tsubstIndex d S3 X12)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k7 : Hvl} :
    (forall {d : (Trace tm)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_tm k7 d k8 k9) -> (forall {X12 : (Index ty)} ,
        (wfindex k8 X12) -> (wfindex k9 X12))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k7 : Hvl} :
    (forall {d : (Trace ty)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_ty k7 d k8 k9) -> (forall {x8 : (Index tm)} ,
        (wfindex k8 x8) -> (wfindex k9 x8))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k7 : Hvl} : (forall (k8 : Hvl) ,
    (forall (S3 : Ty) (wf0 : (wfTy k8 S3)) ,
      (forall {d : (Trace tm)} {k9 : Hvl} ,
        (substhvl_tm k7 d k8 k9) -> (wfTy k9 S3)))) := (ind_wfTy (fun (k8 : Hvl) (S3 : Ty) (wf0 : (wfTy k8 S3)) =>
    (forall {d : (Trace tm)} {k9 : Hvl} ,
      (substhvl_tm k7 d k8 k9) -> (wfTy k9 S3))) (fun (k8 : Hvl) {X12 : (Index ty)} (wfi : (wfindex k8 X12)) {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (wfTy_tvar k9 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k8 : Hvl) (T1 : Ty) (wf0 : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k8 T2)) IHT2 {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (wfTy_tarr k9 (IHT1 (weakenTrace d H0) k9 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k9 (weaken_substhvl_tm H0 del)))) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k8) T)) IHT {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (wfTy_tall k9 (IHT (weakenTrace d (HS ty H0)) (HS ty k9) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k7 : Hvl} {S3 : Ty} (wf : (wfTy k7 S3)) : (forall (k8 : Hvl) ,
    (forall (S4 : Ty) (wf0 : (wfTy k8 S4)) ,
      (forall {d : (Trace ty)} {k9 : Hvl} ,
        (substhvl_ty k7 d k8 k9) -> (wfTy k9 (tsubstTy d S3 S4))))) := (ind_wfTy (fun (k8 : Hvl) (S4 : Ty) (wf0 : (wfTy k8 S4)) =>
    (forall {d : (Trace ty)} {k9 : Hvl} ,
      (substhvl_ty k7 d k8 k9) -> (wfTy k9 (tsubstTy d S3 S4)))) (fun (k8 : Hvl) {X12 : (Index ty)} (wfi : (wfindex k8 X12)) {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k8 : Hvl) (T1 : Ty) (wf0 : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k8 T2)) IHT2 {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (wfTy_tarr k9 (IHT1 (weakenTrace d H0) k9 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k9 (weaken_substhvl_ty H0 del)))) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k8) T)) IHT {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (wfTy_tall k9 (IHT (weakenTrace d (HS ty H0)) (HS ty k9) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k7 : Hvl} {s4 : Tm} (wf : (wfTm k7 s4)) : (forall (k8 : Hvl) ,
    (forall (s5 : Tm) (wf0 : (wfTm k8 s5)) ,
      (forall {d : (Trace tm)} {k9 : Hvl} ,
        (substhvl_tm k7 d k8 k9) -> (wfTm k9 (substTm d s4 s5))))) := (ind_wfTm (fun (k8 : Hvl) (s5 : Tm) (wf0 : (wfTm k8 s5)) =>
    (forall {d : (Trace tm)} {k9 : Hvl} ,
      (substhvl_tm k7 d k8 k9) -> (wfTm k9 (substTm d s4 s5)))) (fun (k8 : Hvl) {x8 : (Index tm)} (wfi : (wfindex k8 x8)) {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) (t : Tm) (wf1 : (wfTm (HS tm k8) t)) IHt {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (wfTm_abs k9 (substhvl_tm_wfTy k8 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k9) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k8 : Hvl) (t1 : Tm) (wf0 : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k8 t2)) IHt2 {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (wfTm_app k9 (IHt1 (weakenTrace d H0) k9 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k9 (weaken_substhvl_tm H0 del)))) (fun (k8 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k8) t)) IHt {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (wfTm_tabs k9 (IHt (weakenTrace d (HS ty H0)) (HS ty k9) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k8 : Hvl) (t : Tm) (wf0 : (wfTm k8 t)) IHt (T : Ty) (wf1 : (wfTy k8 T)) {d : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d k8 k9)) =>
    (wfTm_tapp k9 (IHt (weakenTrace d H0) k9 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k8 T wf1 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k7 : Hvl} {S3 : Ty} (wf : (wfTy k7 S3)) : (forall (k8 : Hvl) ,
    (forall (s4 : Tm) (wf0 : (wfTm k8 s4)) ,
      (forall {d : (Trace ty)} {k9 : Hvl} ,
        (substhvl_ty k7 d k8 k9) -> (wfTm k9 (tsubstTm d S3 s4))))) := (ind_wfTm (fun (k8 : Hvl) (s4 : Tm) (wf0 : (wfTm k8 s4)) =>
    (forall {d : (Trace ty)} {k9 : Hvl} ,
      (substhvl_ty k7 d k8 k9) -> (wfTm k9 (tsubstTm d S3 s4)))) (fun (k8 : Hvl) {x8 : (Index tm)} (wfi : (wfindex k8 x8)) {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (wfTm_var k9 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) (t : Tm) (wf1 : (wfTm (HS tm k8) t)) IHt {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (wfTm_abs k9 (substhvl_ty_wfTy wf k8 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k9) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k8 : Hvl) (t1 : Tm) (wf0 : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k8 t2)) IHt2 {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (wfTm_app k9 (IHt1 (weakenTrace d H0) k9 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d H0) k9 (weaken_substhvl_ty H0 del)))) (fun (k8 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k8) t)) IHt {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (wfTm_tabs k9 (IHt (weakenTrace d (HS ty H0)) (HS ty k9) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k8 : Hvl) (t : Tm) (wf0 : (wfTm k8 t)) IHt (T : Ty) (wf1 : (wfTy k8 T)) {d : (Trace ty)} {k9 : Hvl} (del : (substhvl_ty k7 d k8 k9)) =>
    (wfTm_tapp k9 (IHt (weakenTrace d H0) k9 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k8 T wf1 (weaken_substhvl_ty H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty)
    | etvar (G : Env).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1) => (etvar (appendEnv G G1))
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0) => (HS ty (domainEnv G0))
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
      | (etvar G0) => (etvar (shiftEnv c G0))
    end.
  Fixpoint tshiftEnv (c : (Cutoff ty)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c G0) (tshiftTy (weakenCutoffty c (domainEnv G0)) T))
      | (etvar G0) => (etvar (tshiftEnv c G0))
    end.
  Fixpoint weakenEnv (G : Env) (k7 : Hvl) {struct k7} :
  Env :=
    match k7 with
      | (H0) => G
      | (HS tm k7) => (weakenEnv G k7)
      | (HS ty k7) => (tshiftEnv C0 (weakenEnv G k7))
    end.
  Fixpoint substEnv (d : (Trace tm)) (s4 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s4 G0) T)
      | (etvar G0) => (etvar (substEnv d s4 G0))
    end.
  Fixpoint tsubstEnv (d : (Trace ty)) (S3 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d S3 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S3 T))
      | (etvar G0) => (etvar (tsubstEnv d S3 G0))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c : (Cutoff ty)) (G : Env) ,
      ((domainEnv (tshiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d : (Trace tm)) (s4 : Tm) (G : Env) ,
      ((domainEnv (substEnv d s4 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d : (Trace ty)) (S3 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d S3 G)) = (domainEnv G))).
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
    Lemma tshiftEnv_appendEnv  :
      (forall (c : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c (appendEnv G G0)) = (appendEnv (tshiftEnv c G) (tshiftEnv (weakenCutoffty c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d : (Trace tm)) (s4 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d s4 (appendEnv G G0)) = (appendEnv (substEnv d s4 G) (substEnv (weakenTrace d (domainEnv G)) s4 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d : (Trace ty)) (S3 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d S3 (appendEnv G G0)) = (appendEnv (tsubstEnv d S3 G) (tsubstEnv (weakenTrace d (domainEnv G)) S3 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S3 : Ty) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenTy (weakenTy S3 k7) k8) = (weakenTy S3 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s4 : Tm) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenTm (weakenTm s4 k7) k8) = (weakenTm s4 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T23 : Ty) :
          (wfTy (domainEnv G) T23) -> (lookup_evar (evar G T23) I0 T23)
      | lookup_evar_there_evar
          {G : Env} {x8 : (Index tm)}
          (T24 : Ty) (T25 : Ty) :
          (lookup_evar G x8 T24) -> (lookup_evar (evar G T25) (IS x8) T24)
      | lookup_evar_there_etvar
          {G : Env} {x8 : (Index tm)}
          (T24 : Ty) :
          (lookup_evar G x8 T24) -> (lookup_evar (etvar G) x8 (tshiftTy C0 T24)).
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G : Env}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Env} {X12 : (Index ty)}
          (T24 : Ty) :
          (lookup_etvar G X12) -> (lookup_etvar (evar G T24) X12)
      | lookup_etvar_there_etvar
          {G : Env} {X12 : (Index ty)} :
          (lookup_etvar G X12) -> (lookup_etvar (etvar G) (IS X12)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T24 : Ty) (T25 : Ty) ,
        (lookup_evar (evar G T24) I0 T25) -> (T24 = T25)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x8 : (Index tm)} ,
        (forall (T24 : Ty) ,
          (lookup_evar G x8 T24) -> (forall (T25 : Ty) ,
            (lookup_evar G x8 T25) -> (T24 = T25)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x8 : (Index tm)} (T24 : Ty) ,
        (lookup_evar G x8 T24) -> (wfTy (domainEnv G) T24)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x8 : (Index tm)} (T24 : Ty) ,
        (lookup_evar G x8 T24) -> (lookup_evar (appendEnv G G0) (weakenIndextm x8 (domainEnv G0)) (weakenTy T24 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X12 : (Index ty)} ,
        (lookup_etvar G X12) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X12 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x8 : (Index tm)} (T26 : Ty) ,
        (lookup_evar G x8 T26) -> (wfindex (domainEnv G) x8)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X12 : (Index ty)} ,
        (lookup_etvar G X12) -> (wfindex (domainEnv G) X12)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T24 : Ty} :
        (shift_evar C0 G (evar G T24))
    | shiftevar_there_evar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} :
        (shift_evar c G G0) -> (shift_evar c (etvar G) (etvar G0)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutofftm c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_evar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (tshiftTy c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G) (etvar G0)).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c G0 G1) -> (shift_etvar (weakenCutoffty c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c G G0) -> (shifthvl_tm c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c G G0) -> (shifthvl_ty c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T24 : Ty) (s4 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T24 s4 X0 (evar G T24) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T25 : Ty) :
        (subst_evar G T24 s4 d G0 G1) -> (subst_evar G T24 s4 (XS tm d) (evar G0 T25) (evar G1 T25))
    | subst_evar_there_etvar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} :
        (subst_evar G T24 s4 d G0 G1) -> (subst_evar G T24 s4 (XS ty d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Env} (T24 : Ty) {s4 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T24 s4 d G1 G2) -> (subst_evar G T24 s4 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (S3 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S3 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T24 : Ty) :
        (subst_etvar G S3 d G0 G1) -> (subst_etvar G S3 (XS tm d) (evar G0 T24) (evar G1 (tsubstTy d S3 T24)))
    | subst_etvar_there_etvar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} :
        (subst_etvar G S3 d G0 G1) -> (subst_etvar G S3 (XS ty d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_etvar {G : Env} {S3 : Ty} :
    (forall (G0 : Env) {d : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G S3 d G1 G2) -> (subst_etvar G S3 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d S3 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s4 : Tm} (T24 : Ty) :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T24 s4 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S3 : Ty} :
    (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G S3 d G0 G1) -> (substhvl_ty (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainEnv_tshiftEnv : interaction.
 Hint Rewrite domainEnv_tshiftEnv : env_domain_shift.
 Hint Rewrite domainEnv_tsubstEnv : interaction.
 Hint Rewrite domainEnv_tsubstEnv : env_domain_subst.
 Hint Rewrite tshiftEnv_appendEnv : interaction.
 Hint Rewrite tshiftEnv_appendEnv : env_shift_append.
 Hint Rewrite tsubstEnv_appendEnv : interaction.
 Hint Rewrite tsubstEnv_appendEnv : env_shift_append.
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) {T24 : Ty} (wf : (wfTy (domainEnv G) T24)) ,
    (lookup_evar (appendEnv (evar G T24) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T24 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) ,
    (lookup_etvar (appendEnv (etvar G) G0) (weakenIndexty I0 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTm wfTy : infra.
 Hint Constructors wfTm wfTy : wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H25 : (wfTy _ (tvar _)) |- _ => inversion H25; subst; clear H25
  | H25 : (wfTy _ (tarr _ _)) |- _ => inversion H25; subst; clear H25
  | H25 : (wfTy _ (tall _)) |- _ => inversion H25; subst; clear H25
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H25 : (wfTm _ (var _)) |- _ => inversion H25; subst; clear H25
  | H25 : (wfTm _ (abs _ _)) |- _ => inversion H25; subst; clear H25
  | H25 : (wfTm _ (app _ _)) |- _ => inversion H25; subst; clear H25
  | H25 : (wfTm _ (tabs _)) |- _ => inversion H25; subst; clear H25
  | H25 : (wfTm _ (tapp _ _)) |- _ => inversion H25; subst; clear H25
end : infra wf.
 Hint Resolve lookup_evar_wf : infra.
 Hint Resolve lookup_evar_wf : wf.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : wf.
 Hint Constructors shift_evar shift_etvar : infra.
 Hint Constructors shift_evar shift_etvar : shift.
 Hint Constructors shift_evar shift_etvar : subst.
 Hint Resolve weaken_shift_evar weaken_shift_etvar : infra.
 Hint Resolve weaken_shift_evar weaken_shift_etvar : shift.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : infra.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : shift.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : shift_wf.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : wf.
 Hint Constructors subst_evar subst_etvar : infra.
 Hint Constructors subst_evar subst_etvar : subst.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : infra.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : subst.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : infra.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : subst.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : subst_wf.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : wf.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x8 : (Index tm)} {T24 : Ty} ,
    (lookup_evar G x8 T24) -> (lookup_evar G0 (shiftIndex c x8) T24)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X12 : (Index ty)} ,
    (lookup_etvar G X12) -> (lookup_etvar G0 X12)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x8 : (Index tm)} {T24 : Ty} ,
    (lookup_evar G x8 T24) -> (lookup_evar G0 x8 (tshiftTy c T24))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X12 : (Index ty)} ,
    (lookup_etvar G X12) -> (lookup_etvar G0 (tshiftIndex c X12))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T25 : Ty) {s4 : Tm} :
  (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T25 s4 d G0 G1)) {X12 : (Index ty)} ,
    (lookup_etvar G0 X12) -> (lookup_etvar G1 X12)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {S3 : Ty} (wf : (wfTy (domainEnv G) S3)) :
  (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G S3 d G0 G1)) {x8 : (Index tm)} (T25 : Ty) ,
    (lookup_evar G0 x8 T25) -> (lookup_evar G1 x8 (tsubstTy d S3 T25))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (tvar X12) => 1
    | (tarr T23 T24) => (plus 1 (plus (size_Ty T23) (size_Ty T24)))
    | (tall T25) => (plus 1 (size_Ty T25))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x8) => 1
    | (abs T23 t15) => (plus 1 (plus (size_Ty T23) (size_Tm t15)))
    | (app t16 t17) => (plus 1 (plus (size_Tm t16) (size_Tm t17)))
    | (tabs t18) => (plus 1 (size_Tm t18))
    | (tapp t19 T24) => (plus 1 (plus (size_Tm t19) (size_Ty T24)))
  end.
Fixpoint tshift_size_Ty (S0 : Ty) (c : (Cutoff ty)) {struct S0} :
((size_Ty (tshiftTy c S0)) = (size_Ty S0)) :=
  match S0 return ((size_Ty (tshiftTy c S0)) = (size_Ty S0)) with
    | (tvar _) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tall T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c)))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (tabs t) => (f_equal2 plus eq_refl (shift_size_Tm t c))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c) eq_refl))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
    | (tabs t) => (f_equal2 plus eq_refl (tshift_size_Tm t (CS c)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c) (tshift_size_Ty T c)))
  end.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
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
      (H16 : (wfTy (domainEnv G) T))
      (H17 : (wfindex (domainEnv G) x))
      : (Typing G (var x) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G T1) t (weakenTy T2 (HS tm H0))))
      (H18 : (wfTy (domainEnv G) T1))
      (H19 : (wfTy (domainEnv G) T2))
      :
      (Typing G (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm0 : (Typing G t1 (tarr T11 T12)))
      (jm1 : (Typing G t2 T11)) :
      (Typing G (app t1 t2) T12)
  | T_Tabs (T : Ty) (t : Tm)
      (jm2 : (Typing (etvar G) t T)) :
      (Typing G (tabs t) (tall T))
  | T_Tapp (T12 : Ty) (T2 : Ty)
      (t1 : Tm)
      (jm3 : (Typing G t1 (tall T12)))
      (H28 : (wfTy (domainEnv G) T2))
      :
      (Typing G (tapp t1 T2) (tsubstTy X0 T2 T12)).
Lemma Typing_cast  :
  (forall (G : Env) (t15 : Tm) (T26 : Ty) (G0 : Env) (t16 : Tm) (T27 : Ty) ,
    (G = G0) -> (t15 = t16) -> (T26 = T27) -> (Typing G t15 T26) -> (Typing G0 t16 T27)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_Typing (G1 : Env) (t19 : Tm) (T33 : Ty) (jm10 : (Typing G1 t19 T33)) :
(forall (c : (Cutoff tm)) (G2 : Env) (H44 : (shift_evar c G1 G2)) ,
  (Typing G2 (shiftTm c t19) T33)) :=
  match jm10 in (Typing _ t19 T33) return (forall (c : (Cutoff tm)) (G2 : Env) (H44 : (shift_evar c G1 G2)) ,
    (Typing G2 (shiftTm c t19) T33)) with
    | (T_Var T28 x9 lk0 H28 H29) => (fun (c : (Cutoff tm)) (G2 : Env) (H44 : (shift_evar c G1 G2)) =>
      (T_Var G2 T28 (shiftIndex c x9) (shift_evar_lookup_evar H44 lk0) (shift_wfTy _ _ H28 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H44))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H44)) _ H29)))
    | (T_Abs T29 T32 t16 jm5 H30 H31) => (fun (c : (Cutoff tm)) (G2 : Env) (H44 : (shift_evar c G1 G2)) =>
      (T_Abs G2 T29 T32 (shiftTm (CS c) t16) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G1 T29) t16 (weakenTy T32 (HS tm H0)) jm5 (CS c) (evar G2 T29) (weaken_shift_evar (evar empty T29) H44))) (shift_wfTy _ _ H30 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H44))) (shift_wfTy _ _ H31 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H44)))))
    | (T_App T30 T31 t17 t18 jm6 jm7) => (fun (c : (Cutoff tm)) (G2 : Env) (H44 : (shift_evar c G1 G2)) =>
      (T_App G2 T30 T31 (shiftTm c t17) (shiftTm c t18) (shift_evar_Typing G1 t17 (tarr T30 T31) jm6 c G2 (weaken_shift_evar empty H44)) (shift_evar_Typing G1 t18 T30 jm7 c G2 (weaken_shift_evar empty H44))))
    | (T_Tabs T28 t16 jm8) => (fun (c : (Cutoff tm)) (G2 : Env) (H44 : (shift_evar c G1 G2)) =>
      (T_Tabs G2 T28 (shiftTm c t16) (shift_evar_Typing (etvar G1) t16 T28 jm8 c (etvar G2) (weaken_shift_evar (etvar empty) H44))))
    | (T_Tapp T31 T32 t17 jm9 H40) => (fun (c : (Cutoff tm)) (G2 : Env) (H44 : (shift_evar c G1 G2)) =>
      (T_Tapp G2 T31 T32 (shiftTm c t17) (shift_evar_Typing G1 t17 (tall T31) jm9 c G2 (weaken_shift_evar empty H44)) (shift_wfTy _ _ H40 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H44)))))
  end.
Fixpoint shift_etvar_Typing (G1 : Env) (t19 : Tm) (T33 : Ty) (jm10 : (Typing G1 t19 T33)) :
(forall (c : (Cutoff ty)) (G2 : Env) (H44 : (shift_etvar c G1 G2)) ,
  (Typing G2 (tshiftTm c t19) (tshiftTy c T33))) :=
  match jm10 in (Typing _ t19 T33) return (forall (c : (Cutoff ty)) (G2 : Env) (H44 : (shift_etvar c G1 G2)) ,
    (Typing G2 (tshiftTm c t19) (tshiftTy c T33))) with
    | (T_Var T28 x9 lk0 H28 H29) => (fun (c : (Cutoff ty)) (G2 : Env) (H44 : (shift_etvar c G1 G2)) =>
      (T_Var G2 (tshiftTy c T28) x9 (shift_etvar_lookup_evar H44 lk0) (tshift_wfTy _ _ H28 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H44))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H44)) _ H29)))
    | (T_Abs T29 T32 t16 jm5 H30 H31) => (fun (c : (Cutoff ty)) (G2 : Env) (H44 : (shift_etvar c G1 G2)) =>
      (T_Abs G2 (tshiftTy c T29) (tshiftTy c T32) (tshiftTm c t16) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c T32)) (shift_etvar_Typing (evar G1 T29) t16 (weakenTy T32 (HS tm H0)) jm5 c (evar G2 (tshiftTy c T29)) (weaken_shift_etvar (evar empty T29) H44))) (tshift_wfTy _ _ H30 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H44))) (tshift_wfTy _ _ H31 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H44)))))
    | (T_App T30 T31 t17 t18 jm6 jm7) => (fun (c : (Cutoff ty)) (G2 : Env) (H44 : (shift_etvar c G1 G2)) =>
      (T_App G2 (tshiftTy c T30) (tshiftTy c T31) (tshiftTm c t17) (tshiftTm c t18) (shift_etvar_Typing G1 t17 (tarr T30 T31) jm6 c G2 (weaken_shift_etvar empty H44)) (shift_etvar_Typing G1 t18 T30 jm7 c G2 (weaken_shift_etvar empty H44))))
    | (T_Tabs T28 t16 jm8) => (fun (c : (Cutoff ty)) (G2 : Env) (H44 : (shift_etvar c G1 G2)) =>
      (T_Tabs G2 (tshiftTy (CS c) T28) (tshiftTm (CS c) t16) (shift_etvar_Typing (etvar G1) t16 T28 jm8 (CS c) (etvar G2) (weaken_shift_etvar (etvar empty) H44))))
    | (T_Tapp T31 T32 t17 jm9 H40) => (fun (c : (Cutoff ty)) (G2 : Env) (H44 : (shift_etvar c G1 G2)) =>
      (Typing_cast G2 _ _ G2 (tshiftTm c (tapp t17 T32)) (tshiftTy c (tsubstTy X0 T32 T31)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T31 c T32)) (T_Tapp G2 (tshiftTy (CS c) T31) (tshiftTy c T32) (tshiftTm c t17) (shift_etvar_Typing G1 t17 (tall T31) jm9 c G2 (weaken_shift_etvar empty H44)) (tshift_wfTy _ _ H40 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H44))))))
  end.
 Hint Resolve shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_Typing (G : Env) :
(forall (G0 : Env) (t15 : Tm) (T26 : Ty) (jm4 : (Typing G0 t15 T26)) ,
  (Typing (appendEnv G0 G) (weakenTm t15 (domainEnv G)) (weakenTy T26 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (t15 : Tm) (T26 : Ty) (jm4 : (Typing G0 t15 T26)) ,
    (Typing (appendEnv G0 G) (weakenTm t15 (domainEnv G)) (weakenTy T26 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (t15 : Tm) (T26 : Ty) (jm4 : (Typing G0 t15 T26)) =>
      jm4)
    | (evar G T27) => (fun (G0 : Env) (t15 : Tm) (T26 : Ty) (jm4 : (Typing G0 t15 T26)) =>
      (shift_evar_Typing (appendEnv G0 G) (weakenTm t15 (domainEnv G)) (weakenTy T26 (domainEnv G)) (weaken_Typing G G0 t15 T26 jm4) C0 (evar (appendEnv G0 G) T27) shift_evar_here))
    | (etvar G) => (fun (G0 : Env) (t15 : Tm) (T26 : Ty) (jm4 : (Typing G0 t15 T26)) =>
      (shift_etvar_Typing (appendEnv G0 G) (weakenTm t15 (domainEnv G)) (weakenTy T26 (domainEnv G)) (weaken_Typing G G0 t15 T26 jm4) C0 (etvar (appendEnv G0 G)) shift_etvar_here))
  end.
Fixpoint Typing_wf_0 (G : Env) (t16 : Tm) (T28 : Ty) (jm5 : (Typing G t16 T28)) {struct jm5} :
(wfTm (domainEnv G) t16) :=
  match jm5 in (Typing _ t16 T28) return (wfTm (domainEnv G) t16) with
    | (T_Var T x lk0 H16 H17) => (wfTm_var (domainEnv G) _ H17)
    | (T_Abs T1 T2 t jm H18 H19) => (wfTm_abs (domainEnv G) H18 (Typing_wf_0 (evar G T1) t (weakenTy T2 (HS tm H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tarr T11 T12) jm0) (Typing_wf_0 G t2 T11 jm1))
    | (T_Tabs T t jm2) => (wfTm_tabs (domainEnv G) (Typing_wf_0 (etvar G) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H28) => (wfTm_tapp (domainEnv G) (Typing_wf_0 G t1 (tall T12) jm3) H28)
  end
with Typing_wf_1 (G : Env) (t16 : Tm) (T28 : Ty) (jm6 : (Typing G t16 T28)) {struct jm6} :
(wfTy (domainEnv G) T28) :=
  match jm6 in (Typing _ t16 T28) return (wfTy (domainEnv G) T28) with
    | (T_Var T x lk1 H16 H17) => H16
    | (T_Abs T1 T2 t jm H18 H19) => (wfTy_tarr (domainEnv G) H18 H19)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_tarr_1 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tarr T11 T12) jm0))
    | (T_Tabs T t jm2) => (wfTy_tall (domainEnv G) (Typing_wf_1 (etvar G) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H28) => (substhvl_ty_wfTy H28 (HS ty (domainEnv G)) T12 (inversion_wfTy_tall_1 (domainEnv G) T12 (Typing_wf_1 G t1 (tall T12) jm3)) (substhvl_ty_here (domainEnv G)))
  end.
 Hint Extern 8 => match goal with
  | H30 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H30)); pose proof ((Typing_wf_1 _ _ _ H30)); clear H30
end : wf.
Lemma subst_evar_lookup_evar (G1 : Env) (s4 : Tm) (T29 : Ty) (jm7 : (Typing G1 s4 T29)) :
  (forall (d : (Trace tm)) (G2 : Env) (G4 : Env) (sub : (subst_evar G1 T29 s4 d G2 G4)) (x9 : (Index tm)) (T30 : Ty) ,
    (lookup_evar G2 x9 T30) -> (Typing G4 (substIndex d s4 x9) T30)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Fixpoint subst_evar_Typing (G2 : Env) (s4 : Tm) (T29 : Ty) (jm12 : (Typing G2 s4 T29)) (G1 : Env) (t : Tm) (T : Ty) (jm13 : (Typing G1 t T)) :
(forall (G3 : Env) (d : (Trace tm)) (H46 : (subst_evar G2 T29 s4 d G1 G3)) ,
  (Typing G3 (substTm d s4 t) T)) :=
  match jm13 in (Typing _ t T) return (forall (G3 : Env) (d : (Trace tm)) (H46 : (subst_evar G2 T29 s4 d G1 G3)) ,
    (Typing G3 (substTm d s4 t) T)) with
    | (T_Var T30 x9 lk2 H32 H33) => (fun (G3 : Env) (d : (Trace tm)) (H46 : (subst_evar G2 T29 s4 d G1 G3)) =>
      (subst_evar_lookup_evar G2 s4 T29 jm12 d G1 G3 H46 x9 T30 lk2))
    | (T_Abs T31 T34 t17 jm7 H34 H35) => (fun (G3 : Env) (d : (Trace tm)) (H46 : (subst_evar G2 T29 s4 d G1 G3)) =>
      (T_Abs G3 T31 T34 (substTm (weakenTrace d (HS tm H0)) s4 t17) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G2 s4 T29 jm12 (evar G1 T31) t17 (weakenTy T34 (HS tm H0)) jm7 (appendEnv G3 (evar empty T31)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T31) H46))) (substhvl_tm_wfTy _ _ H34 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H46))) (substhvl_tm_wfTy _ _ H35 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H46)))))
    | (T_App T32 T33 t18 t19 jm8 jm9) => (fun (G3 : Env) (d : (Trace tm)) (H46 : (subst_evar G2 T29 s4 d G1 G3)) =>
      (T_App G3 T32 T33 (substTm (weakenTrace d H0) s4 t18) (substTm (weakenTrace d H0) s4 t19) (subst_evar_Typing G2 s4 T29 jm12 G1 t18 (tarr T32 T33) jm8 G3 d (weaken_subst_evar _ empty H46)) (subst_evar_Typing G2 s4 T29 jm12 G1 t19 T32 jm9 G3 d (weaken_subst_evar _ empty H46))))
    | (T_Tabs T30 t17 jm10) => (fun (G3 : Env) (d : (Trace tm)) (H46 : (subst_evar G2 T29 s4 d G1 G3)) =>
      (T_Tabs G3 T30 (substTm (weakenTrace d (HS ty H0)) s4 t17) (subst_evar_Typing G2 s4 T29 jm12 (etvar G1) t17 T30 jm10 (appendEnv G3 (etvar empty)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty) H46))))
    | (T_Tapp T33 T34 t18 jm11 H44) => (fun (G3 : Env) (d : (Trace tm)) (H46 : (subst_evar G2 T29 s4 d G1 G3)) =>
      (T_Tapp G3 T33 T34 (substTm (weakenTrace d H0) s4 t18) (subst_evar_Typing G2 s4 T29 jm12 G1 t18 (tall T33) jm11 G3 d (weaken_subst_evar _ empty H46)) (substhvl_tm_wfTy _ _ H44 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H46)))))
  end.
Fixpoint subst_etvar_Typing (G2 : Env) (S3 : Ty) (H46 : (wfTy (domainEnv G2) S3)) (G1 : Env) (t : Tm) (T : Ty) (jm12 : (Typing G1 t T)) :
(forall (G3 : Env) (d : (Trace ty)) (H47 : (subst_etvar G2 S3 d G1 G3)) ,
  (Typing G3 (tsubstTm d S3 t) (tsubstTy d S3 T))) :=
  match jm12 in (Typing _ t T) return (forall (G3 : Env) (d : (Trace ty)) (H47 : (subst_etvar G2 S3 d G1 G3)) ,
    (Typing G3 (tsubstTm d S3 t) (tsubstTy d S3 T))) with
    | (T_Var T30 x9 lk2 H32 H33) => (fun (G3 : Env) (d : (Trace ty)) (H47 : (subst_etvar G2 S3 d G1 G3)) =>
      (T_Var G3 (tsubstTy (weakenTrace d H0) S3 T30) x9 (subst_etvar_lookup_evar H46 H47 T30 lk2) (substhvl_ty_wfTy H46 _ _ H32 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H47))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H47)) H33)))
    | (T_Abs T31 T34 t17 jm7 H34 H35) => (fun (G3 : Env) (d : (Trace ty)) (H47 : (subst_etvar G2 S3 d G1 G3)) =>
      (T_Abs G3 (tsubstTy (weakenTrace d H0) S3 T31) (tsubstTy (weakenTrace d H0) S3 T34) (tsubstTm (weakenTrace d (HS tm H0)) S3 t17) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d S3 T34)) (subst_etvar_Typing G2 S3 H46 (evar G1 T31) t17 (weakenTy T34 (HS tm H0)) jm7 (appendEnv G3 (tsubstEnv d S3 (evar empty T31))) (weakenTrace d (HS tm H0)) (weaken_subst_etvar (evar empty T31) H47))) (substhvl_ty_wfTy H46 _ _ H34 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H47))) (substhvl_ty_wfTy H46 _ _ H35 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H47)))))
    | (T_App T32 T33 t18 t19 jm8 jm9) => (fun (G3 : Env) (d : (Trace ty)) (H47 : (subst_etvar G2 S3 d G1 G3)) =>
      (T_App G3 (tsubstTy (weakenTrace d H0) S3 T32) (tsubstTy (weakenTrace d H0) S3 T33) (tsubstTm (weakenTrace d H0) S3 t18) (tsubstTm (weakenTrace d H0) S3 t19) (subst_etvar_Typing G2 S3 H46 G1 t18 (tarr T32 T33) jm8 G3 d (weaken_subst_etvar empty H47)) (subst_etvar_Typing G2 S3 H46 G1 t19 T32 jm9 G3 d (weaken_subst_etvar empty H47))))
    | (T_Tabs T30 t17 jm10) => (fun (G3 : Env) (d : (Trace ty)) (H47 : (subst_etvar G2 S3 d G1 G3)) =>
      (T_Tabs G3 (tsubstTy (weakenTrace d (HS ty H0)) S3 T30) (tsubstTm (weakenTrace d (HS ty H0)) S3 t17) (subst_etvar_Typing G2 S3 H46 (etvar G1) t17 T30 jm10 (appendEnv G3 (tsubstEnv d S3 (etvar empty))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar (etvar empty) H47))))
    | (T_Tapp T33 T34 t18 jm11 H44) => (fun (G3 : Env) (d : (Trace ty)) (H47 : (subst_etvar G2 S3 d G1 G3)) =>
      (Typing_cast G3 _ _ G3 (tsubstTm d S3 (tapp t18 T34)) (tsubstTy d S3 (tsubstTy X0 T34 T33)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T33 d S3 T34)) (T_Tapp G3 (tsubstTy (weakenTrace d (HS ty H0)) S3 T33) (tsubstTy (weakenTrace d H0) S3 T34) (tsubstTm (weakenTrace d H0) S3 t18) (subst_etvar_Typing G2 S3 H46 G1 t18 (tall T33) jm11 G3 d (weaken_subst_etvar empty H47)) (substhvl_ty_wfTy H46 _ _ H44 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H47))))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.