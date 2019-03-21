Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.
Section Namespace.
  Inductive Namespace : Type :=
    | ty 
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
  
  Fixpoint weakenIndexty (X23 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X23
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X23 k))
        | _ => (weakenIndexty X23 k)
      end
    end.
  Fixpoint weakenIndextm (x13 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x13
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x13 k))
        | _ => (weakenIndextm x13 k)
      end
    end.
  Lemma weakenIndexty_append  :
    (forall (X23 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X23 k) k0) = (weakenIndexty X23 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndextm_append  :
    (forall (x13 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x13 k) k0) = (weakenIndextm x13 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T : Ty)
    | texist (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | pack (T1 : Ty) (t : Tm)
        (T2 : Ty)
    | unpack (t1 : Tm) (t2 : Tm).
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
  Fixpoint weakenCutoffty (c : (Cutoff ty)) (k : Hvl) {struct k} :
  (Cutoff ty) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (ty) => (CS (weakenCutoffty c k))
        | _ => (weakenCutoffty c k)
      end
    end.
  Fixpoint weakenCutofftm (c : (Cutoff tm)) (k : Hvl) {struct k} :
  (Cutoff tm) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (tm) => (CS (weakenCutofftm c k))
        | _ => (weakenCutofftm c k)
      end
    end.
  
  Lemma weakenCutoffty_append  :
    (forall (c : (Cutoff ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffty (weakenCutoffty c k) k0) = (weakenCutoffty c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) = (weakenCutofftm c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X23 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X23)
      | (CS c) => match X23 with
        | (I0) => I0
        | (IS X23) => (IS (tshiftIndex c X23))
      end
    end.
  Fixpoint shiftIndex (c : (Cutoff tm)) (x13 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x13)
      | (CS c) => match x13 with
        | (I0) => I0
        | (IS x13) => (IS (shiftIndex c x13))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (tvar X23) => (tvar (tshiftIndex c X23))
      | (tarr T33 T34) => (tarr (tshiftTy c T33) (tshiftTy c T34))
      | (tall T35) => (tall (tshiftTy (CS c) T35))
      | (texist T36) => (texist (tshiftTy (CS c) T36))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x13) => (var (shiftIndex c x13))
      | (abs T33 t24) => (abs T33 (shiftTm (CS c) t24))
      | (app t25 t26) => (app (shiftTm c t25) (shiftTm c t26))
      | (tabs t27) => (tabs (shiftTm c t27))
      | (tapp t28 T34) => (tapp (shiftTm c t28) T34)
      | (pack T35 t29 T36) => (pack T35 (shiftTm c t29) T36)
      | (unpack t30 t31) => (unpack (shiftTm c t30) (shiftTm (CS c) t31))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x13) => (var x13)
      | (abs T33 t24) => (abs (tshiftTy c T33) (tshiftTm c t24))
      | (app t25 t26) => (app (tshiftTm c t25) (tshiftTm c t26))
      | (tabs t27) => (tabs (tshiftTm (CS c) t27))
      | (tapp t28 T34) => (tapp (tshiftTm c t28) (tshiftTy c T34))
      | (pack T35 t29 T36) => (pack (tshiftTy c T35) (tshiftTm c t29) (tshiftTy c T36))
      | (unpack t30 t31) => (unpack (tshiftTm c t30) (tshiftTm (CS c) t31))
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
        (T33 : (Trace a)).
  
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
  Fixpoint tsubstIndex (d : (Trace ty)) (S0 : Ty) (X23 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X23 with
        | (I0) => S0
        | (IS X23) => (tvar X23)
      end
      | (XS tm d) => (tsubstIndex d S0 X23)
      | (XS ty d) => match X23 with
        | (I0) => (tvar I0)
        | (IS X23) => (tshiftTy C0 (tsubstIndex d S0 X23))
      end
    end.
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
      | (XS ty d) => (tshiftTm C0 (substIndex d s x13))
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (tvar X23) => (tsubstIndex d S0 X23)
      | (tarr T33 T34) => (tarr (tsubstTy d S0 T33) (tsubstTy d S0 T34))
      | (tall T35) => (tall (tsubstTy (weakenTrace d (HS ty H0)) S0 T35))
      | (texist T36) => (texist (tsubstTy (weakenTrace d (HS ty H0)) S0 T36))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x13) => (substIndex d s x13)
      | (abs T33 t24) => (abs T33 (substTm (weakenTrace d (HS tm H0)) s t24))
      | (app t25 t26) => (app (substTm d s t25) (substTm d s t26))
      | (tabs t27) => (tabs (substTm (weakenTrace d (HS ty H0)) s t27))
      | (tapp t28 T34) => (tapp (substTm d s t28) T34)
      | (pack T35 t29 T36) => (pack T35 (substTm d s t29) T36)
      | (unpack t30 t31) => (unpack (substTm d s t30) (substTm (weakenTrace d (HS tm (HS ty H0))) s t31))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x13) => (var x13)
      | (abs T33 t24) => (abs (tsubstTy d S0 T33) (tsubstTm (weakenTrace d (HS tm H0)) S0 t24))
      | (app t25 t26) => (app (tsubstTm d S0 t25) (tsubstTm d S0 t26))
      | (tabs t27) => (tabs (tsubstTm (weakenTrace d (HS ty H0)) S0 t27))
      | (tapp t28 T34) => (tapp (tsubstTm d S0 t28) (tsubstTy d S0 T34))
      | (pack T35 t29 T36) => (pack (tsubstTy d S0 T35) (tsubstTm d S0 t29) (tsubstTy d S0 T36))
      | (unpack t30 t31) => (unpack (tsubstTm d S0 t30) (tsubstTm (weakenTrace d (HS tm (HS ty H0))) S0 t31))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S0 : Ty) :
    (forall (k : Hvl) (X23 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S0 (tshiftIndex (weakenCutoffty C0 k) X23)) = (tvar X23))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x13 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x13)) = (var x13))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S1 : Ty) (k : Hvl) (S0 : Ty) {struct S1} :
  ((tsubstTy (weakenTrace X0 k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = S1) :=
    match S1 return ((tsubstTy (weakenTrace X0 k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = S1) with
      | (tvar X23) => (tsubstIndex0_tshiftIndex0_reflection_ind S0 k X23)
      | (tarr T34 T35) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T34 k S0) (tsubst0_tshift0_Ty_reflection_ind T35 k S0))
      | (tall T33) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T33 (HS ty k) S0)))
      | (texist T33) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T33 (HS ty k) S0)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x13) => (substIndex0_shiftIndex0_reflection_ind s k x13)
      | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t24 (HS tm k) s)))
      | (app t25 t26) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t25 k s) (subst0_shift0_Tm_reflection_ind t26 k s))
      | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t24 (HS ty k) s)))
      | (tapp t24 T33) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t24 k s) eq_refl)
      | (pack T34 t24 T35) => (f_equal3 pack eq_refl (subst0_shift0_Tm_reflection_ind t24 k s) eq_refl)
      | (unpack t25 t26) => (f_equal2 unpack (subst0_shift0_Tm_reflection_ind t25 k s) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t26 (HS tm (HS ty k)) s)))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S0 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x13) => eq_refl
      | (abs T33 t24) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T33 k S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t24 (HS tm k) S0)))
      | (app t25 t26) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t25 k S0) (tsubst0_tshift0_Tm_reflection_ind t26 k S0))
      | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t24 (HS ty k) S0)))
      | (tapp t24 T33) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t24 k S0) (tsubst0_tshift0_Ty_reflection_ind T33 k S0))
      | (pack T34 t24 T35) => (f_equal3 pack (tsubst0_tshift0_Ty_reflection_ind T34 k S0) (tsubst0_tshift0_Tm_reflection_ind t24 k S0) (tsubst0_tshift0_Ty_reflection_ind T35 k S0))
      | (unpack t25 t26) => (f_equal2 unpack (tsubst0_tshift0_Tm_reflection_ind t25 k S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t26 (HS tm (HS ty k)) S0)))
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
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff ty)) (X23 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c) k) (tshiftIndex (weakenCutoffty C0 k) X23)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c k) X23)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x13 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x13)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x13)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff ty)) {struct S0} :
    ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S0)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S0))) :=
      match S0 return ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S0)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S0))) with
        | (tvar X23) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c X23))
        | (tarr T34 T35) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T34 k c) (tshift_tshift0_Ty_comm_ind T35 k c))
        | (tall T33) => (f_equal tall (tshift_tshift0_Ty_comm_ind T33 (HS ty k) c))
        | (texist T33) => (f_equal texist (tshift_tshift0_Ty_comm_ind T33 (HS ty k) c))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x13) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x13))
        | (abs T33 t24) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t24 (HS tm k) c))
        | (app t25 t26) => (f_equal2 app (shift_shift0_Tm_comm_ind t25 k c) (shift_shift0_Tm_comm_ind t26 k c))
        | (tabs t24) => (f_equal tabs (shift_shift0_Tm_comm_ind t24 (HS ty k) c))
        | (tapp t24 T33) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t24 k c) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (shift_shift0_Tm_comm_ind t24 k c) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (shift_shift0_Tm_comm_ind t25 k c) (shift_shift0_Tm_comm_ind t26 (HS tm (HS ty k)) c))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t24 (HS tm k) c))
        | (app t25 t26) => (f_equal2 app (shift_tshift0_Tm_comm_ind t25 k c) (shift_tshift0_Tm_comm_ind t26 k c))
        | (tabs t24) => (f_equal tabs (shift_tshift0_Tm_comm_ind t24 (HS ty k) c))
        | (tapp t24 T33) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t24 k c) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (shift_tshift0_Tm_comm_ind t24 k c) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (shift_tshift0_Tm_comm_ind t25 k c) (shift_tshift0_Tm_comm_ind t26 (HS tm (HS ty k)) c))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t24 (HS tm k) c))
        | (app t25 t26) => (f_equal2 app (tshift_shift0_Tm_comm_ind t25 k c) (tshift_shift0_Tm_comm_ind t26 k c))
        | (tabs t24) => (f_equal tabs (tshift_shift0_Tm_comm_ind t24 (HS ty k) c))
        | (tapp t24 T33) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t24 k c) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (tshift_shift0_Tm_comm_ind t24 k c) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (tshift_shift0_Tm_comm_ind t25 k c) (tshift_shift0_Tm_comm_ind t26 (HS tm (HS ty k)) c))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T33 k c) (tshift_tshift0_Tm_comm_ind t24 (HS tm k) c))
        | (app t25 t26) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t25 k c) (tshift_tshift0_Tm_comm_ind t26 k c))
        | (tabs t24) => (f_equal tabs (tshift_tshift0_Tm_comm_ind t24 (HS ty k) c))
        | (tapp t24 T33) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t24 k c) (tshift_tshift0_Ty_comm_ind T33 k c))
        | (pack T34 t24 T35) => (f_equal3 pack (tshift_tshift0_Ty_comm_ind T34 k c) (tshift_tshift0_Tm_comm_ind t24 k c) (tshift_tshift0_Ty_comm_ind T35 k c))
        | (unpack t25 t26) => (f_equal2 unpack (tshift_tshift0_Tm_comm_ind t25 k c) (tshift_tshift0_Tm_comm_ind t26 (HS tm (HS ty k)) c))
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
    Lemma tshiftTy_tsubstIndex0_comm_ind (c : (Cutoff ty)) (S0 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c k) (tsubstIndex (weakenTrace X0 k) S0 X23)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c S0) (tshiftIndex (weakenCutoffty (CS c) k) X23)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shiftTm_substIndex0_comm_ind (c : (Cutoff tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c k) (substIndex (weakenTrace X0 k) s x13)) = (substIndex (weakenTrace X0 k) (shiftTm c s) (shiftIndex (weakenCutofftm (CS c) k) x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c k) (substIndex (weakenTrace X0 k) s x13)) = (substIndex (weakenTrace X0 k) (tshiftTm c s) x13))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c : (Cutoff ty)) (S0 : Ty) {struct S1} :
    ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S0 S1)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S0) (tshiftTy (weakenCutoffty (CS c) k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S0 S1)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S0) (tshiftTy (weakenCutoffty (CS c) k) S1))) with
        | (tvar X23) => (tshiftTy_tsubstIndex0_comm_ind c S0 k X23)
        | (tarr T34 T35) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T34 k c S0) (tshift_tsubst0_Ty_comm_ind T35 k c S0))
        | (tall T33) => (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T33 (HS ty k) c S0) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (texist T33) => (f_equal texist (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T33 (HS ty k) c S0) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x13) => (shiftTm_substIndex0_comm_ind c s k x13)
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t24 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t25 t26) => (f_equal2 app (shift_subst0_Tm_comm_ind t25 k c s) (shift_subst0_Tm_comm_ind t26 k c s))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t24 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t24 T33) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t24 k c s) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (shift_subst0_Tm_comm_ind t24 k c s) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (shift_subst0_Tm_comm_ind t25 k c s) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t26 (HS tm (HS ty k)) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) (S0 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) S0 (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) S0 (shiftTm (weakenCutofftm c k) s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t24 (HS tm k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t25 t26) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t25 k c S0) (shift_tsubst0_Tm_comm_ind t26 k c S0))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t24 (HS ty k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t24 T33) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t24 k c S0) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (shift_tsubst0_Tm_comm_ind t24 k c S0) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (shift_tsubst0_Tm_comm_ind t25 k c S0) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t26 (HS tm (HS ty k)) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) with
        | (var x13) => (tshiftTm_substIndex0_comm_ind c s k x13)
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t24 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t25 t26) => (f_equal2 app (tshift_subst0_Tm_comm_ind t25 k c s) (tshift_subst0_Tm_comm_ind t26 k c s))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t24 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t24 T33) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t24 k c s) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (tshift_subst0_Tm_comm_ind t24 k c s) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (tshift_subst0_Tm_comm_ind t25 k c s) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t26 (HS tm (HS ty k)) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) (S0 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S0) (tshiftTm (weakenCutoffty (CS c) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S0 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S0) (tshiftTm (weakenCutoffty (CS c) k) s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T33 k c S0) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t24 (HS tm k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t25 t26) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t25 k c S0) (tshift_tsubst0_Tm_comm_ind t26 k c S0))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t24 (HS ty k) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t24 T33) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t24 k c S0) (tshift_tsubst0_Ty_comm_ind T33 k c S0))
        | (pack T34 t24 T35) => (f_equal3 pack (tshift_tsubst0_Ty_comm_ind T34 k c S0) (tshift_tsubst0_Tm_comm_ind t24 k c S0) (tshift_tsubst0_Ty_comm_ind T35 k c S0))
        | (unpack t25 t26) => (f_equal2 unpack (tshift_tsubst0_Tm_comm_ind t25 k c S0) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t26 (HS tm (HS ty k)) c S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
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
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S0 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k) S0 (tshiftIndex (weakenCutoffty C0 k) X23)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d k) S0 X23)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d : (Trace ty)) (S0 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k) S0 X23) = (tsubstIndex (weakenTrace d k) S0 X23))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d) k) s x13) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d k) s x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k) s (shiftIndex (weakenCutofftm C0 k) x13)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d k) s x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct S1} :
    ((tsubstTy (weakenTrace (XS ty d) k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S0 S1))) :=
      match S1 return ((tsubstTy (weakenTrace (XS ty d) k) S0 (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S0 S1))) with
        | (tvar X23) => (tsubstIndex_tshiftTy0_comm_ind d S0 k X23)
        | (tarr T34 T35) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T34 k d S0) (tsubst_tshift0_Ty_comm_ind T35 k d S0))
        | (tall T33) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T33 (HS ty k) d S0) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (texist T33) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T33 (HS ty k) d S0) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x13) => (substIndex_shiftTm0_comm_ind d s k x13)
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t24 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (subst_shift0_Tm_comm_ind t25 k d s) (subst_shift0_Tm_comm_ind t26 k d s))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t24 (HS ty k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t24 k d s) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (subst_shift0_Tm_comm_ind t24 k d s) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (subst_shift0_Tm_comm_ind t25 k d s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t26 (HS tm (HS ty k)) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x13) => (substIndex_tshiftTm0_comm_ind d s k x13)
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t24 (HS tm k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (subst_tshift0_Tm_comm_ind t25 k d s) (subst_tshift0_Tm_comm_ind t26 k d s))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t24 (HS ty k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t24 k d s) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (subst_tshift0_Tm_comm_ind t24 k d s) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (subst_tshift0_Tm_comm_ind t25 k d s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t26 (HS tm (HS ty k)) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S0 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S0 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S0 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S0 s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t24 (HS tm k) d S0) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t25 k d S0) (tsubst_shift0_Tm_comm_ind t26 k d S0))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t24 (HS ty k) d S0) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t24 k d S0) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (tsubst_shift0_Tm_comm_ind t24 k d S0) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (tsubst_shift0_Tm_comm_ind t25 k d S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t26 (HS tm (HS ty k)) d S0) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d) k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S0 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d) k) S0 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S0 s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T33 k d S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t24 (HS tm k) d S0) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t25 k d S0) (tsubst_tshift0_Tm_comm_ind t26 k d S0))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t24 (HS ty k) d S0) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t24 k d S0) (tsubst_tshift0_Ty_comm_ind T33 k d S0))
        | (pack T34 t24 T35) => (f_equal3 pack (tsubst_tshift0_Ty_comm_ind T34 k d S0) (tsubst_tshift0_Tm_comm_ind t24 k d S0) (tsubst_tshift0_Ty_comm_ind T35 k d S0))
        | (unpack t25 t26) => (f_equal2 unpack (tsubst_tshift0_Tm_comm_ind t25 k d S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t26 (HS tm (HS ty k)) d S0) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
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
        | (tvar X23) => (tsubstIndex_shiftTy0_comm_ind d S0 k X23)
        | (tarr T34 T35) => (f_equal2 tarr (tsubst_tm_Ty_ind T34 k d S0) (tsubst_tm_Ty_ind T35 k d S0))
        | (tall T33) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T33 (HS ty k) d S0) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (texist T33) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T33 (HS ty k) d S0) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d) k) S0 s) = (tsubstTm (weakenTrace d k) S0 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d) k) S0 s) = (tsubstTm (weakenTrace d k) S0 s)) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs (tsubst_tm_Ty_ind T33 k d S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t24 (HS tm k) d S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl))))
        | (app t25 t26) => (f_equal2 app (tsubst_tm_Tm_ind t25 k d S0) (tsubst_tm_Tm_ind t26 k d S0))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t24 (HS ty k) d S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t24 T33) => (f_equal2 tapp (tsubst_tm_Tm_ind t24 k d S0) (tsubst_tm_Ty_ind T33 k d S0))
        | (pack T34 t24 T35) => (f_equal3 pack (tsubst_tm_Ty_ind T34 k d S0) (tsubst_tm_Tm_ind t24 k d S0) (tsubst_tm_Ty_ind T35 k d S0))
        | (unpack t25 t26) => (f_equal2 unpack (tsubst_tm_Tm_ind t25 k d S0) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t26 (HS tm (HS ty k)) d S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm (HS ty H0)))) eq_refl eq_refl))))
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
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substTm (weakenTrace d k) s (substIndex (weakenTrace X0 k) s0 x13)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substIndex (weakenTrace (XS tm d) k) s x13)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d : (Trace ty)) (S0 : Ty) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((tsubstTm (weakenTrace d k) S0 (substIndex (weakenTrace X0 k) s x13)) = (substIndex (weakenTrace X0 k) (tsubstTm d S0 s) x13))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d : (Trace ty)) (S0 : Ty) (S1 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tsubstTy (weakenTrace d k) S0 (tsubstIndex (weakenTrace X0 k) S1 X23)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstIndex (weakenTrace (XS ty d) k) S0 X23)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d : (Trace tm)) (s : Tm) (S0 : Ty) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substIndex (weakenTrace d k) s x13) = (tsubstTm (weakenTrace X0 k) S0 (substIndex (weakenTrace (XS ty d) k) s x13)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace d k) S0 (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTy (weakenTrace (XS ty d) k) S0 S2))) :=
      match S2 return ((tsubstTy (weakenTrace d k) S0 (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTy (weakenTrace (XS ty d) k) S0 S2))) with
        | (tvar X23) => (tsubstTy_tsubstIndex0_commright_ind d S0 S1 k X23)
        | (tarr T34 T35) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T34 k d S0 S1) (tsubst_tsubst0_Ty_comm_ind T35 k d S0 S1))
        | (tall T33) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T33 (HS ty k) d S0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (texist T33) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T33 (HS ty k) d S0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x13) => (substTm_substIndex0_commright_ind d s s0 k x13)
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t24 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (subst_subst0_Tm_comm_ind t25 k d s s0) (subst_subst0_Tm_comm_ind t26 k d s s0))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t24 (HS ty k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t24 k d s s0) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (subst_subst0_Tm_comm_ind t24 k d s s0) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (subst_subst0_Tm_comm_ind t25 k d s s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm (HS ty H0))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t26 (HS tm (HS ty k)) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (S0 : Ty) {struct s0} :
    ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S0 s0)) = (tsubstTm (weakenTrace X0 k) S0 (substTm (weakenTrace (XS ty d) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S0 s0)) = (tsubstTm (weakenTrace X0 k) S0 (substTm (weakenTrace (XS ty d) k) s s0))) with
        | (var x13) => (substTy_tsubstIndex0_commleft_ind d s S0 k x13)
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t24 (HS tm k) d s S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t25 k d s S0) (subst_tsubst0_Tm_comm_ind t26 k d s S0))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t24 (HS ty k) d s S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t24 k d s S0) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (subst_tsubst0_Tm_comm_ind t24 k d s S0) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (subst_tsubst0_Tm_comm_ind t25 k d s S0) (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm (HS ty H0))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t26 (HS tm (HS ty k)) d s S0) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d k) S0 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S0 s) (tsubstTm (weakenTrace d k) S0 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d k) S0 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S0 s) (tsubstTm (weakenTrace d k) S0 s0))) with
        | (var x13) => (tsubstTm_substIndex0_commright_ind d S0 s k x13)
        | (abs T33 t24) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t24 (HS tm k) d S0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t25 k d S0 s) (tsubst_subst0_Tm_comm_ind t26 k d S0 s))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t24 (HS ty k) d S0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t24 k d S0 s) eq_refl)
        | (pack T34 t24 T35) => (f_equal3 pack eq_refl (tsubst_subst0_Tm_comm_ind t24 k d S0 s) eq_refl)
        | (unpack t25 t26) => (f_equal2 unpack (tsubst_subst0_Tm_comm_ind t25 k d S0 s) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm (HS ty H0))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t26 (HS tm (HS ty k)) d S0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S0 (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTm (weakenTrace (XS ty d) k) S0 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S0 (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S0 S1) (tsubstTm (weakenTrace (XS ty d) k) S0 s))) with
        | (var x13) => eq_refl
        | (abs T33 t24) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T33 k d S0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t24 (HS tm k) d S0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t25 t26) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t25 k d S0 S1) (tsubst_tsubst0_Tm_comm_ind t26 k d S0 S1))
        | (tabs t24) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t24 (HS ty k) d S0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t24 T33) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t24 k d S0 S1) (tsubst_tsubst0_Ty_comm_ind T33 k d S0 S1))
        | (pack T34 t24 T35) => (f_equal3 pack (tsubst_tsubst0_Ty_comm_ind T34 k d S0 S1) (tsubst_tsubst0_Tm_comm_ind t24 k d S0 S1) (tsubst_tsubst0_Ty_comm_ind T35 k d S0 S1))
        | (unpack t25 t26) => (f_equal2 unpack (tsubst_tsubst0_Tm_comm_ind t25 k d S0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm (HS ty H0))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t26 (HS tm (HS ty k)) d S0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
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
    | wfTy_tvar (X23 : (Index ty))
        (wfi : (wfindex k X23)) :
        (wfTy k (tvar X23))
    | wfTy_tarr {T33 : Ty}
        (wf : (wfTy k T33)) {T34 : Ty}
        (wf0 : (wfTy k T34)) :
        (wfTy k (tarr T33 T34))
    | wfTy_tall {T35 : Ty}
        (wf : (wfTy (HS ty k) T35)) :
        (wfTy k (tall T35))
    | wfTy_texist {T36 : Ty}
        (wf : (wfTy (HS ty k) T36)) :
        (wfTy k (texist T36)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x13 : (Index tm))
        (wfi : (wfindex k x13)) :
        (wfTm k (var x13))
    | wfTm_abs {T33 : Ty}
        (wf : (wfTy k T33)) {t24 : Tm}
        (wf0 : (wfTm (HS tm k) t24)) :
        (wfTm k (abs T33 t24))
    | wfTm_app {t25 : Tm}
        (wf : (wfTm k t25)) {t26 : Tm}
        (wf0 : (wfTm k t26)) :
        (wfTm k (app t25 t26))
    | wfTm_tabs {t27 : Tm}
        (wf : (wfTm (HS ty k) t27)) :
        (wfTm k (tabs t27))
    | wfTm_tapp {t28 : Tm}
        (wf : (wfTm k t28)) {T34 : Ty}
        (wf0 : (wfTy k T34)) :
        (wfTm k (tapp t28 T34))
    | wfTm_pack {T35 : Ty}
        (wf : (wfTy k T35)) {t29 : Tm}
        (wf0 : (wfTm k t29)) {T36 : Ty}
        (wf1 : (wfTy k T36)) :
        (wfTm k (pack T35 t29 T36))
    | wfTm_unpack {t30 : Tm}
        (wf : (wfTm k t30)) {t31 : Tm}
        (wf0 : (wfTm (HS tm (HS ty k)) t31))
        : (wfTm k (unpack t30 t31)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H20 : (wfTy k (tvar X))) : (wfindex k X) := match H20 in (wfTy _ S0) return match S0 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T1) := match H21 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T2) := match H21 in (wfTy _ S1) return match S1 return Prop with
    | (tarr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k1 : Hvl) (T : Ty) (H22 : (wfTy k1 (tall T))) : (wfTy (HS ty k1) T) := match H22 in (wfTy _ S2) return match S2 return Prop with
    | (tall T) => (wfTy (HS ty k1) T)
    | _ => True
  end with
    | (wfTy_tall T H4) => H4
    | _ => I
  end.
  Definition inversion_wfTy_texist_1 (k2 : Hvl) (T : Ty) (H23 : (wfTy k2 (texist T))) : (wfTy (HS ty k2) T) := match H23 in (wfTy _ S3) return match S3 return Prop with
    | (texist T) => (wfTy (HS ty k2) T)
    | _ => True
  end with
    | (wfTy_texist T H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k3 : Hvl) (x : (Index tm)) (H24 : (wfTm k3 (var x))) : (wfindex k3 x) := match H24 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k3 x)
    | _ => True
  end with
    | (wfTm_var x H6) => H6
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k4 : Hvl) (T : Ty) (t : Tm) (H25 : (wfTm k4 (abs T t))) : (wfTy k4 T) := match H25 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k4 T)
    | _ => True
  end with
    | (wfTm_abs T H7 t H8) => H7
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k4 : Hvl) (T : Ty) (t : Tm) (H25 : (wfTm k4 (abs T t))) : (wfTm (HS tm k4) t) := match H25 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k4) t)
    | _ => True
  end with
    | (wfTm_abs T H7 t H8) => H8
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k5 : Hvl) (t1 : Tm) (t2 : Tm) (H26 : (wfTm k5 (app t1 t2))) : (wfTm k5 t1) := match H26 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k5 t1)
    | _ => True
  end with
    | (wfTm_app t1 H9 t2 H10) => H9
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k5 : Hvl) (t1 : Tm) (t2 : Tm) (H26 : (wfTm k5 (app t1 t2))) : (wfTm k5 t2) := match H26 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k5 t2)
    | _ => True
  end with
    | (wfTm_app t1 H9 t2 H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k6 : Hvl) (t : Tm) (H27 : (wfTm k6 (tabs t))) : (wfTm (HS ty k6) t) := match H27 in (wfTm _ s2) return match s2 return Prop with
    | (tabs t) => (wfTm (HS ty k6) t)
    | _ => True
  end with
    | (wfTm_tabs t H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k7 : Hvl) (t : Tm) (T : Ty) (H28 : (wfTm k7 (tapp t T))) : (wfTm k7 t) := match H28 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k7 t)
    | _ => True
  end with
    | (wfTm_tapp t H12 T H13) => H12
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k7 : Hvl) (t : Tm) (T : Ty) (H28 : (wfTm k7 (tapp t T))) : (wfTy k7 T) := match H28 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_tapp t H12 T H13) => H13
    | _ => I
  end.
  Definition inversion_wfTm_pack_0 (k8 : Hvl) (T1 : Ty) (t : Tm) (T2 : Ty) (H29 : (wfTm k8 (pack T1 t T2))) : (wfTy k8 T1) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (pack T1 t T2) => (wfTy k8 T1)
    | _ => True
  end with
    | (wfTm_pack T1 H14 t H15 T2 H16) => H14
    | _ => I
  end.
  Definition inversion_wfTm_pack_1 (k8 : Hvl) (T1 : Ty) (t : Tm) (T2 : Ty) (H29 : (wfTm k8 (pack T1 t T2))) : (wfTm k8 t) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (pack T1 t T2) => (wfTm k8 t)
    | _ => True
  end with
    | (wfTm_pack T1 H14 t H15 T2 H16) => H15
    | _ => I
  end.
  Definition inversion_wfTm_pack_2 (k8 : Hvl) (T1 : Ty) (t : Tm) (T2 : Ty) (H29 : (wfTm k8 (pack T1 t T2))) : (wfTy k8 T2) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (pack T1 t T2) => (wfTy k8 T2)
    | _ => True
  end with
    | (wfTm_pack T1 H14 t H15 T2 H16) => H16
    | _ => I
  end.
  Definition inversion_wfTm_unpack_0 (k9 : Hvl) (t1 : Tm) (t2 : Tm) (H30 : (wfTm k9 (unpack t1 t2))) : (wfTm k9 t1) := match H30 in (wfTm _ s5) return match s5 return Prop with
    | (unpack t1 t2) => (wfTm k9 t1)
    | _ => True
  end with
    | (wfTm_unpack t1 H17 t2 H18) => H17
    | _ => I
  end.
  Definition inversion_wfTm_unpack_3 (k9 : Hvl) (t1 : Tm) (t2 : Tm) (H30 : (wfTm k9 (unpack t1 t2))) : (wfTm (HS tm (HS ty k9)) t2) := match H30 in (wfTm _ s5) return match s5 return Prop with
    | (unpack t1 t2) => (wfTm (HS tm (HS ty k9)) t2)
    | _ => True
  end with
    | (wfTm_unpack t1 H17 t2 H18) => H18
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
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
        (shifthvl_tm c k10 k11) -> (shifthvl_tm (CS c) (HS tm k10) (HS tm k11))
    | shifthvl_tm_there_ty
        (c : (Cutoff tm)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_tm c k10 k11) -> (shifthvl_tm c (HS ty k10) (HS ty k11)).
  Inductive shifthvl_ty : (forall (c : (Cutoff ty)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k10 : Hvl)
        :
        (shifthvl_ty C0 k10 (HS ty k10))
    | shifthvl_ty_there_tm
        (c : (Cutoff ty)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_ty c k10 k11) -> (shifthvl_ty c (HS tm k10) (HS tm k11))
    | shifthvl_ty_there_ty
        (c : (Cutoff ty)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_ty c k10 k11) -> (shifthvl_ty (CS c) (HS ty k10) (HS ty k11)).
  Lemma weaken_shifthvl_tm  :
    (forall (k10 : Hvl) {c : (Cutoff tm)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_tm c k11 k12) -> (shifthvl_tm (weakenCutofftm c k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k10 : Hvl) {c : (Cutoff ty)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_ty c k11 k12) -> (shifthvl_ty (weakenCutoffty c k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) (x13 : (Index tm)) ,
      (wfindex k10 x13) -> (wfindex k11 (shiftIndex c x13))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c : (Cutoff tm)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) (X23 : (Index ty)) ,
      (wfindex k10 X23) -> (wfindex k11 X23)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c : (Cutoff ty)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) (x13 : (Index tm)) ,
      (wfindex k10 x13) -> (wfindex k11 x13)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c : (Cutoff ty)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) (X23 : (Index ty)) ,
      (wfindex k10 X23) -> (wfindex k11 (tshiftIndex c X23))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k10 : Hvl) ,
    (forall (S4 : Ty) (wf : (wfTy k10 S4)) ,
      (forall (c : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c k10 k11) -> (wfTy k11 S4)))) := (ind_wfTy (fun (k10 : Hvl) (S4 : Ty) (wf : (wfTy k10 S4)) =>
    (forall (c : (Cutoff tm)) (k11 : Hvl) ,
      (shifthvl_tm c k10 k11) -> (wfTy k11 S4))) (fun (k10 : Hvl) (X23 : (Index ty)) (wfi : (wfindex k10 X23)) (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTy_tvar k11 _ (shift_wfindex_ty c k10 k11 ins X23 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTy_tarr k11 (IHT1 c k11 (weaken_shifthvl_tm H0 ins)) (IHT2 c k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS ty k10) T)) IHT (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTy_tall k11 (IHT c (HS ty k11) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS ty k10) T)) IHT (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTy_texist k11 (IHT c (HS ty k11) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k10 : Hvl) ,
    (forall (S4 : Ty) (wf : (wfTy k10 S4)) ,
      (forall (c : (Cutoff ty)) (k11 : Hvl) ,
        (shifthvl_ty c k10 k11) -> (wfTy k11 (tshiftTy c S4))))) := (ind_wfTy (fun (k10 : Hvl) (S4 : Ty) (wf : (wfTy k10 S4)) =>
    (forall (c : (Cutoff ty)) (k11 : Hvl) ,
      (shifthvl_ty c k10 k11) -> (wfTy k11 (tshiftTy c S4)))) (fun (k10 : Hvl) (X23 : (Index ty)) (wfi : (wfindex k10 X23)) (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTy_tvar k11 _ (tshift_wfindex_ty c k10 k11 ins X23 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTy_tarr k11 (IHT1 c k11 (weaken_shifthvl_ty H0 ins)) (IHT2 c k11 (weaken_shifthvl_ty H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS ty k10) T)) IHT (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTy_tall k11 (IHT (CS c) (HS ty k11) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS ty k10) T)) IHT (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTy_texist k11 (IHT (CS c) (HS ty k11) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k10 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k10 s6)) ,
      (forall (c : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c k10 k11) -> (wfTm k11 (shiftTm c s6))))) := (ind_wfTm (fun (k10 : Hvl) (s6 : Tm) (wf : (wfTm k10 s6)) =>
    (forall (c : (Cutoff tm)) (k11 : Hvl) ,
      (shifthvl_tm c k10 k11) -> (wfTm k11 (shiftTm c s6)))) (fun (k10 : Hvl) (x13 : (Index tm)) (wfi : (wfindex k10 x13)) (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_var k11 _ (shift_wfindex_tm c k10 k11 ins x13 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS tm k10) t)) IHt (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_abs k11 (shift_wfTy k10 T wf c k11 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k11) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_app k11 (IHt1 c k11 (weaken_shifthvl_tm H0 ins)) (IHt2 c k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm (HS ty k10) t)) IHt (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_tabs k11 (IHt c (HS ty k11) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (T : Ty) (wf0 : (wfTy k10 T)) (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_tapp k11 (IHt c k11 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k10 T wf0 c k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) (t : Tm) (wf0 : (wfTm k10 t)) IHt (T2 : Ty) (wf1 : (wfTy k10 T2)) (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_pack k11 (shift_wfTy k10 T1 wf c k11 (weaken_shifthvl_tm H0 ins)) (IHt c k11 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k10 T2 wf1 c k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm (HS tm (HS ty k10)) t2)) IHt2 (c : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c k10 k11)) =>
    (wfTm_unpack k11 (IHt1 c k11 (weaken_shifthvl_tm H0 ins)) (IHt2 (CS c) (HS tm (HS ty k11)) (weaken_shifthvl_tm (HS tm (HS ty H0)) ins))))).
  Definition tshift_wfTm : (forall (k10 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k10 s6)) ,
      (forall (c : (Cutoff ty)) (k11 : Hvl) ,
        (shifthvl_ty c k10 k11) -> (wfTm k11 (tshiftTm c s6))))) := (ind_wfTm (fun (k10 : Hvl) (s6 : Tm) (wf : (wfTm k10 s6)) =>
    (forall (c : (Cutoff ty)) (k11 : Hvl) ,
      (shifthvl_ty c k10 k11) -> (wfTm k11 (tshiftTm c s6)))) (fun (k10 : Hvl) (x13 : (Index tm)) (wfi : (wfindex k10 x13)) (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTm_var k11 _ (tshift_wfindex_tm c k10 k11 ins x13 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS tm k10) t)) IHt (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTm_abs k11 (tshift_wfTy k10 T wf c k11 (weaken_shifthvl_ty H0 ins)) (IHt c (HS tm k11) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTm_app k11 (IHt1 c k11 (weaken_shifthvl_ty H0 ins)) (IHt2 c k11 (weaken_shifthvl_ty H0 ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm (HS ty k10) t)) IHt (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTm_tabs k11 (IHt (CS c) (HS ty k11) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (T : Ty) (wf0 : (wfTy k10 T)) (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTm_tapp k11 (IHt c k11 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k10 T wf0 c k11 (weaken_shifthvl_ty H0 ins)))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) (t : Tm) (wf0 : (wfTm k10 t)) IHt (T2 : Ty) (wf1 : (wfTy k10 T2)) (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTm_pack k11 (tshift_wfTy k10 T1 wf c k11 (weaken_shifthvl_ty H0 ins)) (IHt c k11 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k10 T2 wf1 c k11 (weaken_shifthvl_ty H0 ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm (HS tm (HS ty k10)) t2)) IHt2 (c : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c k10 k11)) =>
    (wfTm_unpack k11 (IHt1 c k11 (weaken_shifthvl_ty H0 ins)) (IHt2 (CS c) (HS tm (HS ty k11)) (weaken_shifthvl_ty (HS tm (HS ty H0)) ins))))).
  Fixpoint weaken_wfTy (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) ,
    (wfTy (appendHvl k11 k10) (weakenTy S4 k10))) :=
    match k10 return (forall (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) ,
      (wfTy (appendHvl k11 k10) (weakenTy S4 k10))) with
      | (H0) => (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
        wf)
      | (HS tm k10) => (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
        (shift_wfTy (appendHvl k11 k10) (weakenTy S4 k10) (weaken_wfTy k10 k11 S4 wf) C0 (HS tm (appendHvl k11 k10)) (shifthvl_tm_here (appendHvl k11 k10))))
      | (HS ty k10) => (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
        (tshift_wfTy (appendHvl k11 k10) (weakenTy S4 k10) (weaken_wfTy k10 k11 S4 wf) C0 (HS ty (appendHvl k11 k10)) (shifthvl_ty_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfTm (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) ,
    (wfTm (appendHvl k11 k10) (weakenTm s6 k10))) :=
    match k10 return (forall (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) ,
      (wfTm (appendHvl k11 k10) (weakenTm s6 k10))) with
      | (H0) => (fun (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) =>
        wf)
      | (HS tm k10) => (fun (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) =>
        (shift_wfTm (appendHvl k11 k10) (weakenTm s6 k10) (weaken_wfTm k10 k11 s6 wf) C0 (HS tm (appendHvl k11 k10)) (shifthvl_tm_here (appendHvl k11 k10))))
      | (HS ty k10) => (fun (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) =>
        (tshift_wfTm (appendHvl k11 k10) (weakenTm s6 k10) (weaken_wfTm k10 k11 s6 wf) C0 (HS ty (appendHvl k11 k10)) (shifthvl_ty_here (appendHvl k11 k10))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k10 : Hvl) (S4 : Ty) (k11 : Hvl) (S5 : Ty) ,
    (k10 = k11) -> (S4 = S5) -> (wfTy k10 S4) -> (wfTy k11 S5)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k10 : Hvl) (s6 : Tm) (k11 : Hvl) (s7 : Tm) ,
    (k10 = k11) -> (s6 = s7) -> (wfTm k10 s6) -> (wfTm k11 s7)).
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
  Inductive substhvl_tm (k10 : Hvl) : (forall (d : (Trace tm)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k10 X0 (HS tm k10) k10)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_tm k10 d k11 k12) -> (substhvl_tm k10 (XS tm d) (HS tm k11) (HS tm k12))
    | substhvl_tm_there_ty
        {d : (Trace tm)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_tm k10 d k11 k12) -> (substhvl_tm k10 (XS ty d) (HS ty k11) (HS ty k12)).
  Inductive substhvl_ty (k10 : Hvl) : (forall (d : (Trace ty)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k10 X0 (HS ty k10) k10)
    | substhvl_ty_there_tm
        {d : (Trace ty)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_ty k10 d k11 k12) -> (substhvl_ty k10 (XS tm d) (HS tm k11) (HS tm k12))
    | substhvl_ty_there_ty
        {d : (Trace ty)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_ty k10 d k11 k12) -> (substhvl_ty k10 (XS ty d) (HS ty k11) (HS ty k12)).
  Lemma weaken_substhvl_tm  :
    (forall {k11 : Hvl} (k10 : Hvl) {d : (Trace tm)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (substhvl_tm k11 (weakenTrace d k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k11 : Hvl} (k10 : Hvl) {d : (Trace ty)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (substhvl_ty k11 (weakenTrace d k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k10 : Hvl} {s6 : Tm} (wft : (wfTm k10 s6)) :
    (forall {d : (Trace tm)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_tm k10 d k11 k12) -> (forall {x13 : (Index tm)} ,
        (wfindex k11 x13) -> (wfTm k12 (substIndex d s6 x13)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k10 : Hvl} {S4 : Ty} (wft : (wfTy k10 S4)) :
    (forall {d : (Trace ty)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_ty k10 d k11 k12) -> (forall {X23 : (Index ty)} ,
        (wfindex k11 X23) -> (wfTy k12 (tsubstIndex d S4 X23)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k10 : Hvl} :
    (forall {d : (Trace tm)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_tm k10 d k11 k12) -> (forall {X23 : (Index ty)} ,
        (wfindex k11 X23) -> (wfindex k12 X23))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k10 : Hvl} :
    (forall {d : (Trace ty)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_ty k10 d k11 k12) -> (forall {x13 : (Index tm)} ,
        (wfindex k11 x13) -> (wfindex k12 x13))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k10 : Hvl} : (forall (k11 : Hvl) ,
    (forall (S4 : Ty) (wf0 : (wfTy k11 S4)) ,
      (forall {d : (Trace tm)} {k12 : Hvl} ,
        (substhvl_tm k10 d k11 k12) -> (wfTy k12 S4)))) := (ind_wfTy (fun (k11 : Hvl) (S4 : Ty) (wf0 : (wfTy k11 S4)) =>
    (forall {d : (Trace tm)} {k12 : Hvl} ,
      (substhvl_tm k10 d k11 k12) -> (wfTy k12 S4))) (fun (k11 : Hvl) {X23 : (Index ty)} (wfi : (wfindex k11 X23)) {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTy_tvar k12 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k11 : Hvl) (T1 : Ty) (wf0 : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k11 T2)) IHT2 {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTy_tarr k12 (IHT1 (weakenTrace d H0) k12 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k12 (weaken_substhvl_tm H0 del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTy_tall k12 (IHT (weakenTrace d (HS ty H0)) (HS ty k12) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTy_texist k12 (IHT (weakenTrace d (HS ty H0)) (HS ty k12) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k10 : Hvl} {S4 : Ty} (wf : (wfTy k10 S4)) : (forall (k11 : Hvl) ,
    (forall (S5 : Ty) (wf0 : (wfTy k11 S5)) ,
      (forall {d : (Trace ty)} {k12 : Hvl} ,
        (substhvl_ty k10 d k11 k12) -> (wfTy k12 (tsubstTy d S4 S5))))) := (ind_wfTy (fun (k11 : Hvl) (S5 : Ty) (wf0 : (wfTy k11 S5)) =>
    (forall {d : (Trace ty)} {k12 : Hvl} ,
      (substhvl_ty k10 d k11 k12) -> (wfTy k12 (tsubstTy d S4 S5)))) (fun (k11 : Hvl) {X23 : (Index ty)} (wfi : (wfindex k11 X23)) {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k11 : Hvl) (T1 : Ty) (wf0 : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k11 T2)) IHT2 {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTy_tarr k12 (IHT1 (weakenTrace d H0) k12 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k12 (weaken_substhvl_ty H0 del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTy_tall k12 (IHT (weakenTrace d (HS ty H0)) (HS ty k12) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTy_texist k12 (IHT (weakenTrace d (HS ty H0)) (HS ty k12) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k10 : Hvl} {s6 : Tm} (wf : (wfTm k10 s6)) : (forall (k11 : Hvl) ,
    (forall (s7 : Tm) (wf0 : (wfTm k11 s7)) ,
      (forall {d : (Trace tm)} {k12 : Hvl} ,
        (substhvl_tm k10 d k11 k12) -> (wfTm k12 (substTm d s6 s7))))) := (ind_wfTm (fun (k11 : Hvl) (s7 : Tm) (wf0 : (wfTm k11 s7)) =>
    (forall {d : (Trace tm)} {k12 : Hvl} ,
      (substhvl_tm k10 d k11 k12) -> (wfTm k12 (substTm d s6 s7)))) (fun (k11 : Hvl) {x13 : (Index tm)} (wfi : (wfindex k11 x13)) {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) (t : Tm) (wf1 : (wfTm (HS tm k11) t)) IHt {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTm_abs k12 (substhvl_tm_wfTy k11 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k12) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k11 : Hvl) (t1 : Tm) (wf0 : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k11 t2)) IHt2 {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTm_app k12 (IHt1 (weakenTrace d H0) k12 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k12 (weaken_substhvl_tm H0 del)))) (fun (k11 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k11) t)) IHt {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTm_tabs k12 (IHt (weakenTrace d (HS ty H0)) (HS ty k12) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k11 : Hvl) (t : Tm) (wf0 : (wfTm k11 t)) IHt (T : Ty) (wf1 : (wfTy k11 T)) {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTm_tapp k12 (IHt (weakenTrace d H0) k12 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k11 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k11 : Hvl) (T1 : Ty) (wf0 : (wfTy k11 T1)) (t : Tm) (wf1 : (wfTm k11 t)) IHt (T2 : Ty) (wf2 : (wfTy k11 T2)) {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTm_pack k12 (substhvl_tm_wfTy k11 T1 wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d H0) k12 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k11 T2 wf2 (weaken_substhvl_tm H0 del)))) (fun (k11 : Hvl) (t1 : Tm) (wf0 : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (HS tm (HS ty k11)) t2)) IHt2 {d : (Trace tm)} {k12 : Hvl} (del : (substhvl_tm k10 d k11 k12)) =>
    (wfTm_unpack k12 (IHt1 (weakenTrace d H0) k12 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d (HS tm (HS ty H0))) (HS tm (HS ty k12)) (weaken_substhvl_tm (HS tm (HS ty H0)) del))))).
  Definition substhvl_ty_wfTm {k10 : Hvl} {S4 : Ty} (wf : (wfTy k10 S4)) : (forall (k11 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k11 s6)) ,
      (forall {d : (Trace ty)} {k12 : Hvl} ,
        (substhvl_ty k10 d k11 k12) -> (wfTm k12 (tsubstTm d S4 s6))))) := (ind_wfTm (fun (k11 : Hvl) (s6 : Tm) (wf0 : (wfTm k11 s6)) =>
    (forall {d : (Trace ty)} {k12 : Hvl} ,
      (substhvl_ty k10 d k11 k12) -> (wfTm k12 (tsubstTm d S4 s6)))) (fun (k11 : Hvl) {x13 : (Index tm)} (wfi : (wfindex k11 x13)) {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTm_var k12 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) (t : Tm) (wf1 : (wfTm (HS tm k11) t)) IHt {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTm_abs k12 (substhvl_ty_wfTy wf k11 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k12) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k11 : Hvl) (t1 : Tm) (wf0 : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k11 t2)) IHt2 {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTm_app k12 (IHt1 (weakenTrace d H0) k12 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d H0) k12 (weaken_substhvl_ty H0 del)))) (fun (k11 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k11) t)) IHt {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTm_tabs k12 (IHt (weakenTrace d (HS ty H0)) (HS ty k12) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k11 : Hvl) (t : Tm) (wf0 : (wfTm k11 t)) IHt (T : Ty) (wf1 : (wfTy k11 T)) {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTm_tapp k12 (IHt (weakenTrace d H0) k12 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k11 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k11 : Hvl) (T1 : Ty) (wf0 : (wfTy k11 T1)) (t : Tm) (wf1 : (wfTm k11 t)) IHt (T2 : Ty) (wf2 : (wfTy k11 T2)) {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTm_pack k12 (substhvl_ty_wfTy wf k11 T1 wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d H0) k12 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k11 T2 wf2 (weaken_substhvl_ty H0 del)))) (fun (k11 : Hvl) (t1 : Tm) (wf0 : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (HS tm (HS ty k11)) t2)) IHt2 {d : (Trace ty)} {k12 : Hvl} (del : (substhvl_ty k10 d k11 k12)) =>
    (wfTm_unpack k12 (IHt1 (weakenTrace d H0) k12 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d (HS tm (HS ty H0))) (HS tm (HS ty k12)) (weaken_substhvl_ty (HS tm (HS ty H0)) del))))).
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
  Fixpoint weakenEnv (G : Env) (k10 : Hvl) {struct k10} :
  Env :=
    match k10 with
      | (H0) => G
      | (HS tm k10) => (weakenEnv G k10)
      | (HS ty k10) => (tshiftEnv C0 (weakenEnv G k10))
    end.
  Fixpoint substEnv (d : (Trace tm)) (s6 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s6 G0) T)
      | (etvar G0) => (etvar (substEnv d s6 G0))
    end.
  Fixpoint tsubstEnv (d : (Trace ty)) (S4 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d S4 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S4 T))
      | (etvar G0) => (etvar (tsubstEnv d S4 G0))
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
    (forall (d : (Trace tm)) (s6 : Tm) (G : Env) ,
      ((domainEnv (substEnv d s6 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d : (Trace ty)) (S4 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d S4 G)) = (domainEnv G))).
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
      (forall (d : (Trace tm)) (s6 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d s6 (appendEnv G G0)) = (appendEnv (substEnv d s6 G) (substEnv (weakenTrace d (domainEnv G)) s6 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d : (Trace ty)) (S4 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d S4 (appendEnv G G0)) = (appendEnv (tsubstEnv d S4 G) (tsubstEnv (weakenTrace d (domainEnv G)) S4 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S4 : Ty) (k10 : Hvl) (k11 : Hvl) ,
      ((weakenTy (weakenTy S4 k10) k11) = (weakenTy S4 (appendHvl k10 k11)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s6 : Tm) (k10 : Hvl) (k11 : Hvl) ,
      ((weakenTm (weakenTm s6 k10) k11) = (weakenTm s6 (appendHvl k10 k11)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T33 : Ty) :
          (wfTy (domainEnv G) T33) -> (lookup_evar (evar G T33) I0 T33)
      | lookup_evar_there_evar
          {G : Env} {x13 : (Index tm)}
          (T34 : Ty) (T35 : Ty) :
          (lookup_evar G x13 T34) -> (lookup_evar (evar G T35) (IS x13) T34)
      | lookup_evar_there_etvar
          {G : Env} {x13 : (Index tm)}
          (T34 : Ty) :
          (lookup_evar G x13 T34) -> (lookup_evar (etvar G) x13 (tshiftTy C0 T34)).
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G : Env}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Env} {X23 : (Index ty)}
          (T34 : Ty) :
          (lookup_etvar G X23) -> (lookup_etvar (evar G T34) X23)
      | lookup_etvar_there_etvar
          {G : Env} {X23 : (Index ty)} :
          (lookup_etvar G X23) -> (lookup_etvar (etvar G) (IS X23)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T34 : Ty) (T35 : Ty) ,
        (lookup_evar (evar G T34) I0 T35) -> (T34 = T35)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x13 : (Index tm)} ,
        (forall (T34 : Ty) ,
          (lookup_evar G x13 T34) -> (forall (T35 : Ty) ,
            (lookup_evar G x13 T35) -> (T34 = T35)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x13 : (Index tm)} (T34 : Ty) ,
        (lookup_evar G x13 T34) -> (wfTy (domainEnv G) T34)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x13 : (Index tm)} (T34 : Ty) ,
        (lookup_evar G x13 T34) -> (lookup_evar (appendEnv G G0) (weakenIndextm x13 (domainEnv G0)) (weakenTy T34 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X23 : (Index ty)} ,
        (lookup_etvar G X23) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X23 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x13 : (Index tm)} (T36 : Ty) ,
        (lookup_evar G x13 T36) -> (wfindex (domainEnv G) x13)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X23 : (Index ty)} ,
        (lookup_etvar G X23) -> (wfindex (domainEnv G) X23)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T34 : Ty} :
        (shift_evar C0 G (evar G T34))
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
  Inductive subst_evar (G : Env) (T34 : Ty) (s6 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T34 s6 X0 (evar G T34) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T35 : Ty) :
        (subst_evar G T34 s6 d G0 G1) -> (subst_evar G T34 s6 (XS tm d) (evar G0 T35) (evar G1 T35))
    | subst_evar_there_etvar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} :
        (subst_evar G T34 s6 d G0 G1) -> (subst_evar G T34 s6 (XS ty d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Env} (T34 : Ty) {s6 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T34 s6 d G1 G2) -> (subst_evar G T34 s6 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (S4 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S4 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T34 : Ty) :
        (subst_etvar G S4 d G0 G1) -> (subst_etvar G S4 (XS tm d) (evar G0 T34) (evar G1 (tsubstTy d S4 T34)))
    | subst_etvar_there_etvar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} :
        (subst_etvar G S4 d G0 G1) -> (subst_etvar G S4 (XS ty d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_etvar {G : Env} {S4 : Ty} :
    (forall (G0 : Env) {d : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G S4 d G1 G2) -> (subst_etvar G S4 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d S4 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s6 : Tm} (T34 : Ty) :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T34 s6 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S4 : Ty} :
    (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G S4 d G0 G1) -> (substhvl_ty (domainEnv G) d (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T34 : Ty} (wf : (wfTy (domainEnv G) T34)) ,
    (lookup_evar (appendEnv (evar G T34) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T34 (domainEnv G0)))).
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
  | H34 : (wfTy _ (tvar _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTy _ (tarr _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTy _ (tall _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTy _ (texist _)) |- _ => inversion H34; subst; clear H34
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H34 : (wfTm _ (var _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (abs _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (app _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (tabs _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (tapp _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (pack _ _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (unpack _ _)) |- _ => inversion H34; subst; clear H34
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
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x13 : (Index tm)} {T34 : Ty} ,
    (lookup_evar G x13 T34) -> (lookup_evar G0 (shiftIndex c x13) T34)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X23 : (Index ty)} ,
    (lookup_etvar G X23) -> (lookup_etvar G0 X23)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x13 : (Index tm)} {T34 : Ty} ,
    (lookup_evar G x13 T34) -> (lookup_evar G0 x13 (tshiftTy c T34))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X23 : (Index ty)} ,
    (lookup_etvar G X23) -> (lookup_etvar G0 (tshiftIndex c X23))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T35 : Ty) {s6 : Tm} :
  (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T35 s6 d G0 G1)) {X23 : (Index ty)} ,
    (lookup_etvar G0 X23) -> (lookup_etvar G1 X23)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {S4 : Ty} (wf : (wfTy (domainEnv G) S4)) :
  (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G S4 d G0 G1)) {x13 : (Index tm)} (T35 : Ty) ,
    (lookup_evar G0 x13 T35) -> (lookup_evar G1 x13 (tsubstTy d S4 T35))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (tvar X23) => 1
    | (tarr T33 T34) => (plus 1 (plus (size_Ty T33) (size_Ty T34)))
    | (tall T35) => (plus 1 (size_Ty T35))
    | (texist T36) => (plus 1 (size_Ty T36))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x13) => 1
    | (abs T33 t24) => (plus 1 (plus (size_Ty T33) (size_Tm t24)))
    | (app t25 t26) => (plus 1 (plus (size_Tm t25) (size_Tm t26)))
    | (tabs t27) => (plus 1 (size_Tm t27))
    | (tapp t28 T34) => (plus 1 (plus (size_Tm t28) (size_Ty T34)))
    | (pack T35 t29 T36) => (plus 1 (plus (size_Ty T35) (plus (size_Tm t29) (size_Ty T36))))
    | (unpack t30 t31) => (plus 1 (plus (size_Tm t30) (size_Tm t31)))
  end.
Fixpoint tshift_size_Ty (S0 : Ty) (c : (Cutoff ty)) {struct S0} :
((size_Ty (tshiftTy c S0)) = (size_Ty S0)) :=
  match S0 return ((size_Ty (tshiftTy c S0)) = (size_Ty S0)) with
    | (tvar _) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tall T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c)))
    | (texist T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c)))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (tabs t) => (f_equal2 plus eq_refl (shift_size_Tm t c))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c) eq_refl))
    | (pack T1 t T2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c) eq_refl)))
    | (unpack t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 (CS c))))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
    | (tabs t) => (f_equal2 plus eq_refl (tshift_size_Tm t (CS c)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c) (tshift_size_Ty T c)))
    | (pack T1 t T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (f_equal2 plus (tshift_size_Tm t c) (tshift_size_Ty T2 c))))
    | (unpack t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 (CS c))))
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
      (H22 : (wfTy (domainEnv G) T))
      (H23 : (wfindex (domainEnv G) x))
      : (Typing G (var x) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G T1) t (weakenTy T2 (HS tm H0))))
      (H24 : (wfTy (domainEnv G) T1))
      (H25 : (wfTy (domainEnv G) T2))
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
      (H34 : (wfTy (domainEnv G) T2))
      :
      (Typing G (tapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Pack (T2 : Ty) (U : Ty)
      (t2 : Tm)
      (jm4 : (Typing G t2 (tsubstTy X0 U T2)))
      (H36 : (wfTy (HS ty (domainEnv G)) T2))
      (H37 : (wfTy (domainEnv G) U)) :
      (Typing G (pack U t2 (texist T2)) (texist T2))
  | T_Unpack (T12 : Ty) (T2 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm5 : (Typing G t1 (texist T12)))
      (jm6 : (Typing (evar (etvar G) T12) t2 (weakenTy T2 (HS tm (HS ty H0)))))
      (H40 : (wfTy (domainEnv G) T2))
      : (Typing G (unpack t1 t2) T2).
Lemma Typing_cast  :
  (forall (G : Env) (t24 : Tm) (T36 : Ty) (G0 : Env) (t25 : Tm) (T37 : Ty) ,
    (G = G0) -> (t24 = t25) -> (T36 = T37) -> (Typing G t24 T36) -> (Typing G0 t25 T37)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_Typing (G1 : Env) (t28 : Tm) (T43 : Ty) (jm16 : (Typing G1 t28 T43)) :
(forall (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) ,
  (Typing G2 (shiftTm c t28) T43)) :=
  match jm16 in (Typing _ t28 T43) return (forall (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) ,
    (Typing G2 (shiftTm c t28) T43)) with
    | (T_Var T38 x14 lk0 H37 H38) => (fun (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) =>
      (T_Var G2 T38 (shiftIndex c x14) (shift_evar_lookup_evar H60 lk0) (shift_wfTy _ _ H37 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H60))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H60)) _ H38)))
    | (T_Abs T39 T42 t25 jm8 H39 H40) => (fun (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) =>
      (T_Abs G2 T39 T42 (shiftTm (CS c) t25) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G1 T39) t25 (weakenTy T42 (HS tm H0)) jm8 (CS c) (evar G2 T39) (weaken_shift_evar (evar empty T39) H60))) (shift_wfTy _ _ H39 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H60))) (shift_wfTy _ _ H40 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H60)))))
    | (T_App T40 T41 t26 t27 jm9 jm10) => (fun (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) =>
      (T_App G2 T40 T41 (shiftTm c t26) (shiftTm c t27) (shift_evar_Typing G1 t26 (tarr T40 T41) jm9 c G2 (weaken_shift_evar empty H60)) (shift_evar_Typing G1 t27 T40 jm10 c G2 (weaken_shift_evar empty H60))))
    | (T_Tabs T38 t25 jm11) => (fun (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) =>
      (T_Tabs G2 T38 (shiftTm c t25) (shift_evar_Typing (etvar G1) t25 T38 jm11 c (etvar G2) (weaken_shift_evar (etvar empty) H60))))
    | (T_Tapp T41 T42 t26 jm12 H49) => (fun (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) =>
      (T_Tapp G2 T41 T42 (shiftTm c t26) (shift_evar_Typing G1 t26 (tall T41) jm12 c G2 (weaken_shift_evar empty H60)) (shift_wfTy _ _ H49 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H60)))))
    | (T_Pack T42 U1 t27 jm13 H51 H52) => (fun (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) =>
      (T_Pack G2 T42 U1 (shiftTm c t27) (shift_evar_Typing G1 t27 (tsubstTy X0 U1 T42) jm13 c G2 (weaken_shift_evar empty H60)) (shift_wfTy _ _ H51 _ _ (weaken_shifthvl_tm (HS ty H0) (shift_evar_shifthvl_tm H60))) (shift_wfTy _ _ H52 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H60)))))
    | (T_Unpack T41 T42 t26 t27 jm14 jm15 H55) => (fun (c : (Cutoff tm)) (G2 : Env) (H60 : (shift_evar c G1 G2)) =>
      (T_Unpack G2 T41 T42 (shiftTm c t26) (shiftTm (CS c) t27) (shift_evar_Typing G1 t26 (texist T41) jm14 c G2 (weaken_shift_evar empty H60)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar (etvar G1) T41) t27 (weakenTy T42 (HS tm (HS ty H0))) jm15 (CS c) (evar (etvar G2) T41) (weaken_shift_evar (evar (etvar empty) T41) H60))) (shift_wfTy _ _ H55 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H60)))))
  end.
Fixpoint shift_etvar_Typing (G1 : Env) (t28 : Tm) (T43 : Ty) (jm16 : (Typing G1 t28 T43)) :
(forall (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) ,
  (Typing G2 (tshiftTm c t28) (tshiftTy c T43))) :=
  match jm16 in (Typing _ t28 T43) return (forall (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) ,
    (Typing G2 (tshiftTm c t28) (tshiftTy c T43))) with
    | (T_Var T38 x14 lk0 H37 H38) => (fun (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) =>
      (T_Var G2 (tshiftTy c T38) x14 (shift_etvar_lookup_evar H60 lk0) (tshift_wfTy _ _ H37 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H60))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H60)) _ H38)))
    | (T_Abs T39 T42 t25 jm8 H39 H40) => (fun (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) =>
      (T_Abs G2 (tshiftTy c T39) (tshiftTy c T42) (tshiftTm c t25) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c T42)) (shift_etvar_Typing (evar G1 T39) t25 (weakenTy T42 (HS tm H0)) jm8 c (evar G2 (tshiftTy c T39)) (weaken_shift_etvar (evar empty T39) H60))) (tshift_wfTy _ _ H39 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H60))) (tshift_wfTy _ _ H40 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H60)))))
    | (T_App T40 T41 t26 t27 jm9 jm10) => (fun (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) =>
      (T_App G2 (tshiftTy c T40) (tshiftTy c T41) (tshiftTm c t26) (tshiftTm c t27) (shift_etvar_Typing G1 t26 (tarr T40 T41) jm9 c G2 (weaken_shift_etvar empty H60)) (shift_etvar_Typing G1 t27 T40 jm10 c G2 (weaken_shift_etvar empty H60))))
    | (T_Tabs T38 t25 jm11) => (fun (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) =>
      (T_Tabs G2 (tshiftTy (CS c) T38) (tshiftTm (CS c) t25) (shift_etvar_Typing (etvar G1) t25 T38 jm11 (CS c) (etvar G2) (weaken_shift_etvar (etvar empty) H60))))
    | (T_Tapp T41 T42 t26 jm12 H49) => (fun (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) =>
      (Typing_cast G2 _ _ G2 (tshiftTm c (tapp t26 T42)) (tshiftTy c (tsubstTy X0 T42 T41)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T41 c T42)) (T_Tapp G2 (tshiftTy (CS c) T41) (tshiftTy c T42) (tshiftTm c t26) (shift_etvar_Typing G1 t26 (tall T41) jm12 c G2 (weaken_shift_etvar empty H60)) (tshift_wfTy _ _ H49 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H60))))))
    | (T_Pack T42 U1 t27 jm13 H51 H52) => (fun (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) =>
      (T_Pack G2 (tshiftTy (CS c) T42) (tshiftTy c U1) (tshiftTm c t27) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (tshiftTy_tsubstTy0_comm T42 c U1) (shift_etvar_Typing G1 t27 (tsubstTy X0 U1 T42) jm13 c G2 (weaken_shift_etvar empty H60))) (tshift_wfTy _ _ H51 _ _ (weaken_shifthvl_ty (HS ty H0) (shift_etvar_shifthvl_ty H60))) (tshift_wfTy _ _ H52 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H60)))))
    | (T_Unpack T41 T42 t26 t27 jm14 jm15 H55) => (fun (c : (Cutoff ty)) (G2 : Env) (H60 : (shift_etvar c G1 G2)) =>
      (T_Unpack G2 (tshiftTy (CS c) T41) (tshiftTy c T42) (tshiftTm c t26) (tshiftTm (CS c) t27) (shift_etvar_Typing G1 t26 (texist T41) jm14 c G2 (weaken_shift_etvar empty H60)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm (HS ty H0)) c T42)) (shift_etvar_Typing (evar (etvar G1) T41) t27 (weakenTy T42 (HS tm (HS ty H0))) jm15 (CS c) (evar (etvar G2) (tshiftTy (CS c) T41)) (weaken_shift_etvar (evar (etvar empty) T41) H60))) (tshift_wfTy _ _ H55 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H60)))))
  end.
 Hint Resolve shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_Typing (G : Env) :
(forall (G0 : Env) (t24 : Tm) (T36 : Ty) (jm7 : (Typing G0 t24 T36)) ,
  (Typing (appendEnv G0 G) (weakenTm t24 (domainEnv G)) (weakenTy T36 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (t24 : Tm) (T36 : Ty) (jm7 : (Typing G0 t24 T36)) ,
    (Typing (appendEnv G0 G) (weakenTm t24 (domainEnv G)) (weakenTy T36 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (t24 : Tm) (T36 : Ty) (jm7 : (Typing G0 t24 T36)) =>
      jm7)
    | (evar G T37) => (fun (G0 : Env) (t24 : Tm) (T36 : Ty) (jm7 : (Typing G0 t24 T36)) =>
      (shift_evar_Typing (appendEnv G0 G) (weakenTm t24 (domainEnv G)) (weakenTy T36 (domainEnv G)) (weaken_Typing G G0 t24 T36 jm7) C0 (evar (appendEnv G0 G) T37) shift_evar_here))
    | (etvar G) => (fun (G0 : Env) (t24 : Tm) (T36 : Ty) (jm7 : (Typing G0 t24 T36)) =>
      (shift_etvar_Typing (appendEnv G0 G) (weakenTm t24 (domainEnv G)) (weakenTy T36 (domainEnv G)) (weaken_Typing G G0 t24 T36 jm7) C0 (etvar (appendEnv G0 G)) shift_etvar_here))
  end.
Fixpoint Typing_wf_0 (G : Env) (t25 : Tm) (T38 : Ty) (jm8 : (Typing G t25 T38)) {struct jm8} :
(wfTm (domainEnv G) t25) :=
  match jm8 in (Typing _ t25 T38) return (wfTm (domainEnv G) t25) with
    | (T_Var T x lk0 H22 H23) => (wfTm_var (domainEnv G) _ H23)
    | (T_Abs T1 T2 t jm H24 H25) => (wfTm_abs (domainEnv G) H24 (Typing_wf_0 (evar G T1) t (weakenTy T2 (HS tm H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tarr T11 T12) jm0) (Typing_wf_0 G t2 T11 jm1))
    | (T_Tabs T t jm2) => (wfTm_tabs (domainEnv G) (Typing_wf_0 (etvar G) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H34) => (wfTm_tapp (domainEnv G) (Typing_wf_0 G t1 (tall T12) jm3) H34)
    | (T_Pack T2 U t2 jm4 H36 H37) => (wfTm_pack (domainEnv G) H37 (Typing_wf_0 G t2 (tsubstTy X0 U T2) jm4) (wfTy_texist (domainEnv G) H36))
    | (T_Unpack T12 T2 t1 t2 jm5 jm6 H40) => (wfTm_unpack (domainEnv G) (Typing_wf_0 G t1 (texist T12) jm5) (Typing_wf_0 (evar (etvar G) T12) t2 (weakenTy T2 (HS tm (HS ty H0))) jm6))
  end
with Typing_wf_1 (G : Env) (t25 : Tm) (T38 : Ty) (jm9 : (Typing G t25 T38)) {struct jm9} :
(wfTy (domainEnv G) T38) :=
  match jm9 in (Typing _ t25 T38) return (wfTy (domainEnv G) T38) with
    | (T_Var T x lk1 H22 H23) => H22
    | (T_Abs T1 T2 t jm H24 H25) => (wfTy_tarr (domainEnv G) H24 H25)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_tarr_1 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tarr T11 T12) jm0))
    | (T_Tabs T t jm2) => (wfTy_tall (domainEnv G) (Typing_wf_1 (etvar G) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H34) => (substhvl_ty_wfTy H34 (HS ty (domainEnv G)) T12 (inversion_wfTy_tall_1 (domainEnv G) T12 (Typing_wf_1 G t1 (tall T12) jm3)) (substhvl_ty_here (domainEnv G)))
    | (T_Pack T2 U t2 jm4 H36 H37) => (wfTy_texist (domainEnv G) H36)
    | (T_Unpack T12 T2 t1 t2 jm5 jm6 H40) => H40
  end.
 Hint Extern 8 => match goal with
  | H39 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H39)); pose proof ((Typing_wf_1 _ _ _ H39)); clear H39
end : wf.
Lemma subst_evar_lookup_evar (G1 : Env) (s6 : Tm) (T39 : Ty) (jm10 : (Typing G1 s6 T39)) :
  (forall (d : (Trace tm)) (G2 : Env) (G4 : Env) (sub : (subst_evar G1 T39 s6 d G2 G4)) (x14 : (Index tm)) (T40 : Ty) ,
    (lookup_evar G2 x14 T40) -> (Typing G4 (substIndex d s6 x14) T40)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Fixpoint subst_evar_Typing (G2 : Env) (s6 : Tm) (T39 : Ty) (jm18 : (Typing G2 s6 T39)) (G1 : Env) (t : Tm) (T : Ty) (jm19 : (Typing G1 t T)) :
(forall (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) ,
  (Typing G3 (substTm d s6 t) T)) :=
  match jm19 in (Typing _ t T) return (forall (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) ,
    (Typing G3 (substTm d s6 t) T)) with
    | (T_Var T40 x14 lk2 H41 H42) => (fun (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) =>
      (subst_evar_lookup_evar G2 s6 T39 jm18 d G1 G3 H62 x14 T40 lk2))
    | (T_Abs T41 T44 t26 jm10 H43 H44) => (fun (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) =>
      (T_Abs G3 T41 T44 (substTm (weakenTrace d (HS tm H0)) s6 t26) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G2 s6 T39 jm18 (evar G1 T41) t26 (weakenTy T44 (HS tm H0)) jm10 (appendEnv G3 (evar empty T41)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T41) H62))) (substhvl_tm_wfTy _ _ H43 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62))) (substhvl_tm_wfTy _ _ H44 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62)))))
    | (T_App T42 T43 t27 t28 jm11 jm12) => (fun (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) =>
      (T_App G3 T42 T43 (substTm (weakenTrace d H0) s6 t27) (substTm (weakenTrace d H0) s6 t28) (subst_evar_Typing G2 s6 T39 jm18 G1 t27 (tarr T42 T43) jm11 G3 d (weaken_subst_evar _ empty H62)) (subst_evar_Typing G2 s6 T39 jm18 G1 t28 T42 jm12 G3 d (weaken_subst_evar _ empty H62))))
    | (T_Tabs T40 t26 jm13) => (fun (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) =>
      (T_Tabs G3 T40 (substTm (weakenTrace d (HS ty H0)) s6 t26) (subst_evar_Typing G2 s6 T39 jm18 (etvar G1) t26 T40 jm13 (appendEnv G3 (etvar empty)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty) H62))))
    | (T_Tapp T43 T44 t27 jm14 H53) => (fun (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) =>
      (T_Tapp G3 T43 T44 (substTm (weakenTrace d H0) s6 t27) (subst_evar_Typing G2 s6 T39 jm18 G1 t27 (tall T43) jm14 G3 d (weaken_subst_evar _ empty H62)) (substhvl_tm_wfTy _ _ H53 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62)))))
    | (T_Pack T44 U1 t28 jm15 H55 H56) => (fun (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) =>
      (T_Pack G3 T44 U1 (substTm (weakenTrace d H0) s6 t28) (subst_evar_Typing G2 s6 T39 jm18 G1 t28 (tsubstTy X0 U1 T44) jm15 G3 d (weaken_subst_evar _ empty H62)) (substhvl_tm_wfTy _ _ H55 (weaken_substhvl_tm (HS ty H0) (subst_evar_substhvl_tm _ H62))) (substhvl_tm_wfTy _ _ H56 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62)))))
    | (T_Unpack T43 T44 t27 t28 jm16 jm17 H59) => (fun (G3 : Env) (d : (Trace tm)) (H62 : (subst_evar G2 T39 s6 d G1 G3)) =>
      (T_Unpack G3 T43 T44 (substTm (weakenTrace d H0) s6 t27) (substTm (weakenTrace d (HS tm (HS ty H0))) s6 t28) (subst_evar_Typing G2 s6 T39 jm18 G1 t27 (texist T43) jm16 G3 d (weaken_subst_evar _ empty H62)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G2 s6 T39 jm18 (evar (etvar G1) T43) t28 (weakenTy T44 (HS tm (HS ty H0))) jm17 (appendEnv G3 (evar (etvar empty) T43)) (weakenTrace d (HS tm (HS ty H0))) (weaken_subst_evar _ (evar (etvar empty) T43) H62))) (substhvl_tm_wfTy _ _ H59 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62)))))
  end.
Fixpoint subst_etvar_Typing (G2 : Env) (S4 : Ty) (H62 : (wfTy (domainEnv G2) S4)) (G1 : Env) (t : Tm) (T : Ty) (jm18 : (Typing G1 t T)) :
(forall (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) ,
  (Typing G3 (tsubstTm d S4 t) (tsubstTy d S4 T))) :=
  match jm18 in (Typing _ t T) return (forall (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) ,
    (Typing G3 (tsubstTm d S4 t) (tsubstTy d S4 T))) with
    | (T_Var T40 x14 lk2 H41 H42) => (fun (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) =>
      (T_Var G3 (tsubstTy (weakenTrace d H0) S4 T40) x14 (subst_etvar_lookup_evar H62 H63 T40 lk2) (substhvl_ty_wfTy H62 _ _ H41 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H63))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H63)) H42)))
    | (T_Abs T41 T44 t26 jm10 H43 H44) => (fun (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) =>
      (T_Abs G3 (tsubstTy (weakenTrace d H0) S4 T41) (tsubstTy (weakenTrace d H0) S4 T44) (tsubstTm (weakenTrace d (HS tm H0)) S4 t26) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d S4 T44)) (subst_etvar_Typing G2 S4 H62 (evar G1 T41) t26 (weakenTy T44 (HS tm H0)) jm10 (appendEnv G3 (tsubstEnv d S4 (evar empty T41))) (weakenTrace d (HS tm H0)) (weaken_subst_etvar (evar empty T41) H63))) (substhvl_ty_wfTy H62 _ _ H43 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H63))) (substhvl_ty_wfTy H62 _ _ H44 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H63)))))
    | (T_App T42 T43 t27 t28 jm11 jm12) => (fun (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) =>
      (T_App G3 (tsubstTy (weakenTrace d H0) S4 T42) (tsubstTy (weakenTrace d H0) S4 T43) (tsubstTm (weakenTrace d H0) S4 t27) (tsubstTm (weakenTrace d H0) S4 t28) (subst_etvar_Typing G2 S4 H62 G1 t27 (tarr T42 T43) jm11 G3 d (weaken_subst_etvar empty H63)) (subst_etvar_Typing G2 S4 H62 G1 t28 T42 jm12 G3 d (weaken_subst_etvar empty H63))))
    | (T_Tabs T40 t26 jm13) => (fun (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) =>
      (T_Tabs G3 (tsubstTy (weakenTrace d (HS ty H0)) S4 T40) (tsubstTm (weakenTrace d (HS ty H0)) S4 t26) (subst_etvar_Typing G2 S4 H62 (etvar G1) t26 T40 jm13 (appendEnv G3 (tsubstEnv d S4 (etvar empty))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar (etvar empty) H63))))
    | (T_Tapp T43 T44 t27 jm14 H53) => (fun (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) =>
      (Typing_cast G3 _ _ G3 (tsubstTm d S4 (tapp t27 T44)) (tsubstTy d S4 (tsubstTy X0 T44 T43)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T43 d S4 T44)) (T_Tapp G3 (tsubstTy (weakenTrace d (HS ty H0)) S4 T43) (tsubstTy (weakenTrace d H0) S4 T44) (tsubstTm (weakenTrace d H0) S4 t27) (subst_etvar_Typing G2 S4 H62 G1 t27 (tall T43) jm14 G3 d (weaken_subst_etvar empty H63)) (substhvl_ty_wfTy H62 _ _ H53 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H63))))))
    | (T_Pack T44 U1 t28 jm15 H55 H56) => (fun (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) =>
      (T_Pack G3 (tsubstTy (weakenTrace d (HS ty H0)) S4 T44) (tsubstTy (weakenTrace d H0) S4 U1) (tsubstTm (weakenTrace d H0) S4 t28) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (tsubstTy_tsubstTy0_comm T44 d S4 U1) (subst_etvar_Typing G2 S4 H62 G1 t28 (tsubstTy X0 U1 T44) jm15 G3 d (weaken_subst_etvar empty H63))) (substhvl_ty_wfTy H62 _ _ H55 (weaken_substhvl_ty (HS ty H0) (subst_etvar_substhvl_ty H63))) (substhvl_ty_wfTy H62 _ _ H56 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H63)))))
    | (T_Unpack T43 T44 t27 t28 jm16 jm17 H59) => (fun (G3 : Env) (d : (Trace ty)) (H63 : (subst_etvar G2 S4 d G1 G3)) =>
      (T_Unpack G3 (tsubstTy (weakenTrace d (HS ty H0)) S4 T43) (tsubstTy (weakenTrace d H0) S4 T44) (tsubstTm (weakenTrace d H0) S4 t27) (tsubstTm (weakenTrace d (HS tm (HS ty H0))) S4 t28) (subst_etvar_Typing G2 S4 H62 G1 t27 (texist T43) jm16 G3 d (weaken_subst_etvar empty H63)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm (HS ty H0)) d S4 T44)) (subst_etvar_Typing G2 S4 H62 (evar (etvar G1) T43) t28 (weakenTy T44 (HS tm (HS ty H0))) jm17 (appendEnv G3 (tsubstEnv d S4 (evar (etvar empty) T43))) (weakenTrace d (HS tm (HS ty H0))) (weaken_subst_etvar (evar (etvar empty) T43) H63))) (substhvl_ty_wfTy H62 _ _ H59 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H63)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.