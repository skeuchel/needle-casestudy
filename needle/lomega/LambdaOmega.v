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
  
  Fixpoint weakenIndextm (x6 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x6
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x6 k))
        | _ => (weakenIndextm x6 k)
      end
    end.
  Fixpoint weakenIndexty (X29 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X29
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X29 k))
        | _ => (weakenIndexty X29 k)
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x6 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x6 k) k0) = (weakenIndextm x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexty_append  :
    (forall (X29 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X29 k) k0) = (weakenIndexty X29 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Kind : Set :=
    | star 
    | karr (K1 : Kind) (K2 : Kind).
  Scheme ind_Kind := Induction for Kind Sort Prop.
  
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tabs (K : Kind) (T : Ty)
    | tapp (T1 : Ty) (T2 : Ty)
    | tarr (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
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
  Fixpoint shiftIndex (c : (Cutoff tm)) (x6 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x6)
      | (CS c) => match x6 with
        | (I0) => I0
        | (IS x6) => (IS (shiftIndex c x6))
      end
    end.
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X29 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X29)
      | (CS c) => match X29 with
        | (I0) => I0
        | (IS X29) => (IS (tshiftIndex c X29))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S32 : Ty) {struct S32} :
  Ty :=
    match S32 with
      | (tvar X29) => (tvar (tshiftIndex c X29))
      | (tabs K62 T80) => (tabs K62 (tshiftTy (CS c) T80))
      | (tapp T81 T82) => (tapp (tshiftTy c T81) (tshiftTy c T82))
      | (tarr T83 T84) => (tarr (tshiftTy c T83) (tshiftTy c T84))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var (shiftIndex c x6))
      | (abs T80 t11) => (abs T80 (shiftTm (CS c) t11))
      | (app t12 t13) => (app (shiftTm c t12) (shiftTm c t13))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T80 t11) => (abs (tshiftTy c T80) (tshiftTm c t11))
      | (app t12 t13) => (app (tshiftTm c t12) (tshiftTm c t13))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenKind (K62 : Kind) (k : Hvl) {struct k} :
  Kind :=
    match k with
      | (H0) => K62
      | (HS tm k) => (weakenKind K62 k)
      | (HS ty k) => (weakenKind K62 k)
    end.
  Fixpoint weakenTy (S32 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S32
      | (HS tm k) => (weakenTy S32 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S32 k))
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
        (T80 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x6 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x6
      | (HS b k) => (XS b (weakenTrace x6 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x6 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x6 k) k0) = (weakenTrace x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x6 : (Index tm)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x6 with
        | (I0) => s
        | (IS x6) => (var x6)
      end
      | (XS tm d) => match x6 with
        | (I0) => (var I0)
        | (IS x6) => (shiftTm C0 (substIndex d s x6))
      end
      | (XS ty d) => (tshiftTm C0 (substIndex d s x6))
    end.
  Fixpoint tsubstIndex (d : (Trace ty)) (S32 : Ty) (X29 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X29 with
        | (I0) => S32
        | (IS X29) => (tvar X29)
      end
      | (XS tm d) => (tsubstIndex d S32 X29)
      | (XS ty d) => match X29 with
        | (I0) => (tvar I0)
        | (IS X29) => (tshiftTy C0 (tsubstIndex d S32 X29))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct S33} :
  Ty :=
    match S33 with
      | (tvar X29) => (tsubstIndex d S32 X29)
      | (tabs K62 T80) => (tabs K62 (tsubstTy (weakenTrace d (HS ty H0)) S32 T80))
      | (tapp T81 T82) => (tapp (tsubstTy d S32 T81) (tsubstTy d S32 T82))
      | (tarr T83 T84) => (tarr (tsubstTy d S32 T83) (tsubstTy d S32 T84))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x6) => (substIndex d s x6)
      | (abs T80 t11) => (abs T80 (substTm (weakenTrace d (HS tm H0)) s t11))
      | (app t12 t13) => (app (substTm d s t12) (substTm d s t13))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S32 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T80 t11) => (abs (tsubstTy d S32 T80) (tsubstTm (weakenTrace d (HS tm H0)) S32 t11))
      | (app t12 t13) => (app (tsubstTm d S32 t12) (tsubstTm d S32 t13))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x6 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x6)) = (var x6))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S32 : Ty) :
    (forall (k : Hvl) (X29 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S32 (tshiftIndex (weakenCutoffty C0 k) X29)) = (tvar X29))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S33 : Ty) (k : Hvl) (S32 : Ty) {struct S33} :
  ((tsubstTy (weakenTrace X0 k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = S33) :=
    match S33 return ((tsubstTy (weakenTrace X0 k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = S33) with
      | (tvar X29) => (tsubstIndex0_tshiftIndex0_reflection_ind S32 k X29)
      | (tabs K62 T80) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T80 (HS ty k) S32)))
      | (tapp T81 T82) => (f_equal2 tapp (tsubst0_tshift0_Ty_reflection_ind T81 k S32) (tsubst0_tshift0_Ty_reflection_ind T82 k S32))
      | (tarr T81 T82) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T81 k S32) (tsubst0_tshift0_Ty_reflection_ind T82 k S32))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x6) => (substIndex0_shiftIndex0_reflection_ind s k x6)
      | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t11 (HS tm k) s)))
      | (app t12 t13) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t12 k s) (subst0_shift0_Tm_reflection_ind t13 k s))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S32 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x6) => eq_refl
      | (abs T80 t11) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T80 k S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t11 (HS tm k) S32)))
      | (app t12 t13) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t12 k S32) (tsubst0_tshift0_Tm_reflection_ind t13 k S32))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S33 : Ty) : (forall (S32 : Ty) ,
    ((tsubstTy X0 S32 (tshiftTy C0 S33)) = S33)) := (tsubst0_tshift0_Ty_reflection_ind S33 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S32 : Ty) ,
    ((tsubstTm X0 S32 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x6 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x6)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x6)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff ty)) (X29 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c) k) (tshiftIndex (weakenCutoffty C0 k) X29)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c k) X29)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S32 : Ty) (k : Hvl) (c : (Cutoff ty)) {struct S32} :
    ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S32)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S32))) :=
      match S32 return ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S32)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S32))) with
        | (tvar X29) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c X29))
        | (tabs K62 T80) => (f_equal2 tabs eq_refl (tshift_tshift0_Ty_comm_ind T80 (HS ty k) c))
        | (tapp T81 T82) => (f_equal2 tapp (tshift_tshift0_Ty_comm_ind T81 k c) (tshift_tshift0_Ty_comm_ind T82 k c))
        | (tarr T81 T82) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T81 k c) (tshift_tshift0_Ty_comm_ind T82 k c))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x6))
        | (abs T80 t11) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t11 (HS tm k) c))
        | (app t12 t13) => (f_equal2 app (shift_shift0_Tm_comm_ind t12 k c) (shift_shift0_Tm_comm_ind t13 k c))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t11 (HS tm k) c))
        | (app t12 t13) => (f_equal2 app (shift_tshift0_Tm_comm_ind t12 k c) (shift_tshift0_Tm_comm_ind t13 k c))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t11 (HS tm k) c))
        | (app t12 t13) => (f_equal2 app (tshift_shift0_Tm_comm_ind t12 k c) (tshift_shift0_Tm_comm_ind t13 k c))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T80 k c) (tshift_tshift0_Tm_comm_ind t11 (HS tm k) c))
        | (app t12 t13) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t12 k c) (tshift_tshift0_Tm_comm_ind t13 k c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S32 : Ty) : (forall (c : (Cutoff ty)) ,
      ((tshiftTy (CS c) (tshiftTy C0 S32)) = (tshiftTy C0 (tshiftTy c S32)))) := (tshift_tshift0_Ty_comm_ind S32 H0).
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
    (forall (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) ,
      ((weakenTy (tshiftTy c S32) k) = (tshiftTy (weakenCutoffty c k) (weakenTy S32 k)))).
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
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (shiftTm c s) (shiftIndex (weakenCutofftm (CS c) k) x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tshiftTm c s) x6))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c : (Cutoff ty)) (S32 : Ty) :
      (forall (k : Hvl) (X29 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c k) (tsubstIndex (weakenTrace X0 k) S32 X29)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c S32) (tshiftIndex (weakenCutoffty (CS c) k) X29)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S33 : Ty) (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) {struct S33} :
    ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S32 S33)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S32) (tshiftTy (weakenCutoffty (CS c) k) S33))) :=
      match S33 return ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S32 S33)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S32) (tshiftTy (weakenCutoffty (CS c) k) S33))) with
        | (tvar X29) => (tshiftTy_tsubstIndex0_comm_ind c S32 k X29)
        | (tabs K62 T80) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T80 (HS ty k) c S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp T81 T82) => (f_equal2 tapp (tshift_tsubst0_Ty_comm_ind T81 k c S32) (tshift_tsubst0_Ty_comm_ind T82 k c S32))
        | (tarr T81 T82) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T81 k c S32) (tshift_tsubst0_Ty_comm_ind T82 k c S32))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x6) => (shiftTm_substIndex0_comm_ind c s k x6)
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t11 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t12 t13) => (f_equal2 app (shift_subst0_Tm_comm_ind t12 k c s) (shift_subst0_Tm_comm_ind t13 k c s))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) (S32 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) S32 (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) S32 (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t11 (HS tm k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t12 t13) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t12 k c S32) (shift_tsubst0_Tm_comm_ind t13 k c S32))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) with
        | (var x6) => (tshiftTm_substIndex0_comm_ind c s k x6)
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t11 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t12 t13) => (f_equal2 app (tshift_subst0_Tm_comm_ind t12 k c s) (tshift_subst0_Tm_comm_ind t13 k c s))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S32) (tshiftTm (weakenCutoffty (CS c) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S32) (tshiftTm (weakenCutoffty (CS c) k) s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T80 k c S32) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t11 (HS tm k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t12 t13) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t12 k c S32) (tshift_tsubst0_Tm_comm_ind t13 k c S32))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S33 : Ty) : (forall (c : (Cutoff ty)) (S32 : Ty) ,
      ((tshiftTy c (tsubstTy X0 S32 S33)) = (tsubstTy X0 (tshiftTy c S32) (tshiftTy (CS c) S33)))) := (tshift_tsubst0_Ty_comm_ind S33 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c (substTm X0 s s0)) = (substTm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff tm)) (S32 : Ty) ,
      ((shiftTm c (tsubstTm X0 S32 s)) = (tsubstTm X0 S32 (shiftTm c s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c (substTm X0 s s0)) = (substTm X0 (tshiftTm c s) (tshiftTm c s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff ty)) (S32 : Ty) ,
      ((tshiftTm c (tsubstTm X0 S32 s)) = (tsubstTm X0 (tshiftTy c S32) (tshiftTm (CS c) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k) s (shiftIndex (weakenCutofftm C0 k) x6)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d) k) s x6) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d : (Trace ty)) (S32 : Ty) :
      (forall (k : Hvl) (X29 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k) S32 X29) = (tsubstIndex (weakenTrace d k) S32 X29))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S32 : Ty) :
      (forall (k : Hvl) (X29 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k) S32 (tshiftIndex (weakenCutoffty C0 k) X29)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d k) S32 X29)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S33 : Ty) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct S33} :
    ((tsubstTy (weakenTrace (XS ty d) k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S32 S33))) :=
      match S33 return ((tsubstTy (weakenTrace (XS ty d) k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S32 S33))) with
        | (tvar X29) => (tsubstIndex_tshiftTy0_comm_ind d S32 k X29)
        | (tabs K62 T80) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T80 (HS ty k) d S32) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp T81 T82) => (f_equal2 tapp (tsubst_tshift0_Ty_comm_ind T81 k d S32) (tsubst_tshift0_Ty_comm_ind T82 k d S32))
        | (tarr T81 T82) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T81 k d S32) (tsubst_tshift0_Ty_comm_ind T82 k d S32))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_shiftTm0_comm_ind d s k x6)
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t11 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (subst_shift0_Tm_comm_ind t12 k d s) (subst_shift0_Tm_comm_ind t13 k d s))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_tshiftTm0_comm_ind d s k x6)
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t11 (HS tm k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (subst_tshift0_Tm_comm_ind t12 k d s) (subst_tshift0_Tm_comm_ind t13 k d s))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S32 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S32 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t11 (HS tm k) d S32) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t12 k d S32) (tsubst_shift0_Tm_comm_ind t13 k d S32))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d) k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d) k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T80 k d S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t11 (HS tm k) d S32) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t12 k d S32) (tsubst_tshift0_Tm_comm_ind t13 k d S32))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S33 : Ty) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTy (XS ty d) S32 (tshiftTy C0 S33)) = (tshiftTy C0 (tsubstTy d S32 S33)))) := (tsubst_tshift0_Ty_comm_ind S33 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTm d S32 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d S32 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTm (XS ty d) S32 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d S32 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S33 : Ty) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct S33} :
    ((tsubstTy (weakenTrace (XS tm d) k) S32 S33) = (tsubstTy (weakenTrace d k) S32 S33)) :=
      match S33 return ((tsubstTy (weakenTrace (XS tm d) k) S32 S33) = (tsubstTy (weakenTrace d k) S32 S33)) with
        | (tvar X29) => (tsubstIndex_shiftTy0_comm_ind d S32 k X29)
        | (tabs K62 T80) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T80 (HS ty k) d S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tapp T81 T82) => (f_equal2 tapp (tsubst_tm_Ty_ind T81 k d S32) (tsubst_tm_Ty_ind T82 k d S32))
        | (tarr T81 T82) => (f_equal2 tarr (tsubst_tm_Ty_ind T81 k d S32) (tsubst_tm_Ty_ind T82 k d S32))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d) k) S32 s) = (tsubstTm (weakenTrace d k) S32 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d) k) S32 s) = (tsubstTm (weakenTrace d k) S32 s)) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs (tsubst_tm_Ty_ind T80 k d S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t11 (HS tm k) d S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl))))
        | (app t12 t13) => (f_equal2 app (tsubst_tm_Tm_ind t12 k d S32) (tsubst_tm_Tm_ind t13 k d S32))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S33 : Ty) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTy (XS tm d) S32 S33) = (tsubstTy d S32 S33))) := (tsubst_tm_Ty_ind S33 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTm (XS tm d) S32 s) = (tsubstTm d S32 s))) := (tsubst_tm_Tm_ind s H0).
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
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substTm (weakenTrace d k) s (substIndex (weakenTrace X0 k) s0 x6)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substIndex (weakenTrace (XS tm d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d : (Trace ty)) (S32 : Ty) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((tsubstTm (weakenTrace d k) S32 (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tsubstTm d S32 s) x6))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d : (Trace ty)) (S32 : Ty) (S33 : Ty) :
      (forall (k : Hvl) (X29 : (Index ty)) ,
        ((tsubstTy (weakenTrace d k) S32 (tsubstIndex (weakenTrace X0 k) S33 X29)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstIndex (weakenTrace (XS ty d) k) S32 X29)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d : (Trace tm)) (s : Tm) (S32 : Ty) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace d k) s x6) = (tsubstTm (weakenTrace X0 k) S32 (substIndex (weakenTrace (XS ty d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S34 : Ty) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct S34} :
    ((tsubstTy (weakenTrace d k) S32 (tsubstTy (weakenTrace X0 k) S33 S34)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTy (weakenTrace (XS ty d) k) S32 S34))) :=
      match S34 return ((tsubstTy (weakenTrace d k) S32 (tsubstTy (weakenTrace X0 k) S33 S34)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTy (weakenTrace (XS ty d) k) S32 S34))) with
        | (tvar X29) => (tsubstTy_tsubstIndex0_commright_ind d S32 S33 k X29)
        | (tabs K62 T80) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T80 (HS ty k) d S32 S33) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp T81 T82) => (f_equal2 tapp (tsubst_tsubst0_Ty_comm_ind T81 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T82 k d S32 S33))
        | (tarr T81 T82) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T81 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T82 k d S32 S33))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x6) => (substTm_substIndex0_commright_ind d s s0 k x6)
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t11 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (subst_subst0_Tm_comm_ind t12 k d s s0) (subst_subst0_Tm_comm_ind t13 k d s s0))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (S32 : Ty) {struct s0} :
    ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S32 s0)) = (tsubstTm (weakenTrace X0 k) S32 (substTm (weakenTrace (XS ty d) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S32 s0)) = (tsubstTm (weakenTrace X0 k) S32 (substTm (weakenTrace (XS ty d) k) s s0))) with
        | (var x6) => (substTy_tsubstIndex0_commleft_ind d s S32 k x6)
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t11 (HS tm k) d s S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t12 k d s S32) (subst_tsubst0_Tm_comm_ind t13 k d s S32))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d k) S32 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S32 s) (tsubstTm (weakenTrace d k) S32 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d k) S32 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S32 s) (tsubstTm (weakenTrace d k) S32 s0))) with
        | (var x6) => (tsubstTm_substIndex0_commright_ind d S32 s k x6)
        | (abs T80 t11) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t11 (HS tm k) d S32 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t12 k d S32 s) (tsubst_subst0_Tm_comm_ind t13 k d S32 s))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S32 (tsubstTm (weakenTrace X0 k) S33 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTm (weakenTrace (XS ty d) k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S32 (tsubstTm (weakenTrace X0 k) S33 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTm (weakenTrace (XS ty d) k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T80 t11) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T80 k d S32 S33) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t11 (HS tm k) d S32 S33) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t12 t13) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t12 k d S32 S33) (tsubst_tsubst0_Tm_comm_ind t13 k d S32 S33))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S34 : Ty) : (forall (d : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
      ((tsubstTy d S32 (tsubstTy X0 S33 S34)) = (tsubstTy X0 (tsubstTy d S32 S33) (tsubstTy (XS ty d) S32 S34)))) := (tsubst_tsubst0_Ty_comm_ind S34 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d s (substTm X0 s0 s1)) = (substTm X0 (substTm d s s0) (substTm (XS tm d) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) (S32 : Ty) ,
      ((substTm d s (tsubstTm X0 S32 s0)) = (tsubstTm X0 S32 (substTm (XS ty d) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d : (Trace ty)) (S32 : Ty) (s : Tm) ,
      ((tsubstTm d S32 (substTm X0 s s0)) = (substTm X0 (tsubstTm d S32 s) (tsubstTm d S32 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
      ((tsubstTm d S32 (tsubstTm X0 S33 s)) = (tsubstTm X0 (tsubstTy d S32 S33) (tsubstTm (XS ty d) S32 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
        ((weakenTy (tsubstTy d S32 S33) k) = (tsubstTy (weakenTrace d k) S32 (weakenTy S33 k)))).
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
      (forall (k : Hvl) (d : (Trace ty)) (S32 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d S32 s) k) = (tsubstTm (weakenTrace d k) S32 (weakenTm s k)))).
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
  Inductive wfKind (k : Hvl) : Kind -> Prop :=
    | wfKind_star :
        (wfKind k (star))
    | wfKind_karr {K62 : Kind}
        (wf : (wfKind k K62))
        {K63 : Kind}
        (wf0 : (wfKind k K63)) :
        (wfKind k (karr K62 K63)).
  Inductive wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tvar (X29 : (Index ty))
        (wfi : (wfindex k X29)) :
        (wfTy k (tvar X29))
    | wfTy_tabs {K62 : Kind}
        (wf : (wfKind k K62)) {T80 : Ty}
        (wf0 : (wfTy (HS ty k) T80)) :
        (wfTy k (tabs K62 T80))
    | wfTy_tapp {T81 : Ty}
        (wf : (wfTy k T81)) {T82 : Ty}
        (wf0 : (wfTy k T82)) :
        (wfTy k (tapp T81 T82))
    | wfTy_tarr {T83 : Ty}
        (wf : (wfTy k T83)) {T84 : Ty}
        (wf0 : (wfTy k T84)) :
        (wfTy k (tarr T83 T84)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x6 : (Index tm))
        (wfi : (wfindex k x6)) :
        (wfTm k (var x6))
    | wfTm_abs {T80 : Ty}
        (wf : (wfTy k T80)) {t11 : Tm}
        (wf0 : (wfTm (HS tm k) t11)) :
        (wfTm k (abs T80 t11))
    | wfTm_app {t12 : Tm}
        (wf : (wfTm k t12)) {t13 : Tm}
        (wf0 : (wfTm k t13)) :
        (wfTm k (app t12 t13)).
  Definition inversion_wfKind_karr_0 (k0 : Hvl) (K1 : Kind) (K2 : Kind) (H18 : (wfKind k0 (karr K1 K2))) : (wfKind k0 K1) := match H18 in (wfKind _ K63) return match K63 return Prop with
    | (karr K1 K2) => (wfKind k0 K1)
    | _ => True
  end with
    | (wfKind_karr K1 H1 K2 H2) => H1
    | _ => I
  end.
  Definition inversion_wfKind_karr_1 (k0 : Hvl) (K1 : Kind) (K2 : Kind) (H18 : (wfKind k0 (karr K1 K2))) : (wfKind k0 K2) := match H18 in (wfKind _ K63) return match K63 return Prop with
    | (karr K1 K2) => (wfKind k0 K2)
    | _ => True
  end with
    | (wfKind_karr K1 H1 K2 H2) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tvar_1 (k1 : Hvl) (X : (Index ty)) (H19 : (wfTy k1 (tvar X))) : (wfindex k1 X) := match H19 in (wfTy _ S32) return match S32 return Prop with
    | (tvar X) => (wfindex k1 X)
    | _ => True
  end with
    | (wfTy_tvar X H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tabs_1 (k2 : Hvl) (K : Kind) (T : Ty) (H20 : (wfTy k2 (tabs K T))) : (wfKind k2 K) := match H20 in (wfTy _ S33) return match S33 return Prop with
    | (tabs K T) => (wfKind k2 K)
    | _ => True
  end with
    | (wfTy_tabs K H4 T H5) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tabs_2 (k2 : Hvl) (K : Kind) (T : Ty) (H20 : (wfTy k2 (tabs K T))) : (wfTy (HS ty k2) T) := match H20 in (wfTy _ S33) return match S33 return Prop with
    | (tabs K T) => (wfTy (HS ty k2) T)
    | _ => True
  end with
    | (wfTy_tabs K H4 T H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tapp_0 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k3 (tapp T1 T2))) : (wfTy k3 T1) := match H21 in (wfTy _ S34) return match S34 return Prop with
    | (tapp T1 T2) => (wfTy k3 T1)
    | _ => True
  end with
    | (wfTy_tapp T1 H6 T2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTy_tapp_1 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k3 (tapp T1 T2))) : (wfTy k3 T2) := match H21 in (wfTy _ S34) return match S34 return Prop with
    | (tapp T1 T2) => (wfTy k3 T2)
    | _ => True
  end with
    | (wfTy_tapp T1 H6 T2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H22 : (wfTy k4 (tarr T1 T2))) : (wfTy k4 T1) := match H22 in (wfTy _ S35) return match S35 return Prop with
    | (tarr T1 T2) => (wfTy k4 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H8 T2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H22 : (wfTy k4 (tarr T1 T2))) : (wfTy k4 T2) := match H22 in (wfTy _ S35) return match S35 return Prop with
    | (tarr T1 T2) => (wfTy k4 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H8 T2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k5 : Hvl) (x : (Index tm)) (H23 : (wfTm k5 (var x))) : (wfindex k5 x) := match H23 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k5 x)
    | _ => True
  end with
    | (wfTm_var x H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k6 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k6 (abs T t))) : (wfTy k6 T) := match H24 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k6 T)
    | _ => True
  end with
    | (wfTm_abs T H11 t H12) => H11
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k6 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k6 (abs T t))) : (wfTm (HS tm k6) t) := match H24 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k6) t)
    | _ => True
  end with
    | (wfTm_abs T H11 t H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k7 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k7 (app t1 t2))) : (wfTm k7 t1) := match H25 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k7 t1)
    | _ => True
  end with
    | (wfTm_app t1 H13 t2 H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k7 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k7 (app t1 t2))) : (wfTm k7 t2) := match H25 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k7 t2)
    | _ => True
  end with
    | (wfTm_app t1 H13 t2 H14) => H14
    | _ => I
  end.
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c : (Cutoff tm)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k8 : Hvl)
        : (shifthvl_tm C0 k8 (HS tm k8))
    | shifthvl_tm_there_tm
        (c : (Cutoff tm)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_tm c k8 k9) -> (shifthvl_tm (CS c) (HS tm k8) (HS tm k9))
    | shifthvl_tm_there_ty
        (c : (Cutoff tm)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_tm c k8 k9) -> (shifthvl_tm c (HS ty k8) (HS ty k9)).
  Inductive shifthvl_ty : (forall (c : (Cutoff ty)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k8 : Hvl)
        : (shifthvl_ty C0 k8 (HS ty k8))
    | shifthvl_ty_there_tm
        (c : (Cutoff ty)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_ty c k8 k9) -> (shifthvl_ty c (HS tm k8) (HS tm k9))
    | shifthvl_ty_there_ty
        (c : (Cutoff ty)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_ty c k8 k9) -> (shifthvl_ty (CS c) (HS ty k8) (HS ty k9)).
  Lemma weaken_shifthvl_tm  :
    (forall (k8 : Hvl) {c : (Cutoff tm)} {k9 : Hvl} {k10 : Hvl} ,
      (shifthvl_tm c k9 k10) -> (shifthvl_tm (weakenCutofftm c k8) (appendHvl k9 k8) (appendHvl k10 k8))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k8 : Hvl) {c : (Cutoff ty)} {k9 : Hvl} {k10 : Hvl} ,
      (shifthvl_ty c k9 k10) -> (shifthvl_ty (weakenCutoffty c k8) (appendHvl k9 k8) (appendHvl k10 k8))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) (x6 : (Index tm)) ,
      (wfindex k8 x6) -> (wfindex k9 (shiftIndex c x6))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c : (Cutoff tm)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) (X29 : (Index ty)) ,
      (wfindex k8 X29) -> (wfindex k9 X29)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c : (Cutoff ty)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) (x6 : (Index tm)) ,
      (wfindex k8 x6) -> (wfindex k9 x6)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c : (Cutoff ty)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) (X29 : (Index ty)) ,
      (wfindex k8 X29) -> (wfindex k9 (tshiftIndex c X29))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfKind : (forall (k8 : Hvl) ,
    (forall (K64 : Kind) (wf : (wfKind k8 K64)) ,
      (forall (c : (Cutoff tm)) (k9 : Hvl) ,
        (shifthvl_tm c k8 k9) -> (wfKind k9 K64)))) := (fun (k8 : Hvl) =>
    (ind_wfKind k8 (fun (K64 : Kind) (wf : (wfKind k8 K64)) =>
      (forall (c : (Cutoff tm)) (k9 : Hvl) ,
        (shifthvl_tm c k8 k9) -> (wfKind k9 K64))) (fun (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
      (wfKind_star k9)) (fun (K1 : Kind) (wf : (wfKind k8 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k8 K2)) IHK2 (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
      (wfKind_karr k9 (IHK1 c k9 (weaken_shifthvl_tm H0 ins)) (IHK2 c k9 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfKind : (forall (k8 : Hvl) ,
    (forall (K64 : Kind) (wf : (wfKind k8 K64)) ,
      (forall (c : (Cutoff ty)) (k9 : Hvl) ,
        (shifthvl_ty c k8 k9) -> (wfKind k9 K64)))) := (fun (k8 : Hvl) =>
    (ind_wfKind k8 (fun (K64 : Kind) (wf : (wfKind k8 K64)) =>
      (forall (c : (Cutoff ty)) (k9 : Hvl) ,
        (shifthvl_ty c k8 k9) -> (wfKind k9 K64))) (fun (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
      (wfKind_star k9)) (fun (K1 : Kind) (wf : (wfKind k8 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k8 K2)) IHK2 (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
      (wfKind_karr k9 (IHK1 c k9 (weaken_shifthvl_ty H0 ins)) (IHK2 c k9 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTy : (forall (k8 : Hvl) ,
    (forall (S36 : Ty) (wf : (wfTy k8 S36)) ,
      (forall (c : (Cutoff tm)) (k9 : Hvl) ,
        (shifthvl_tm c k8 k9) -> (wfTy k9 S36)))) := (ind_wfTy (fun (k8 : Hvl) (S36 : Ty) (wf : (wfTy k8 S36)) =>
    (forall (c : (Cutoff tm)) (k9 : Hvl) ,
      (shifthvl_tm c k8 k9) -> (wfTy k9 S36))) (fun (k8 : Hvl) (X29 : (Index ty)) (wfi : (wfindex k8 X29)) (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_tvar k9 _ (shift_wfindex_ty c k8 k9 ins X29 wfi))) (fun (k8 : Hvl) (K : Kind) (wf : (wfKind k8 K)) (T : Ty) (wf0 : (wfTy (HS ty k8) T)) IHT (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_tabs k9 (shift_wfKind k8 K wf c k9 (weaken_shifthvl_tm H0 ins)) (IHT c (HS ty k9) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_tapp k9 (IHT1 c k9 (weaken_shifthvl_tm H0 ins)) (IHT2 c k9 (weaken_shifthvl_tm H0 ins)))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_tarr k9 (IHT1 c k9 (weaken_shifthvl_tm H0 ins)) (IHT2 c k9 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTy : (forall (k8 : Hvl) ,
    (forall (S36 : Ty) (wf : (wfTy k8 S36)) ,
      (forall (c : (Cutoff ty)) (k9 : Hvl) ,
        (shifthvl_ty c k8 k9) -> (wfTy k9 (tshiftTy c S36))))) := (ind_wfTy (fun (k8 : Hvl) (S36 : Ty) (wf : (wfTy k8 S36)) =>
    (forall (c : (Cutoff ty)) (k9 : Hvl) ,
      (shifthvl_ty c k8 k9) -> (wfTy k9 (tshiftTy c S36)))) (fun (k8 : Hvl) (X29 : (Index ty)) (wfi : (wfindex k8 X29)) (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_tvar k9 _ (tshift_wfindex_ty c k8 k9 ins X29 wfi))) (fun (k8 : Hvl) (K : Kind) (wf : (wfKind k8 K)) (T : Ty) (wf0 : (wfTy (HS ty k8) T)) IHT (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_tabs k9 (tshift_wfKind k8 K wf c k9 (weaken_shifthvl_ty H0 ins)) (IHT (CS c) (HS ty k9) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_tapp k9 (IHT1 c k9 (weaken_shifthvl_ty H0 ins)) (IHT2 c k9 (weaken_shifthvl_ty H0 ins)))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_tarr k9 (IHT1 c k9 (weaken_shifthvl_ty H0 ins)) (IHT2 c k9 (weaken_shifthvl_ty H0 ins))))).
  Definition shift_wfTm : (forall (k8 : Hvl) ,
    (forall (s2 : Tm) (wf : (wfTm k8 s2)) ,
      (forall (c : (Cutoff tm)) (k9 : Hvl) ,
        (shifthvl_tm c k8 k9) -> (wfTm k9 (shiftTm c s2))))) := (ind_wfTm (fun (k8 : Hvl) (s2 : Tm) (wf : (wfTm k8 s2)) =>
    (forall (c : (Cutoff tm)) (k9 : Hvl) ,
      (shifthvl_tm c k8 k9) -> (wfTm k9 (shiftTm c s2)))) (fun (k8 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k8 x6)) (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_var k9 _ (shift_wfindex_tm c k8 k9 ins x6 wfi))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS tm k8) t)) IHt (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_abs k9 (shift_wfTy k8 T wf c k9 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k9) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k8 : Hvl) (t1 : Tm) (wf : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k8 t2)) IHt2 (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_app k9 (IHt1 c k9 (weaken_shifthvl_tm H0 ins)) (IHt2 c k9 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k8 : Hvl) ,
    (forall (s2 : Tm) (wf : (wfTm k8 s2)) ,
      (forall (c : (Cutoff ty)) (k9 : Hvl) ,
        (shifthvl_ty c k8 k9) -> (wfTm k9 (tshiftTm c s2))))) := (ind_wfTm (fun (k8 : Hvl) (s2 : Tm) (wf : (wfTm k8 s2)) =>
    (forall (c : (Cutoff ty)) (k9 : Hvl) ,
      (shifthvl_ty c k8 k9) -> (wfTm k9 (tshiftTm c s2)))) (fun (k8 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k8 x6)) (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_var k9 _ (tshift_wfindex_tm c k8 k9 ins x6 wfi))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS tm k8) t)) IHt (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_abs k9 (tshift_wfTy k8 T wf c k9 (weaken_shifthvl_ty H0 ins)) (IHt c (HS tm k9) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k8 : Hvl) (t1 : Tm) (wf : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k8 t2)) IHt2 (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_app k9 (IHt1 c k9 (weaken_shifthvl_ty H0 ins)) (IHt2 c k9 (weaken_shifthvl_ty H0 ins))))).
  Fixpoint weaken_wfKind (k8 : Hvl) {struct k8} :
  (forall (k9 : Hvl) (K64 : Kind) (wf : (wfKind k9 K64)) ,
    (wfKind (appendHvl k9 k8) (weakenKind K64 k8))) :=
    match k8 return (forall (k9 : Hvl) (K64 : Kind) (wf : (wfKind k9 K64)) ,
      (wfKind (appendHvl k9 k8) (weakenKind K64 k8))) with
      | (H0) => (fun (k9 : Hvl) (K64 : Kind) (wf : (wfKind k9 K64)) =>
        wf)
      | (HS tm k8) => (fun (k9 : Hvl) (K64 : Kind) (wf : (wfKind k9 K64)) =>
        (shift_wfKind (appendHvl k9 k8) (weakenKind K64 k8) (weaken_wfKind k8 k9 K64 wf) C0 (HS tm (appendHvl k9 k8)) (shifthvl_tm_here (appendHvl k9 k8))))
      | (HS ty k8) => (fun (k9 : Hvl) (K64 : Kind) (wf : (wfKind k9 K64)) =>
        (tshift_wfKind (appendHvl k9 k8) (weakenKind K64 k8) (weaken_wfKind k8 k9 K64 wf) C0 (HS ty (appendHvl k9 k8)) (shifthvl_ty_here (appendHvl k9 k8))))
    end.
  Fixpoint weaken_wfTy (k8 : Hvl) {struct k8} :
  (forall (k9 : Hvl) (S36 : Ty) (wf : (wfTy k9 S36)) ,
    (wfTy (appendHvl k9 k8) (weakenTy S36 k8))) :=
    match k8 return (forall (k9 : Hvl) (S36 : Ty) (wf : (wfTy k9 S36)) ,
      (wfTy (appendHvl k9 k8) (weakenTy S36 k8))) with
      | (H0) => (fun (k9 : Hvl) (S36 : Ty) (wf : (wfTy k9 S36)) =>
        wf)
      | (HS tm k8) => (fun (k9 : Hvl) (S36 : Ty) (wf : (wfTy k9 S36)) =>
        (shift_wfTy (appendHvl k9 k8) (weakenTy S36 k8) (weaken_wfTy k8 k9 S36 wf) C0 (HS tm (appendHvl k9 k8)) (shifthvl_tm_here (appendHvl k9 k8))))
      | (HS ty k8) => (fun (k9 : Hvl) (S36 : Ty) (wf : (wfTy k9 S36)) =>
        (tshift_wfTy (appendHvl k9 k8) (weakenTy S36 k8) (weaken_wfTy k8 k9 S36 wf) C0 (HS ty (appendHvl k9 k8)) (shifthvl_ty_here (appendHvl k9 k8))))
    end.
  Fixpoint weaken_wfTm (k8 : Hvl) {struct k8} :
  (forall (k9 : Hvl) (s2 : Tm) (wf : (wfTm k9 s2)) ,
    (wfTm (appendHvl k9 k8) (weakenTm s2 k8))) :=
    match k8 return (forall (k9 : Hvl) (s2 : Tm) (wf : (wfTm k9 s2)) ,
      (wfTm (appendHvl k9 k8) (weakenTm s2 k8))) with
      | (H0) => (fun (k9 : Hvl) (s2 : Tm) (wf : (wfTm k9 s2)) =>
        wf)
      | (HS tm k8) => (fun (k9 : Hvl) (s2 : Tm) (wf : (wfTm k9 s2)) =>
        (shift_wfTm (appendHvl k9 k8) (weakenTm s2 k8) (weaken_wfTm k8 k9 s2 wf) C0 (HS tm (appendHvl k9 k8)) (shifthvl_tm_here (appendHvl k9 k8))))
      | (HS ty k8) => (fun (k9 : Hvl) (s2 : Tm) (wf : (wfTm k9 s2)) =>
        (tshift_wfTm (appendHvl k9 k8) (weakenTm s2 k8) (weaken_wfTm k8 k9 s2 wf) C0 (HS ty (appendHvl k9 k8)) (shifthvl_ty_here (appendHvl k9 k8))))
    end.
End ShiftWellFormed.
Lemma wfKind_cast  :
  (forall (k8 : Hvl) (K64 : Kind) (k9 : Hvl) (K65 : Kind) ,
    (k8 = k9) -> (K64 = K65) -> (wfKind k8 K64) -> (wfKind k9 K65)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k8 : Hvl) (S36 : Ty) (k9 : Hvl) (S37 : Ty) ,
    (k8 = k9) -> (S36 = S37) -> (wfTy k8 S36) -> (wfTy k9 S37)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k8 : Hvl) (s2 : Tm) (k9 : Hvl) (s3 : Tm) ,
    (k8 = k9) -> (s2 = s3) -> (wfTm k8 s2) -> (wfTm k9 s3)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k8 : Hvl) : (forall (d : (Trace tm)) (k9 : Hvl) (k10 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k8 X0 (HS tm k8) k8)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_tm k8 d k9 k10) -> (substhvl_tm k8 (XS tm d) (HS tm k9) (HS tm k10))
    | substhvl_tm_there_ty
        {d : (Trace tm)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_tm k8 d k9 k10) -> (substhvl_tm k8 (XS ty d) (HS ty k9) (HS ty k10)).
  Inductive substhvl_ty (k8 : Hvl) : (forall (d : (Trace ty)) (k9 : Hvl) (k10 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k8 X0 (HS ty k8) k8)
    | substhvl_ty_there_tm
        {d : (Trace ty)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_ty k8 d k9 k10) -> (substhvl_ty k8 (XS tm d) (HS tm k9) (HS tm k10))
    | substhvl_ty_there_ty
        {d : (Trace ty)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_ty k8 d k9 k10) -> (substhvl_ty k8 (XS ty d) (HS ty k9) (HS ty k10)).
  Lemma weaken_substhvl_tm  :
    (forall {k9 : Hvl} (k8 : Hvl) {d : (Trace tm)} {k10 : Hvl} {k11 : Hvl} ,
      (substhvl_tm k9 d k10 k11) -> (substhvl_tm k9 (weakenTrace d k8) (appendHvl k10 k8) (appendHvl k11 k8))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k9 : Hvl} (k8 : Hvl) {d : (Trace ty)} {k10 : Hvl} {k11 : Hvl} ,
      (substhvl_ty k9 d k10 k11) -> (substhvl_ty k9 (weakenTrace d k8) (appendHvl k10 k8) (appendHvl k11 k8))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k8 : Hvl} {s2 : Tm} (wft : (wfTm k8 s2)) :
    (forall {d : (Trace tm)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (forall {x6 : (Index tm)} ,
        (wfindex k9 x6) -> (wfTm k10 (substIndex d s2 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k8 : Hvl} {S36 : Ty} (wft : (wfTy k8 S36)) :
    (forall {d : (Trace ty)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (forall {X29 : (Index ty)} ,
        (wfindex k9 X29) -> (wfTy k10 (tsubstIndex d S36 X29)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k8 : Hvl} :
    (forall {d : (Trace tm)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (forall {X29 : (Index ty)} ,
        (wfindex k9 X29) -> (wfindex k10 X29))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k8 : Hvl} :
    (forall {d : (Trace ty)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (forall {x6 : (Index tm)} ,
        (wfindex k9 x6) -> (wfindex k10 x6))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfKind {k8 : Hvl} : (forall (k9 : Hvl) ,
    (forall (K64 : Kind) (wf0 : (wfKind k9 K64)) ,
      (forall {d : (Trace tm)} {k10 : Hvl} ,
        (substhvl_tm k8 d k9 k10) -> (wfKind k10 K64)))) := (fun (k9 : Hvl) =>
    (ind_wfKind k9 (fun (K64 : Kind) (wf0 : (wfKind k9 K64)) =>
      (forall {d : (Trace tm)} {k10 : Hvl} ,
        (substhvl_tm k8 d k9 k10) -> (wfKind k10 K64))) (fun {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
      (wfKind_star k10)) (fun (K1 : Kind) (wf0 : (wfKind k9 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k9 K2)) IHK2 {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
      (wfKind_karr k10 (IHK1 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (IHK2 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfKind {k8 : Hvl} : (forall (k9 : Hvl) ,
    (forall (K64 : Kind) (wf0 : (wfKind k9 K64)) ,
      (forall {d : (Trace ty)} {k10 : Hvl} ,
        (substhvl_ty k8 d k9 k10) -> (wfKind k10 K64)))) := (fun (k9 : Hvl) =>
    (ind_wfKind k9 (fun (K64 : Kind) (wf0 : (wfKind k9 K64)) =>
      (forall {d : (Trace ty)} {k10 : Hvl} ,
        (substhvl_ty k8 d k9 k10) -> (wfKind k10 K64))) (fun {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
      (wfKind_star k10)) (fun (K1 : Kind) (wf0 : (wfKind k9 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k9 K2)) IHK2 {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
      (wfKind_karr k10 (IHK1 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (IHK2 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTy {k8 : Hvl} : (forall (k9 : Hvl) ,
    (forall (S36 : Ty) (wf0 : (wfTy k9 S36)) ,
      (forall {d : (Trace tm)} {k10 : Hvl} ,
        (substhvl_tm k8 d k9 k10) -> (wfTy k10 S36)))) := (ind_wfTy (fun (k9 : Hvl) (S36 : Ty) (wf0 : (wfTy k9 S36)) =>
    (forall {d : (Trace tm)} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (wfTy k10 S36))) (fun (k9 : Hvl) {X29 : (Index ty)} (wfi : (wfindex k9 X29)) {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_tvar k10 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k9 : Hvl) (K : Kind) (wf0 : (wfKind k9 K)) (T : Ty) (wf1 : (wfTy (HS ty k9) T)) IHT {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_tabs k10 (substhvl_tm_wfKind k9 K wf0 (weaken_substhvl_tm H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k10) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_tapp k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_tarr k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTy {k8 : Hvl} {S36 : Ty} (wf : (wfTy k8 S36)) : (forall (k9 : Hvl) ,
    (forall (S37 : Ty) (wf0 : (wfTy k9 S37)) ,
      (forall {d : (Trace ty)} {k10 : Hvl} ,
        (substhvl_ty k8 d k9 k10) -> (wfTy k10 (tsubstTy d S36 S37))))) := (ind_wfTy (fun (k9 : Hvl) (S37 : Ty) (wf0 : (wfTy k9 S37)) =>
    (forall {d : (Trace ty)} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (wfTy k10 (tsubstTy d S36 S37)))) (fun (k9 : Hvl) {X29 : (Index ty)} (wfi : (wfindex k9 X29)) {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k9 : Hvl) (K : Kind) (wf0 : (wfKind k9 K)) (T : Ty) (wf1 : (wfTy (HS ty k9) T)) IHT {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTy_tabs k10 (substhvl_ty_wfKind k9 K wf0 (weaken_substhvl_ty H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k10) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTy_tapp k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTy_tarr k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del))))).
  Definition substhvl_tm_wfTm {k8 : Hvl} {s2 : Tm} (wf : (wfTm k8 s2)) : (forall (k9 : Hvl) ,
    (forall (s3 : Tm) (wf0 : (wfTm k9 s3)) ,
      (forall {d : (Trace tm)} {k10 : Hvl} ,
        (substhvl_tm k8 d k9 k10) -> (wfTm k10 (substTm d s2 s3))))) := (ind_wfTm (fun (k9 : Hvl) (s3 : Tm) (wf0 : (wfTm k9 s3)) =>
    (forall {d : (Trace tm)} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (wfTm k10 (substTm d s2 s3)))) (fun (k9 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k9 x6)) {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS tm k9) t)) IHt {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTm_abs k10 (substhvl_tm_wfTy k9 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k10) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k9 : Hvl) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k9 t2)) IHt2 {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTm_app k10 (IHt1 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k8 : Hvl} {S36 : Ty} (wf : (wfTy k8 S36)) : (forall (k9 : Hvl) ,
    (forall (s2 : Tm) (wf0 : (wfTm k9 s2)) ,
      (forall {d : (Trace ty)} {k10 : Hvl} ,
        (substhvl_ty k8 d k9 k10) -> (wfTm k10 (tsubstTm d S36 s2))))) := (ind_wfTm (fun (k9 : Hvl) (s2 : Tm) (wf0 : (wfTm k9 s2)) =>
    (forall {d : (Trace ty)} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (wfTm k10 (tsubstTm d S36 s2)))) (fun (k9 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k9 x6)) {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_var k10 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS tm k9) t)) IHt {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_abs k10 (substhvl_ty_wfTy wf k9 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k10) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k9 : Hvl) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k9 t2)) IHt2 {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_app k10 (IHt1 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty)
    | etvar (G : Env) (K : Kind).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1 K) => (etvar (appendEnv G G1) K)
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0 K) => (HS ty (domainEnv G0))
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
      | (etvar G0 K) => (etvar (shiftEnv c G0) K)
    end.
  Fixpoint tshiftEnv (c : (Cutoff ty)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c G0) (tshiftTy (weakenCutoffty c (domainEnv G0)) T))
      | (etvar G0 K) => (etvar (tshiftEnv c G0) K)
    end.
  Fixpoint weakenEnv (G : Env) (k8 : Hvl) {struct k8} :
  Env :=
    match k8 with
      | (H0) => G
      | (HS tm k8) => (weakenEnv G k8)
      | (HS ty k8) => (tshiftEnv C0 (weakenEnv G k8))
    end.
  Fixpoint substEnv (d : (Trace tm)) (s2 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s2 G0) T)
      | (etvar G0 K) => (etvar (substEnv d s2 G0) K)
    end.
  Fixpoint tsubstEnv (d : (Trace ty)) (S36 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d S36 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S36 T))
      | (etvar G0 K) => (etvar (tsubstEnv d S36 G0) K)
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
    (forall (d : (Trace tm)) (s2 : Tm) (G : Env) ,
      ((domainEnv (substEnv d s2 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d : (Trace ty)) (S36 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d S36 G)) = (domainEnv G))).
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
      (forall (d : (Trace tm)) (s2 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d s2 (appendEnv G G0)) = (appendEnv (substEnv d s2 G) (substEnv (weakenTrace d (domainEnv G)) s2 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d : (Trace ty)) (S36 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d S36 (appendEnv G G0)) = (appendEnv (tsubstEnv d S36 G) (tsubstEnv (weakenTrace d (domainEnv G)) S36 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenKind_append  :
    (forall (K64 : Kind) (k8 : Hvl) (k9 : Hvl) ,
      ((weakenKind (weakenKind K64 k8) k9) = (weakenKind K64 (appendHvl k8 k9)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S36 : Ty) (k8 : Hvl) (k9 : Hvl) ,
      ((weakenTy (weakenTy S36 k8) k9) = (weakenTy S36 (appendHvl k8 k9)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s2 : Tm) (k8 : Hvl) (k9 : Hvl) ,
      ((weakenTm (weakenTm s2 k8) k9) = (weakenTm s2 (appendHvl k8 k9)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T80 : Ty) :
          (wfTy (domainEnv G) T80) -> (lookup_evar (evar G T80) I0 T80)
      | lookup_evar_there_evar
          {G : Env} {x6 : (Index tm)}
          (T81 : Ty) (T82 : Ty) :
          (lookup_evar G x6 T81) -> (lookup_evar (evar G T82) (IS x6) T81)
      | lookup_evar_there_etvar
          {G : Env} {x6 : (Index tm)}
          (T81 : Ty) (K64 : Kind) :
          (lookup_evar G x6 T81) -> (lookup_evar (etvar G K64) x6 (tshiftTy C0 T81)).
    Inductive lookup_etvar : Env -> (Index ty) -> Kind -> Prop :=
      | lookup_etvar_here {G : Env}
          (K64 : Kind) :
          (wfKind (domainEnv G) K64) -> (lookup_etvar (etvar G K64) I0 K64)
      | lookup_etvar_there_evar
          {G : Env} {X29 : (Index ty)}
          (K65 : Kind) (T81 : Ty) :
          (lookup_etvar G X29 K65) -> (lookup_etvar (evar G T81) X29 K65)
      | lookup_etvar_there_etvar
          {G : Env} {X29 : (Index ty)}
          (K65 : Kind) (K66 : Kind) :
          (lookup_etvar G X29 K65) -> (lookup_etvar (etvar G K66) (IS X29) K65).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T81 : Ty) (T82 : Ty) ,
        (lookup_evar (evar G T81) I0 T82) -> (T81 = T82)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (K65 : Kind) (K66 : Kind) ,
        (lookup_etvar (etvar G K65) I0 K66) -> (K65 = K66)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x6 : (Index tm)} ,
        (forall (T81 : Ty) ,
          (lookup_evar G x6 T81) -> (forall (T82 : Ty) ,
            (lookup_evar G x6 T82) -> (T81 = T82)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X29 : (Index ty)} ,
        (forall (K65 : Kind) ,
          (lookup_etvar G X29 K65) -> (forall (K66 : Kind) ,
            (lookup_etvar G X29 K66) -> (K65 = K66)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x6 : (Index tm)} (T81 : Ty) ,
        (lookup_evar G x6 T81) -> (wfTy (domainEnv G) T81)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X29 : (Index ty)} (K65 : Kind) ,
        (lookup_etvar G X29 K65) -> (wfKind (domainEnv G) K65)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x6 : (Index tm)} (T81 : Ty) ,
        (lookup_evar G x6 T81) -> (lookup_evar (appendEnv G G0) (weakenIndextm x6 (domainEnv G0)) (weakenTy T81 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X29 : (Index ty)} (K65 : Kind) ,
        (lookup_etvar G X29 K65) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X29 (domainEnv G0)) (weakenKind K65 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x6 : (Index tm)} (T83 : Ty) ,
        (lookup_evar G x6 T83) -> (wfindex (domainEnv G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X29 : (Index ty)} (K67 : Kind) ,
        (lookup_etvar G X29 K67) -> (wfindex (domainEnv G) X29)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T81 : Ty} :
        (shift_evar C0 G (evar G T81))
    | shiftevar_there_evar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_evar c G G0) -> (shift_evar c (etvar G K) (etvar G0 K)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutofftm c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {K65 : Kind} :
        (shift_etvar C0 G (etvar G K65))
    | shiftetvar_there_evar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (tshiftTy c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G K) (etvar G0 K)).
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
  Inductive subst_evar (G : Env) (T81 : Ty) (s2 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T81 s2 X0 (evar G T81) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T82 : Ty) :
        (subst_evar G T81 s2 d G0 G1) -> (subst_evar G T81 s2 (XS tm d) (evar G0 T82) (evar G1 T82))
    | subst_evar_there_etvar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (K65 : Kind) :
        (subst_evar G T81 s2 d G0 G1) -> (subst_evar G T81 s2 (XS ty d) (etvar G0 K65) (etvar G1 K65)).
  Lemma weaken_subst_evar {G : Env} (T81 : Ty) {s2 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T81 s2 d G1 G2) -> (subst_evar G T81 s2 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (K65 : Kind) (S36 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K65 S36 X0 (etvar G K65) G)
    | subst_etvar_there_evar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T81 : Ty) :
        (subst_etvar G K65 S36 d G0 G1) -> (subst_etvar G K65 S36 (XS tm d) (evar G0 T81) (evar G1 (tsubstTy d S36 T81)))
    | subst_etvar_there_etvar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (K66 : Kind) :
        (subst_etvar G K65 S36 d G0 G1) -> (subst_etvar G K65 S36 (XS ty d) (etvar G0 K66) (etvar G1 K66)).
  Lemma weaken_subst_etvar {G : Env} (K65 : Kind) {S36 : Ty} :
    (forall (G0 : Env) {d : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G K65 S36 d G1 G2) -> (subst_etvar G K65 S36 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d S36 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s2 : Tm} (T81 : Ty) :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T81 s2 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S36 : Ty} (K65 : Kind) :
    (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G K65 S36 d G0 G1) -> (substhvl_ty (domainEnv G) d (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T81 : Ty} (wf : (wfTy (domainEnv G) T81)) ,
    (lookup_evar (appendEnv (evar G T81) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T81 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {K65 : Kind} (wf : (wfKind (domainEnv G) K65)) ,
    (lookup_etvar (appendEnv (etvar G K65) G0) (weakenIndexty I0 (domainEnv G0)) (weakenKind K65 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfKind wfTm wfTy : infra.
 Hint Constructors wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H32 : (wfKind _ (star)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfKind _ (karr _ _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H32 : (wfTy _ (tvar _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (tabs _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (tapp _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (tarr _ _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H32 : (wfTm _ (var _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (abs _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (app _ _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Resolve lookup_evar_wf lookup_etvar_wf : infra.
 Hint Resolve lookup_evar_wf lookup_etvar_wf : wf.
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
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x6 : (Index tm)} {T81 : Ty} ,
    (lookup_evar G x6 T81) -> (lookup_evar G0 (shiftIndex c x6) T81)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X29 : (Index ty)} {K65 : Kind} ,
    (lookup_etvar G X29 K65) -> (lookup_etvar G0 X29 K65)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x6 : (Index tm)} {T81 : Ty} ,
    (lookup_evar G x6 T81) -> (lookup_evar G0 x6 (tshiftTy c T81))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X29 : (Index ty)} {K65 : Kind} ,
    (lookup_etvar G X29 K65) -> (lookup_etvar G0 (tshiftIndex c X29) K65)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T82 : Ty) {s2 : Tm} :
  (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T82 s2 d G0 G1)) {X29 : (Index ty)} (K66 : Kind) ,
    (lookup_etvar G0 X29 K66) -> (lookup_etvar G1 X29 K66)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} (K66 : Kind) {S36 : Ty} (wf : (wfTy (domainEnv G) S36)) :
  (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G K66 S36 d G0 G1)) {x6 : (Index tm)} (T82 : Ty) ,
    (lookup_evar G0 x6 T82) -> (lookup_evar G1 x6 (tsubstTy d S36 T82))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Kind (K62 : Kind) {struct K62} :
nat :=
  match K62 with
    | (star) => 1
    | (karr K63 K64) => (plus 1 (plus (size_Kind K63) (size_Kind K64)))
  end.
Fixpoint size_Ty (S32 : Ty) {struct S32} :
nat :=
  match S32 with
    | (tvar X29) => 1
    | (tabs K62 T80) => (plus 1 (plus (size_Kind K62) (size_Ty T80)))
    | (tapp T81 T82) => (plus 1 (plus (size_Ty T81) (size_Ty T82)))
    | (tarr T83 T84) => (plus 1 (plus (size_Ty T83) (size_Ty T84)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x6) => 1
    | (abs T80 t11) => (plus 1 (plus (size_Ty T80) (size_Tm t11)))
    | (app t12 t13) => (plus 1 (plus (size_Tm t12) (size_Tm t13)))
  end.
Fixpoint tshift_size_Ty (S32 : Ty) (c : (Cutoff ty)) {struct S32} :
((size_Ty (tshiftTy c S32)) = (size_Ty S32)) :=
  match S32 return ((size_Ty (tshiftTy c S32)) = (size_Ty S32)) with
    | (tvar _) => eq_refl
    | (tabs K T) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (tshift_size_Ty T (CS c))))
    | (tapp T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
  end.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Kind  :
  (forall (k : Hvl) (K62 : Kind) ,
    ((size_Kind (weakenKind K62 k)) = (size_Kind K62))).
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
  (forall (k : Hvl) (S32 : Ty) ,
    ((size_Ty (weakenTy S32 k)) = (size_Ty S32))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive TRed (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | QR_Var (K : Kind)
      (X : (Index ty))
      (lk : (lookup_etvar G X K))
      (H20 : (wfKind (domainEnv G) K))
      (H21 : (wfindex (domainEnv G) X))
      : (TRed G (tvar X) (tvar X) K)
  | QR_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm21 : (TRed G S1 T1 (star)))
      (jm22 : (TRed G S2 T2 (star))) :
      (TRed G (tarr S1 S2) (tarr T1 T2) (star))
  | QR_Abs (K1 : Kind) (K2 : Kind)
      (S2 : Ty) (T2 : Ty)
      (jm23 : (TRed (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0))))
      (H26 : (wfKind (domainEnv G) K1))
      (H27 : (wfKind (domainEnv G) K2))
      :
      (TRed G (tabs K1 S2) (tabs K1 T2) (karr K1 K2))
  | QR_App (K1 : Kind) (K2 : Kind)
      (S1 : Ty) (S2 : Ty) (T1 : Ty)
      (T2 : Ty)
      (jm24 : (TRed G S1 T1 (karr K2 K1)))
      (jm25 : (TRed G S2 T2 K2)) :
      (TRed G (tapp S1 S2) (tapp T1 T2) K1)
  | QR_AppAbs (K1 : Kind)
      (K2 : Kind) (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm26 : (TRed (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0))))
      (jm27 : (TRed G S2 T2 K2))
      (H36 : (wfKind (domainEnv G) K1))
      :
      (TRed G (tapp (tabs K2 S1) S2) (tsubstTy X0 T2 T1) K1).
Inductive Kinding (G : Env) : Ty -> Kind -> Prop :=
  | K_TVar (K : Kind)
      (X : (Index ty))
      (lk : (lookup_etvar G X K))
      (H19 : (wfKind (domainEnv G) K))
      (H20 : (wfindex (domainEnv G) X))
      : (Kinding G (tvar X) K)
  | K_Abs (K1 : Kind) (K2 : Kind)
      (T2 : Ty)
      (jm : (Kinding (etvar G K1) T2 (weakenKind K2 (HS ty H0))))
      (H21 : (wfKind (domainEnv G) K1))
      (H22 : (wfKind (domainEnv G) K2))
      :
      (Kinding G (tabs K1 T2) (karr K1 K2))
  | K_App (K11 : Kind)
      (K12 : Kind) (T1 : Ty) (T2 : Ty)
      (jm0 : (Kinding G T1 (karr K11 K12)))
      (jm1 : (Kinding G T2 K11)) :
      (Kinding G (tapp T1 T2) K12)
  | K_Arr (T1 : Ty) (T2 : Ty)
      (jm2 : (Kinding G T1 (star)))
      (jm3 : (Kinding G T2 (star))) :
      (Kinding G (tarr T1 T2) (star)).
Inductive TRedStar (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | QRS_Nil (K : Kind) (T : Ty)
      (jm28 : (Kinding G T K)) :
      (TRedStar G T T K)
  | QRS_Cons (K : Kind) (S1 : Ty)
      (T : Ty) (U : Ty)
      (jm29 : (TRedStar G S1 T K))
      (jm30 : (TRed G T U K)) :
      (TRedStar G S1 U K).
Inductive TyEq (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | Q_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm4 : (TyEq G S1 T1 (star)))
      (jm5 : (TyEq G S2 T2 (star))) :
      (TyEq G (tarr S1 S2) (tarr T1 T2) (star))
  | Q_Abs (K1 : Kind) (K2 : Kind)
      (S2 : Ty) (T2 : Ty)
      (jm6 : (TyEq (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0))))
      (H24 : (wfKind (domainEnv G) K1))
      (H25 : (wfKind (domainEnv G) K2))
      :
      (TyEq G (tabs K1 S2) (tabs K1 T2) (karr K1 K2))
  | Q_App (K1 : Kind) (K2 : Kind)
      (S1 : Ty) (S2 : Ty) (T1 : Ty)
      (T2 : Ty)
      (jm7 : (TyEq G S1 T1 (karr K1 K2)))
      (jm8 : (TyEq G S2 T2 K1)) :
      (TyEq G (tapp S1 S2) (tapp T1 T2) K2)
  | Q_AppAbs (K11 : Kind)
      (K12 : Kind) (T12 : Ty)
      (T2 : Ty)
      (jm9 : (Kinding (etvar G K11) T12 (weakenKind K12 (HS ty H0))))
      (jm10 : (Kinding G T2 K11))
      (H35 : (wfKind (domainEnv G) K12))
      :
      (TyEq G (tapp (tabs K11 T12) T2) (tsubstTy X0 T2 T12) K12)
  | Q_Refl (K : Kind) (T : Ty)
      (jm11 : (Kinding G T K)) :
      (TyEq G T T K)
  | Q_Symm (K : Kind) (S1 : Ty)
      (T : Ty)
      (jm12 : (TyEq G T S1 K)) :
      (TyEq G S1 T K)
  | Q_Trans (K : Kind) (S1 : Ty)
      (T : Ty) (U : Ty)
      (jm13 : (TyEq G S1 U K))
      (jm14 : (TyEq G U T K)) :
      (TyEq G S1 T K).
Inductive Typing (G : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (y : (Index tm))
      (lk0 : (lookup_evar G y T))
      (H19 : (wfTy (domainEnv G) T))
      (H20 : (wfindex (domainEnv G) y))
      : (Typing G (var y) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm15 : (Kinding G T1 (star)))
      (jm16 : (Typing (evar G T1) t (weakenTy T2 (HS tm H0))))
      (H22 : (wfTy (domainEnv G) T2))
      :
      (Typing G (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm17 : (Typing G t1 (tarr T11 T12)))
      (jm18 : (Typing G t2 T11)) :
      (Typing G (app t1 t2) T12)
  | T_Eq (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm19 : (Typing G t S1))
      (jm20 : (TyEq G S1 T (star))) :
      (Typing G t T).
Lemma TRed_cast  :
  (forall (G : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (G0 : Env) (T85 : Ty) (T86 : Ty) (K68 : Kind) ,
    (G = G0) -> (T83 = T85) -> (T84 = T86) -> (K67 = K68) -> (TRed G T83 T84 K67) -> (TRed G0 T85 T86 K68)).
Proof.
  congruence .
Qed.
Lemma Kinding_cast  :
  (forall (G : Env) (T83 : Ty) (K67 : Kind) (G0 : Env) (T84 : Ty) (K68 : Kind) ,
    (G = G0) -> (T83 = T84) -> (K67 = K68) -> (Kinding G T83 K67) -> (Kinding G0 T84 K68)).
Proof.
  congruence .
Qed.
Lemma TRedStar_cast  :
  (forall (G : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (G0 : Env) (T85 : Ty) (T86 : Ty) (K68 : Kind) ,
    (G = G0) -> (T83 = T85) -> (T84 = T86) -> (K67 = K68) -> (TRedStar G T83 T84 K67) -> (TRedStar G0 T85 T86 K68)).
Proof.
  congruence .
Qed.
Lemma TyEq_cast  :
  (forall (G : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (G0 : Env) (T85 : Ty) (T86 : Ty) (K68 : Kind) ,
    (G = G0) -> (T83 = T85) -> (T84 = T86) -> (K67 = K68) -> (TyEq G T83 T84 K67) -> (TyEq G0 T85 T86 K68)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G : Env) (t11 : Tm) (T83 : Ty) (G0 : Env) (t12 : Tm) (T84 : Ty) ,
    (G = G0) -> (t11 = t12) -> (T83 = T84) -> (Typing G t11 T83) -> (Typing G0 t12 T84)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_TRed (G9 : Env) (T98 : Ty) (T99 : Ty) (K79 : Kind) (jm43 : (TRed G9 T98 T99 K79)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c G9 G10)) ,
  (TRed G10 T98 T99 K79)) :=
  match jm43 in (TRed _ T98 T99 K79) return (forall (c : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c G9 G10)) ,
    (TRed G10 T98 T99 K79)) with
    | (QR_Var K76 X34 lk1 H55 H56) => (fun (c : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c G9 G10)) =>
      (QR_Var G10 K76 X34 (shift_evar_lookup_etvar H80 lk1) (shift_wfKind _ _ H55 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80))) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80)) _ H56)))
    | (QR_Arrow S36 S37 T96 T97 jm36 jm37) => (fun (c : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c G9 G10)) =>
      (QR_Arrow G10 S36 S37 T96 T97 (shift_evar_TRed G9 S36 T96 (star) jm36 c G10 (weaken_shift_evar empty H80)) (shift_evar_TRed G9 S37 T97 (star) jm37 c G10 (weaken_shift_evar empty H80))))
    | (QR_Abs K77 K78 S37 T97 jm38 H61 H62) => (fun (c : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c G9 G10)) =>
      (QR_Abs G10 K77 K78 S37 T97 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TRed (etvar G9 K77) S37 T97 (weakenKind K78 (HS ty H0)) jm38 c (etvar G10 K77) (weaken_shift_evar (etvar empty K77) H80))) (shift_wfKind _ _ H61 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80))) (shift_wfKind _ _ H62 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80)))))
    | (QR_App K77 K78 S36 S37 T96 T97 jm39 jm40) => (fun (c : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c G9 G10)) =>
      (QR_App G10 K77 K78 S36 S37 T96 T97 (shift_evar_TRed G9 S36 T96 (karr K78 K77) jm39 c G10 (weaken_shift_evar empty H80)) (shift_evar_TRed G9 S37 T97 K78 jm40 c G10 (weaken_shift_evar empty H80))))
    | (QR_AppAbs K77 K78 S36 S37 T96 T97 jm41 jm42 H71) => (fun (c : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c G9 G10)) =>
      (QR_AppAbs G10 K77 K78 S36 S37 T96 T97 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TRed (etvar G9 K78) S36 T96 (weakenKind K77 (HS ty H0)) jm41 c (etvar G10 K78) (weaken_shift_evar (etvar empty K78) H80))) (shift_evar_TRed G9 S37 T97 K78 jm42 c G10 (weaken_shift_evar empty H80)) (shift_wfKind _ _ H71 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80)))))
  end.
Fixpoint shift_etvar_TRed (G9 : Env) (T98 : Ty) (T99 : Ty) (K79 : Kind) (jm43 : (TRed G9 T98 T99 K79)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c G9 G10)) ,
  (TRed G10 (tshiftTy c T98) (tshiftTy c T99) K79)) :=
  match jm43 in (TRed _ T98 T99 K79) return (forall (c : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c G9 G10)) ,
    (TRed G10 (tshiftTy c T98) (tshiftTy c T99) K79)) with
    | (QR_Var K76 X34 lk1 H55 H56) => (fun (c : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c G9 G10)) =>
      (QR_Var G10 K76 (tshiftIndex c X34) (shift_etvar_lookup_etvar H80 lk1) (tshift_wfKind _ _ H55 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80))) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80)) _ H56)))
    | (QR_Arrow S36 S37 T96 T97 jm36 jm37) => (fun (c : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c G9 G10)) =>
      (QR_Arrow G10 (tshiftTy c S36) (tshiftTy c S37) (tshiftTy c T96) (tshiftTy c T97) (shift_etvar_TRed G9 S36 T96 (star) jm36 c G10 (weaken_shift_etvar empty H80)) (shift_etvar_TRed G9 S37 T97 (star) jm37 c G10 (weaken_shift_etvar empty H80))))
    | (QR_Abs K77 K78 S37 T97 jm38 H61 H62) => (fun (c : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c G9 G10)) =>
      (QR_Abs G10 K77 K78 (tshiftTy (CS c) S37) (tshiftTy (CS c) T97) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TRed (etvar G9 K77) S37 T97 (weakenKind K78 (HS ty H0)) jm38 (CS c) (etvar G10 K77) (weaken_shift_etvar (etvar empty K77) H80))) (tshift_wfKind _ _ H61 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80))) (tshift_wfKind _ _ H62 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80)))))
    | (QR_App K77 K78 S36 S37 T96 T97 jm39 jm40) => (fun (c : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c G9 G10)) =>
      (QR_App G10 K77 K78 (tshiftTy c S36) (tshiftTy c S37) (tshiftTy c T96) (tshiftTy c T97) (shift_etvar_TRed G9 S36 T96 (karr K78 K77) jm39 c G10 (weaken_shift_etvar empty H80)) (shift_etvar_TRed G9 S37 T97 K78 jm40 c G10 (weaken_shift_etvar empty H80))))
    | (QR_AppAbs K77 K78 S36 S37 T96 T97 jm41 jm42 H71) => (fun (c : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c G9 G10)) =>
      (TRed_cast G10 _ _ _ G10 (tshiftTy c (tapp (tabs K78 S36) S37)) (tshiftTy c (tsubstTy X0 T97 T96)) K77 eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T96 c T97)) eq_refl (QR_AppAbs G10 K77 K78 (tshiftTy (CS c) S36) (tshiftTy c S37) (tshiftTy (CS c) T96) (tshiftTy c T97) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TRed (etvar G9 K78) S36 T96 (weakenKind K77 (HS ty H0)) jm41 (CS c) (etvar G10 K78) (weaken_shift_etvar (etvar empty K78) H80))) (shift_etvar_TRed G9 S37 T97 K78 jm42 c G10 (weaken_shift_etvar empty H80)) (tshift_wfKind _ _ H71 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80))))))
  end.
Fixpoint shift_evar_Kinding (G9 : Env) (T98 : Ty) (K81 : Kind) (jm41 : (Kinding G9 T98 K81)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H68 : (shift_evar c G9 G10)) ,
  (Kinding G10 T98 K81)) :=
  match jm41 in (Kinding _ T98 K81) return (forall (c : (Cutoff tm)) (G10 : Env) (H68 : (shift_evar c G9 G10)) ,
    (Kinding G10 T98 K81)) with
    | (K_TVar K76 X34 lk1 H55 H56) => (fun (c : (Cutoff tm)) (G10 : Env) (H68 : (shift_evar c G9 G10)) =>
      (K_TVar G10 K76 X34 (shift_evar_lookup_etvar H68 lk1) (shift_wfKind _ _ H55 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H68))) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H68)) _ H56)))
    | (K_Abs K77 K80 T97 jm36 H57 H58) => (fun (c : (Cutoff tm)) (G10 : Env) (H68 : (shift_evar c G9 G10)) =>
      (K_Abs G10 K77 K80 T97 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Kinding (etvar G9 K77) T97 (weakenKind K80 (HS ty H0)) jm36 c (etvar G10 K77) (weaken_shift_evar (etvar empty K77) H68))) (shift_wfKind _ _ H57 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H68))) (shift_wfKind _ _ H58 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H68)))))
    | (K_App K78 K79 T96 T97 jm37 jm38) => (fun (c : (Cutoff tm)) (G10 : Env) (H68 : (shift_evar c G9 G10)) =>
      (K_App G10 K78 K79 T96 T97 (shift_evar_Kinding G9 T96 (karr K78 K79) jm37 c G10 (weaken_shift_evar empty H68)) (shift_evar_Kinding G9 T97 K78 jm38 c G10 (weaken_shift_evar empty H68))))
    | (K_Arr T96 T97 jm39 jm40) => (fun (c : (Cutoff tm)) (G10 : Env) (H68 : (shift_evar c G9 G10)) =>
      (K_Arr G10 T96 T97 (shift_evar_Kinding G9 T96 (star) jm39 c G10 (weaken_shift_evar empty H68)) (shift_evar_Kinding G9 T97 (star) jm40 c G10 (weaken_shift_evar empty H68))))
  end.
Fixpoint shift_etvar_Kinding (G9 : Env) (T98 : Ty) (K81 : Kind) (jm41 : (Kinding G9 T98 K81)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H68 : (shift_etvar c G9 G10)) ,
  (Kinding G10 (tshiftTy c T98) K81)) :=
  match jm41 in (Kinding _ T98 K81) return (forall (c : (Cutoff ty)) (G10 : Env) (H68 : (shift_etvar c G9 G10)) ,
    (Kinding G10 (tshiftTy c T98) K81)) with
    | (K_TVar K76 X34 lk1 H55 H56) => (fun (c : (Cutoff ty)) (G10 : Env) (H68 : (shift_etvar c G9 G10)) =>
      (K_TVar G10 K76 (tshiftIndex c X34) (shift_etvar_lookup_etvar H68 lk1) (tshift_wfKind _ _ H55 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H68))) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H68)) _ H56)))
    | (K_Abs K77 K80 T97 jm36 H57 H58) => (fun (c : (Cutoff ty)) (G10 : Env) (H68 : (shift_etvar c G9 G10)) =>
      (K_Abs G10 K77 K80 (tshiftTy (CS c) T97) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_Kinding (etvar G9 K77) T97 (weakenKind K80 (HS ty H0)) jm36 (CS c) (etvar G10 K77) (weaken_shift_etvar (etvar empty K77) H68))) (tshift_wfKind _ _ H57 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H68))) (tshift_wfKind _ _ H58 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H68)))))
    | (K_App K78 K79 T96 T97 jm37 jm38) => (fun (c : (Cutoff ty)) (G10 : Env) (H68 : (shift_etvar c G9 G10)) =>
      (K_App G10 K78 K79 (tshiftTy c T96) (tshiftTy c T97) (shift_etvar_Kinding G9 T96 (karr K78 K79) jm37 c G10 (weaken_shift_etvar empty H68)) (shift_etvar_Kinding G9 T97 K78 jm38 c G10 (weaken_shift_etvar empty H68))))
    | (K_Arr T96 T97 jm39 jm40) => (fun (c : (Cutoff ty)) (G10 : Env) (H68 : (shift_etvar c G9 G10)) =>
      (K_Arr G10 (tshiftTy c T96) (tshiftTy c T97) (shift_etvar_Kinding G9 T96 (star) jm39 c G10 (weaken_shift_etvar empty H68)) (shift_etvar_Kinding G9 T97 (star) jm40 c G10 (weaken_shift_etvar empty H68))))
  end.
Fixpoint shift_evar_TRedStar (G9 : Env) (T97 : Ty) (T98 : Ty) (K77 : Kind) (jm39 : (TRedStar G9 T97 T98 K77)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H64 : (shift_evar c G9 G10)) ,
  (TRedStar G10 T97 T98 K77)) :=
  match jm39 in (TRedStar _ T97 T98 K77) return (forall (c : (Cutoff tm)) (G10 : Env) (H64 : (shift_evar c G9 G10)) ,
    (TRedStar G10 T97 T98 K77)) with
    | (QRS_Nil K76 T96 jm36) => (fun (c : (Cutoff tm)) (G10 : Env) (H64 : (shift_evar c G9 G10)) =>
      (QRS_Nil G10 K76 T96 (shift_evar_Kinding G9 T96 K76 jm36 c G10 (weaken_shift_evar empty H64))))
    | (QRS_Cons K76 S36 T96 U3 jm37 jm38) => (fun (c : (Cutoff tm)) (G10 : Env) (H64 : (shift_evar c G9 G10)) =>
      (QRS_Cons G10 K76 S36 T96 U3 (shift_evar_TRedStar G9 S36 T96 K76 jm37 c G10 (weaken_shift_evar empty H64)) (shift_evar_TRed G9 T96 U3 K76 jm38 c G10 (weaken_shift_evar empty H64))))
  end.
Fixpoint shift_etvar_TRedStar (G9 : Env) (T97 : Ty) (T98 : Ty) (K77 : Kind) (jm39 : (TRedStar G9 T97 T98 K77)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H64 : (shift_etvar c G9 G10)) ,
  (TRedStar G10 (tshiftTy c T97) (tshiftTy c T98) K77)) :=
  match jm39 in (TRedStar _ T97 T98 K77) return (forall (c : (Cutoff ty)) (G10 : Env) (H64 : (shift_etvar c G9 G10)) ,
    (TRedStar G10 (tshiftTy c T97) (tshiftTy c T98) K77)) with
    | (QRS_Nil K76 T96 jm36) => (fun (c : (Cutoff ty)) (G10 : Env) (H64 : (shift_etvar c G9 G10)) =>
      (QRS_Nil G10 K76 (tshiftTy c T96) (shift_etvar_Kinding G9 T96 K76 jm36 c G10 (weaken_shift_etvar empty H64))))
    | (QRS_Cons K76 S36 T96 U3 jm37 jm38) => (fun (c : (Cutoff ty)) (G10 : Env) (H64 : (shift_etvar c G9 G10)) =>
      (QRS_Cons G10 K76 (tshiftTy c S36) (tshiftTy c T96) (tshiftTy c U3) (shift_etvar_TRedStar G9 S36 T96 K76 jm37 c G10 (weaken_shift_etvar empty H64)) (shift_etvar_TRed G9 T96 U3 K76 jm38 c G10 (weaken_shift_etvar empty H64))))
  end.
Fixpoint shift_evar_TyEq (G9 : Env) (T100 : Ty) (T101 : Ty) (K81 : Kind) (jm47 : (TyEq G9 T100 T101 K81)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) ,
  (TyEq G10 T100 T101 K81)) :=
  match jm47 in (TyEq _ T100 T101 K81) return (forall (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) ,
    (TyEq G10 T100 T101 K81)) with
    | (Q_Arrow S36 S37 T97 T99 jm41 jm42) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (Q_Arrow G10 S36 S37 T97 T99 (shift_evar_TyEq G9 S36 T97 (star) jm41 c G10 (weaken_shift_evar empty H85)) (shift_evar_TyEq G9 S37 T99 (star) jm42 c G10 (weaken_shift_evar empty H85))))
    | (Q_Abs K77 K80 S37 T99 jm43 H59 H60) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (Q_Abs G10 K77 K80 S37 T99 (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TyEq (etvar G9 K77) S37 T99 (weakenKind K80 (HS ty H0)) jm43 c (etvar G10 K77) (weaken_shift_evar (etvar empty K77) H85))) (shift_wfKind _ _ H59 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85))) (shift_wfKind _ _ H60 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)))))
    | (Q_App K77 K80 S36 S37 T97 T99 jm44 jm45) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (Q_App G10 K77 K80 S36 S37 T97 T99 (shift_evar_TyEq G9 S36 T97 (karr K77 K80) jm44 c G10 (weaken_shift_evar empty H85)) (shift_evar_TyEq G9 S37 T99 K77 jm45 c G10 (weaken_shift_evar empty H85))))
    | (Q_AppAbs K78 K79 T98 T99 jm46 jm36 H70) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (Q_AppAbs G10 K78 K79 T98 T99 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Kinding (etvar G9 K78) T98 (weakenKind K79 (HS ty H0)) jm46 c (etvar G10 K78) (weaken_shift_evar (etvar empty K78) H85))) (shift_evar_Kinding G9 T99 K78 jm36 c G10 (weaken_shift_evar empty H85)) (shift_wfKind _ _ H70 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)))))
    | (Q_Refl K76 T96 jm37) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (Q_Refl G10 K76 T96 (shift_evar_Kinding G9 T96 K76 jm37 c G10 (weaken_shift_evar empty H85))))
    | (Q_Symm K76 S36 T96 jm38) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (Q_Symm G10 K76 S36 T96 (shift_evar_TyEq G9 T96 S36 K76 jm38 c G10 (weaken_shift_evar empty H85))))
    | (Q_Trans K76 S36 T96 U3 jm39 jm40) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (Q_Trans G10 K76 S36 T96 U3 (shift_evar_TyEq G9 S36 U3 K76 jm39 c G10 (weaken_shift_evar empty H85)) (shift_evar_TyEq G9 U3 T96 K76 jm40 c G10 (weaken_shift_evar empty H85))))
  end.
Fixpoint shift_etvar_TyEq (G9 : Env) (T100 : Ty) (T101 : Ty) (K81 : Kind) (jm47 : (TyEq G9 T100 T101 K81)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) ,
  (TyEq G10 (tshiftTy c T100) (tshiftTy c T101) K81)) :=
  match jm47 in (TyEq _ T100 T101 K81) return (forall (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) ,
    (TyEq G10 (tshiftTy c T100) (tshiftTy c T101) K81)) with
    | (Q_Arrow S36 S37 T97 T99 jm41 jm42) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Q_Arrow G10 (tshiftTy c S36) (tshiftTy c S37) (tshiftTy c T97) (tshiftTy c T99) (shift_etvar_TyEq G9 S36 T97 (star) jm41 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_TyEq G9 S37 T99 (star) jm42 c G10 (weaken_shift_etvar empty H85))))
    | (Q_Abs K77 K80 S37 T99 jm43 H59 H60) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Q_Abs G10 K77 K80 (tshiftTy (CS c) S37) (tshiftTy (CS c) T99) (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TyEq (etvar G9 K77) S37 T99 (weakenKind K80 (HS ty H0)) jm43 (CS c) (etvar G10 K77) (weaken_shift_etvar (etvar empty K77) H85))) (tshift_wfKind _ _ H59 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85))) (tshift_wfKind _ _ H60 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85)))))
    | (Q_App K77 K80 S36 S37 T97 T99 jm44 jm45) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Q_App G10 K77 K80 (tshiftTy c S36) (tshiftTy c S37) (tshiftTy c T97) (tshiftTy c T99) (shift_etvar_TyEq G9 S36 T97 (karr K77 K80) jm44 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_TyEq G9 S37 T99 K77 jm45 c G10 (weaken_shift_etvar empty H85))))
    | (Q_AppAbs K78 K79 T98 T99 jm46 jm36 H70) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (TyEq_cast G10 _ _ _ G10 (tshiftTy c (tapp (tabs K78 T98) T99)) (tshiftTy c (tsubstTy X0 T99 T98)) K79 eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T98 c T99)) eq_refl (Q_AppAbs G10 K78 K79 (tshiftTy (CS c) T98) (tshiftTy c T99) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_Kinding (etvar G9 K78) T98 (weakenKind K79 (HS ty H0)) jm46 (CS c) (etvar G10 K78) (weaken_shift_etvar (etvar empty K78) H85))) (shift_etvar_Kinding G9 T99 K78 jm36 c G10 (weaken_shift_etvar empty H85)) (tshift_wfKind _ _ H70 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85))))))
    | (Q_Refl K76 T96 jm37) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Q_Refl G10 K76 (tshiftTy c T96) (shift_etvar_Kinding G9 T96 K76 jm37 c G10 (weaken_shift_etvar empty H85))))
    | (Q_Symm K76 S36 T96 jm38) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Q_Symm G10 K76 (tshiftTy c S36) (tshiftTy c T96) (shift_etvar_TyEq G9 T96 S36 K76 jm38 c G10 (weaken_shift_etvar empty H85))))
    | (Q_Trans K76 S36 T96 U3 jm39 jm40) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Q_Trans G10 K76 (tshiftTy c S36) (tshiftTy c T96) (tshiftTy c U3) (shift_etvar_TyEq G9 S36 U3 K76 jm39 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_TyEq G9 U3 T96 K76 jm40 c G10 (weaken_shift_etvar empty H85))))
  end.
Fixpoint shift_evar_Typing (G9 : Env) (t15 : Tm) (T101 : Ty) (jm42 : (Typing G9 t15 T101)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H69 : (shift_evar c G9 G10)) ,
  (Typing G10 (shiftTm c t15) T101)) :=
  match jm42 in (Typing _ t15 T101) return (forall (c : (Cutoff tm)) (G10 : Env) (H69 : (shift_evar c G9 G10)) ,
    (Typing G10 (shiftTm c t15) T101)) with
    | (T_Var T96 y1 lk1 H55 H56) => (fun (c : (Cutoff tm)) (G10 : Env) (H69 : (shift_evar c G9 G10)) =>
      (T_Var G10 T96 (shiftIndex c y1) (shift_evar_lookup_evar H69 lk1) (shift_wfTy _ _ H55 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H69))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H69)) _ H56)))
    | (T_Abs T97 T100 t12 jm36 jm37 H58) => (fun (c : (Cutoff tm)) (G10 : Env) (H69 : (shift_evar c G9 G10)) =>
      (T_Abs G10 T97 T100 (shiftTm (CS c) t12) (shift_evar_Kinding G9 T97 (star) jm36 c G10 (weaken_shift_evar empty H69)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G9 T97) t12 (weakenTy T100 (HS tm H0)) jm37 (CS c) (evar G10 T97) (weaken_shift_evar (evar empty T97) H69))) (shift_wfTy _ _ H58 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H69)))))
    | (T_App T98 T99 t13 t14 jm38 jm39) => (fun (c : (Cutoff tm)) (G10 : Env) (H69 : (shift_evar c G9 G10)) =>
      (T_App G10 T98 T99 (shiftTm c t13) (shiftTm c t14) (shift_evar_Typing G9 t13 (tarr T98 T99) jm38 c G10 (weaken_shift_evar empty H69)) (shift_evar_Typing G9 t14 T98 jm39 c G10 (weaken_shift_evar empty H69))))
    | (T_Eq S36 T96 t12 jm40 jm41) => (fun (c : (Cutoff tm)) (G10 : Env) (H69 : (shift_evar c G9 G10)) =>
      (T_Eq G10 S36 T96 (shiftTm c t12) (shift_evar_Typing G9 t12 S36 jm40 c G10 (weaken_shift_evar empty H69)) (shift_evar_TyEq G9 S36 T96 (star) jm41 c G10 (weaken_shift_evar empty H69))))
  end.
Fixpoint shift_etvar_Typing (G9 : Env) (t15 : Tm) (T101 : Ty) (jm42 : (Typing G9 t15 T101)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H69 : (shift_etvar c G9 G10)) ,
  (Typing G10 (tshiftTm c t15) (tshiftTy c T101))) :=
  match jm42 in (Typing _ t15 T101) return (forall (c : (Cutoff ty)) (G10 : Env) (H69 : (shift_etvar c G9 G10)) ,
    (Typing G10 (tshiftTm c t15) (tshiftTy c T101))) with
    | (T_Var T96 y1 lk1 H55 H56) => (fun (c : (Cutoff ty)) (G10 : Env) (H69 : (shift_etvar c G9 G10)) =>
      (T_Var G10 (tshiftTy c T96) y1 (shift_etvar_lookup_evar H69 lk1) (tshift_wfTy _ _ H55 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H69))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H69)) _ H56)))
    | (T_Abs T97 T100 t12 jm36 jm37 H58) => (fun (c : (Cutoff ty)) (G10 : Env) (H69 : (shift_etvar c G9 G10)) =>
      (T_Abs G10 (tshiftTy c T97) (tshiftTy c T100) (tshiftTm c t12) (shift_etvar_Kinding G9 T97 (star) jm36 c G10 (weaken_shift_etvar empty H69)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c T100)) (shift_etvar_Typing (evar G9 T97) t12 (weakenTy T100 (HS tm H0)) jm37 c (evar G10 (tshiftTy c T97)) (weaken_shift_etvar (evar empty T97) H69))) (tshift_wfTy _ _ H58 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H69)))))
    | (T_App T98 T99 t13 t14 jm38 jm39) => (fun (c : (Cutoff ty)) (G10 : Env) (H69 : (shift_etvar c G9 G10)) =>
      (T_App G10 (tshiftTy c T98) (tshiftTy c T99) (tshiftTm c t13) (tshiftTm c t14) (shift_etvar_Typing G9 t13 (tarr T98 T99) jm38 c G10 (weaken_shift_etvar empty H69)) (shift_etvar_Typing G9 t14 T98 jm39 c G10 (weaken_shift_etvar empty H69))))
    | (T_Eq S36 T96 t12 jm40 jm41) => (fun (c : (Cutoff ty)) (G10 : Env) (H69 : (shift_etvar c G9 G10)) =>
      (T_Eq G10 (tshiftTy c S36) (tshiftTy c T96) (tshiftTm c t12) (shift_etvar_Typing G9 t12 S36 jm40 c G10 (weaken_shift_etvar empty H69)) (shift_etvar_TyEq G9 S36 T96 (star) jm41 c G10 (weaken_shift_etvar empty H69))))
  end.
 Hint Resolve shift_evar_Kinding shift_etvar_Kinding shift_evar_TRed shift_etvar_TRed shift_evar_TRedStar shift_etvar_TRedStar shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_Kinding shift_etvar_Kinding shift_evar_TRed shift_etvar_TRed shift_evar_TRedStar shift_etvar_TRedStar shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_TRed (G : Env) :
(forall (G0 : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (jm31 : (TRed G0 T83 T84 K67)) ,
  (TRed (appendEnv G0 G) (weakenTy T83 (domainEnv G)) (weakenTy T84 (domainEnv G)) (weakenKind K67 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (jm31 : (TRed G0 T83 T84 K67)) ,
    (TRed (appendEnv G0 G) (weakenTy T83 (domainEnv G)) (weakenTy T84 (domainEnv G)) (weakenKind K67 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (jm31 : (TRed G0 T83 T84 K67)) =>
      jm31)
    | (evar G T85) => (fun (G0 : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (jm31 : (TRed G0 T83 T84 K67)) =>
      (shift_evar_TRed (appendEnv G0 G) (weakenTy T83 (domainEnv G)) (weakenTy T84 (domainEnv G)) (weakenKind K67 (domainEnv G)) (weaken_TRed G G0 T83 T84 K67 jm31) C0 (evar (appendEnv G0 G) T85) shift_evar_here))
    | (etvar G K68) => (fun (G0 : Env) (T83 : Ty) (T84 : Ty) (K67 : Kind) (jm31 : (TRed G0 T83 T84 K67)) =>
      (shift_etvar_TRed (appendEnv G0 G) (weakenTy T83 (domainEnv G)) (weakenTy T84 (domainEnv G)) (weakenKind K67 (domainEnv G)) (weaken_TRed G G0 T83 T84 K67 jm31) C0 (etvar (appendEnv G0 G) K68) shift_etvar_here))
  end.
Fixpoint weaken_Kinding (G1 : Env) :
(forall (G2 : Env) (T86 : Ty) (K69 : Kind) (jm32 : (Kinding G2 T86 K69)) ,
  (Kinding (appendEnv G2 G1) (weakenTy T86 (domainEnv G1)) (weakenKind K69 (domainEnv G1)))) :=
  match G1 return (forall (G2 : Env) (T86 : Ty) (K69 : Kind) (jm32 : (Kinding G2 T86 K69)) ,
    (Kinding (appendEnv G2 G1) (weakenTy T86 (domainEnv G1)) (weakenKind K69 (domainEnv G1)))) with
    | (empty) => (fun (G2 : Env) (T86 : Ty) (K69 : Kind) (jm32 : (Kinding G2 T86 K69)) =>
      jm32)
    | (evar G1 T87) => (fun (G2 : Env) (T86 : Ty) (K69 : Kind) (jm32 : (Kinding G2 T86 K69)) =>
      (shift_evar_Kinding (appendEnv G2 G1) (weakenTy T86 (domainEnv G1)) (weakenKind K69 (domainEnv G1)) (weaken_Kinding G1 G2 T86 K69 jm32) C0 (evar (appendEnv G2 G1) T87) shift_evar_here))
    | (etvar G1 K70) => (fun (G2 : Env) (T86 : Ty) (K69 : Kind) (jm32 : (Kinding G2 T86 K69)) =>
      (shift_etvar_Kinding (appendEnv G2 G1) (weakenTy T86 (domainEnv G1)) (weakenKind K69 (domainEnv G1)) (weaken_Kinding G1 G2 T86 K69 jm32) C0 (etvar (appendEnv G2 G1) K70) shift_etvar_here))
  end.
Fixpoint weaken_TRedStar (G3 : Env) :
(forall (G4 : Env) (T88 : Ty) (T89 : Ty) (K71 : Kind) (jm33 : (TRedStar G4 T88 T89 K71)) ,
  (TRedStar (appendEnv G4 G3) (weakenTy T88 (domainEnv G3)) (weakenTy T89 (domainEnv G3)) (weakenKind K71 (domainEnv G3)))) :=
  match G3 return (forall (G4 : Env) (T88 : Ty) (T89 : Ty) (K71 : Kind) (jm33 : (TRedStar G4 T88 T89 K71)) ,
    (TRedStar (appendEnv G4 G3) (weakenTy T88 (domainEnv G3)) (weakenTy T89 (domainEnv G3)) (weakenKind K71 (domainEnv G3)))) with
    | (empty) => (fun (G4 : Env) (T88 : Ty) (T89 : Ty) (K71 : Kind) (jm33 : (TRedStar G4 T88 T89 K71)) =>
      jm33)
    | (evar G3 T90) => (fun (G4 : Env) (T88 : Ty) (T89 : Ty) (K71 : Kind) (jm33 : (TRedStar G4 T88 T89 K71)) =>
      (shift_evar_TRedStar (appendEnv G4 G3) (weakenTy T88 (domainEnv G3)) (weakenTy T89 (domainEnv G3)) (weakenKind K71 (domainEnv G3)) (weaken_TRedStar G3 G4 T88 T89 K71 jm33) C0 (evar (appendEnv G4 G3) T90) shift_evar_here))
    | (etvar G3 K72) => (fun (G4 : Env) (T88 : Ty) (T89 : Ty) (K71 : Kind) (jm33 : (TRedStar G4 T88 T89 K71)) =>
      (shift_etvar_TRedStar (appendEnv G4 G3) (weakenTy T88 (domainEnv G3)) (weakenTy T89 (domainEnv G3)) (weakenKind K71 (domainEnv G3)) (weaken_TRedStar G3 G4 T88 T89 K71 jm33) C0 (etvar (appendEnv G4 G3) K72) shift_etvar_here))
  end.
Fixpoint weaken_TyEq (G5 : Env) :
(forall (G6 : Env) (T91 : Ty) (T92 : Ty) (K73 : Kind) (jm34 : (TyEq G6 T91 T92 K73)) ,
  (TyEq (appendEnv G6 G5) (weakenTy T91 (domainEnv G5)) (weakenTy T92 (domainEnv G5)) (weakenKind K73 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (T91 : Ty) (T92 : Ty) (K73 : Kind) (jm34 : (TyEq G6 T91 T92 K73)) ,
    (TyEq (appendEnv G6 G5) (weakenTy T91 (domainEnv G5)) (weakenTy T92 (domainEnv G5)) (weakenKind K73 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (T91 : Ty) (T92 : Ty) (K73 : Kind) (jm34 : (TyEq G6 T91 T92 K73)) =>
      jm34)
    | (evar G5 T93) => (fun (G6 : Env) (T91 : Ty) (T92 : Ty) (K73 : Kind) (jm34 : (TyEq G6 T91 T92 K73)) =>
      (shift_evar_TyEq (appendEnv G6 G5) (weakenTy T91 (domainEnv G5)) (weakenTy T92 (domainEnv G5)) (weakenKind K73 (domainEnv G5)) (weaken_TyEq G5 G6 T91 T92 K73 jm34) C0 (evar (appendEnv G6 G5) T93) shift_evar_here))
    | (etvar G5 K74) => (fun (G6 : Env) (T91 : Ty) (T92 : Ty) (K73 : Kind) (jm34 : (TyEq G6 T91 T92 K73)) =>
      (shift_etvar_TyEq (appendEnv G6 G5) (weakenTy T91 (domainEnv G5)) (weakenTy T92 (domainEnv G5)) (weakenKind K73 (domainEnv G5)) (weaken_TyEq G5 G6 T91 T92 K73 jm34) C0 (etvar (appendEnv G6 G5) K74) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G7 : Env) :
(forall (G8 : Env) (t11 : Tm) (T94 : Ty) (jm35 : (Typing G8 t11 T94)) ,
  (Typing (appendEnv G8 G7) (weakenTm t11 (domainEnv G7)) (weakenTy T94 (domainEnv G7)))) :=
  match G7 return (forall (G8 : Env) (t11 : Tm) (T94 : Ty) (jm35 : (Typing G8 t11 T94)) ,
    (Typing (appendEnv G8 G7) (weakenTm t11 (domainEnv G7)) (weakenTy T94 (domainEnv G7)))) with
    | (empty) => (fun (G8 : Env) (t11 : Tm) (T94 : Ty) (jm35 : (Typing G8 t11 T94)) =>
      jm35)
    | (evar G7 T95) => (fun (G8 : Env) (t11 : Tm) (T94 : Ty) (jm35 : (Typing G8 t11 T94)) =>
      (shift_evar_Typing (appendEnv G8 G7) (weakenTm t11 (domainEnv G7)) (weakenTy T94 (domainEnv G7)) (weaken_Typing G7 G8 t11 T94 jm35) C0 (evar (appendEnv G8 G7) T95) shift_evar_here))
    | (etvar G7 K75) => (fun (G8 : Env) (t11 : Tm) (T94 : Ty) (jm35 : (Typing G8 t11 T94)) =>
      (shift_etvar_Typing (appendEnv G8 G7) (weakenTm t11 (domainEnv G7)) (weakenTy T94 (domainEnv G7)) (weaken_Typing G7 G8 t11 T94 jm35) C0 (etvar (appendEnv G8 G7) K75) shift_etvar_here))
  end.
Fixpoint TRed_wf_0 (G : Env) (T96 : Ty) (T97 : Ty) (K76 : Kind) (jm36 : (TRed G T96 T97 K76)) {struct jm36} :
(wfTy (domainEnv G) T96) :=
  match jm36 in (TRed _ T96 T97 K76) return (wfTy (domainEnv G) T96) with
    | (QR_Var K X lk H20 H21) => (wfTy_tvar (domainEnv G) _ H21)
    | (QR_Arrow S1 S2 T1 T2 jm21 jm22) => (wfTy_tarr (domainEnv G) (TRed_wf_0 G S1 T1 (star) jm21) (TRed_wf_0 G S2 T2 (star) jm22))
    | (QR_Abs K1 K2 S2 T2 jm23 H26 H27) => (wfTy_tabs (domainEnv G) H26 (TRed_wf_0 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm23))
    | (QR_App K1 K2 S1 S2 T1 T2 jm24 jm25) => (wfTy_tapp (domainEnv G) (TRed_wf_0 G S1 T1 (karr K2 K1) jm24) (TRed_wf_0 G S2 T2 K2 jm25))
    | (QR_AppAbs K1 K2 S1 S2 T1 T2 jm26 jm27 H36) => (wfTy_tapp (domainEnv G) (wfTy_tabs (domainEnv G) (TRed_wf_2 G S2 T2 K2 jm27) (TRed_wf_0 (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0)) jm26)) (TRed_wf_0 G S2 T2 K2 jm27))
  end
with TRed_wf_1 (G : Env) (T96 : Ty) (T97 : Ty) (K76 : Kind) (jm37 : (TRed G T96 T97 K76)) {struct jm37} :
(wfTy (domainEnv G) T97) :=
  match jm37 in (TRed _ T96 T97 K76) return (wfTy (domainEnv G) T97) with
    | (QR_Var K X lk H20 H21) => (wfTy_tvar (domainEnv G) _ H21)
    | (QR_Arrow S1 S2 T1 T2 jm21 jm22) => (wfTy_tarr (domainEnv G) (TRed_wf_1 G S1 T1 (star) jm21) (TRed_wf_1 G S2 T2 (star) jm22))
    | (QR_Abs K1 K2 S2 T2 jm23 H26 H27) => (wfTy_tabs (domainEnv G) H26 (TRed_wf_1 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm23))
    | (QR_App K1 K2 S1 S2 T1 T2 jm24 jm25) => (wfTy_tapp (domainEnv G) (TRed_wf_1 G S1 T1 (karr K2 K1) jm24) (TRed_wf_1 G S2 T2 K2 jm25))
    | (QR_AppAbs K1 K2 S1 S2 T1 T2 jm26 jm27 H36) => (substhvl_ty_wfTy (TRed_wf_1 G S2 T2 K2 jm27) (HS ty (domainEnv G)) T1 (TRed_wf_1 (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0)) jm26) (substhvl_ty_here (domainEnv G)))
  end
with TRed_wf_2 (G : Env) (T96 : Ty) (T97 : Ty) (K76 : Kind) (jm38 : (TRed G T96 T97 K76)) {struct jm38} :
(wfKind (domainEnv G) K76) :=
  match jm38 in (TRed _ T96 T97 K76) return (wfKind (domainEnv G) K76) with
    | (QR_Var K X lk H20 H21) => H20
    | (QR_Arrow S1 S2 T1 T2 jm21 jm22) => (wfKind_star (domainEnv G))
    | (QR_Abs K1 K2 S2 T2 jm23 H26 H27) => (wfKind_karr (domainEnv G) H26 H27)
    | (QR_App K1 K2 S1 S2 T1 T2 jm24 jm25) => (inversion_wfKind_karr_1 (domainEnv G) K2 K1 (TRed_wf_2 G S1 T1 (karr K2 K1) jm24))
    | (QR_AppAbs K1 K2 S1 S2 T1 T2 jm26 jm27 H36) => H36
  end.
Fixpoint Kinding_wf_0 (G : Env) (T98 : Ty) (K77 : Kind) (jm39 : (Kinding G T98 K77)) {struct jm39} :
(wfTy (domainEnv G) T98) :=
  match jm39 in (Kinding _ T98 K77) return (wfTy (domainEnv G) T98) with
    | (K_TVar K X lk1 H19 H20) => (wfTy_tvar (domainEnv G) _ H20)
    | (K_Abs K1 K2 T2 jm H21 H22) => (wfTy_tabs (domainEnv G) H21 (Kinding_wf_0 (etvar G K1) T2 (weakenKind K2 (HS ty H0)) jm))
    | (K_App K11 K12 T1 T2 jm0 jm1) => (wfTy_tapp (domainEnv G) (Kinding_wf_0 G T1 (karr K11 K12) jm0) (Kinding_wf_0 G T2 K11 jm1))
    | (K_Arr T1 T2 jm2 jm3) => (wfTy_tarr (domainEnv G) (Kinding_wf_0 G T1 (star) jm2) (Kinding_wf_0 G T2 (star) jm3))
  end
with Kinding_wf_1 (G : Env) (T98 : Ty) (K77 : Kind) (jm40 : (Kinding G T98 K77)) {struct jm40} :
(wfKind (domainEnv G) K77) :=
  match jm40 in (Kinding _ T98 K77) return (wfKind (domainEnv G) K77) with
    | (K_TVar K X lk2 H19 H20) => H19
    | (K_Abs K1 K2 T2 jm H21 H22) => (wfKind_karr (domainEnv G) H21 H22)
    | (K_App K11 K12 T1 T2 jm0 jm1) => (inversion_wfKind_karr_1 (domainEnv G) K11 K12 (Kinding_wf_1 G T1 (karr K11 K12) jm0))
    | (K_Arr T1 T2 jm2 jm3) => (wfKind_star (domainEnv G))
  end.
Fixpoint TRedStar_wf_0 (G : Env) (T99 : Ty) (T100 : Ty) (K78 : Kind) (jm41 : (TRedStar G T99 T100 K78)) {struct jm41} :
(wfTy (domainEnv G) T99) :=
  match jm41 in (TRedStar _ T99 T100 K78) return (wfTy (domainEnv G) T99) with
    | (QRS_Nil K T jm28) => (Kinding_wf_0 G T K jm28)
    | (QRS_Cons K S1 T U jm29 jm30) => (TRedStar_wf_0 G S1 T K jm29)
  end
with TRedStar_wf_1 (G : Env) (T99 : Ty) (T100 : Ty) (K78 : Kind) (jm42 : (TRedStar G T99 T100 K78)) {struct jm42} :
(wfTy (domainEnv G) T100) :=
  match jm42 in (TRedStar _ T99 T100 K78) return (wfTy (domainEnv G) T100) with
    | (QRS_Nil K T jm28) => (Kinding_wf_0 G T K jm28)
    | (QRS_Cons K S1 T U jm29 jm30) => (TRed_wf_1 G T U K jm30)
  end
with TRedStar_wf_2 (G : Env) (T99 : Ty) (T100 : Ty) (K78 : Kind) (jm43 : (TRedStar G T99 T100 K78)) {struct jm43} :
(wfKind (domainEnv G) K78) :=
  match jm43 in (TRedStar _ T99 T100 K78) return (wfKind (domainEnv G) K78) with
    | (QRS_Nil K T jm28) => (Kinding_wf_1 G T K jm28)
    | (QRS_Cons K S1 T U jm29 jm30) => (TRed_wf_2 G T U K jm30)
  end.
Fixpoint TyEq_wf_0 (G : Env) (T101 : Ty) (T102 : Ty) (K79 : Kind) (jm44 : (TyEq G T101 T102 K79)) {struct jm44} :
(wfTy (domainEnv G) T101) :=
  match jm44 in (TyEq _ T101 T102 K79) return (wfTy (domainEnv G) T101) with
    | (Q_Arrow S1 S2 T1 T2 jm4 jm5) => (wfTy_tarr (domainEnv G) (TyEq_wf_0 G S1 T1 (star) jm4) (TyEq_wf_0 G S2 T2 (star) jm5))
    | (Q_Abs K1 K2 S2 T2 jm6 H24 H25) => (wfTy_tabs (domainEnv G) H24 (TyEq_wf_0 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm6))
    | (Q_App K1 K2 S1 S2 T1 T2 jm7 jm8) => (wfTy_tapp (domainEnv G) (TyEq_wf_0 G S1 T1 (karr K1 K2) jm7) (TyEq_wf_0 G S2 T2 K1 jm8))
    | (Q_AppAbs K11 K12 T12 T2 jm9 jm10 H35) => (wfTy_tapp (domainEnv G) (wfTy_tabs (domainEnv G) (Kinding_wf_1 G T2 K11 jm10) (Kinding_wf_0 (etvar G K11) T12 (weakenKind K12 (HS ty H0)) jm9)) (Kinding_wf_0 G T2 K11 jm10))
    | (Q_Refl K T jm11) => (Kinding_wf_0 G T K jm11)
    | (Q_Symm K S1 T jm12) => (TyEq_wf_1 G T S1 K jm12)
    | (Q_Trans K S1 T U jm13 jm14) => (TyEq_wf_0 G S1 U K jm13)
  end
with TyEq_wf_1 (G : Env) (T101 : Ty) (T102 : Ty) (K79 : Kind) (jm45 : (TyEq G T101 T102 K79)) {struct jm45} :
(wfTy (domainEnv G) T102) :=
  match jm45 in (TyEq _ T101 T102 K79) return (wfTy (domainEnv G) T102) with
    | (Q_Arrow S1 S2 T1 T2 jm4 jm5) => (wfTy_tarr (domainEnv G) (TyEq_wf_1 G S1 T1 (star) jm4) (TyEq_wf_1 G S2 T2 (star) jm5))
    | (Q_Abs K1 K2 S2 T2 jm6 H24 H25) => (wfTy_tabs (domainEnv G) H24 (TyEq_wf_1 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm6))
    | (Q_App K1 K2 S1 S2 T1 T2 jm7 jm8) => (wfTy_tapp (domainEnv G) (TyEq_wf_1 G S1 T1 (karr K1 K2) jm7) (TyEq_wf_1 G S2 T2 K1 jm8))
    | (Q_AppAbs K11 K12 T12 T2 jm9 jm10 H35) => (substhvl_ty_wfTy (Kinding_wf_0 G T2 K11 jm10) (HS ty (domainEnv G)) T12 (Kinding_wf_0 (etvar G K11) T12 (weakenKind K12 (HS ty H0)) jm9) (substhvl_ty_here (domainEnv G)))
    | (Q_Refl K T jm11) => (Kinding_wf_0 G T K jm11)
    | (Q_Symm K S1 T jm12) => (TyEq_wf_0 G T S1 K jm12)
    | (Q_Trans K S1 T U jm13 jm14) => (TyEq_wf_1 G U T K jm14)
  end
with TyEq_wf_2 (G : Env) (T101 : Ty) (T102 : Ty) (K79 : Kind) (jm46 : (TyEq G T101 T102 K79)) {struct jm46} :
(wfKind (domainEnv G) K79) :=
  match jm46 in (TyEq _ T101 T102 K79) return (wfKind (domainEnv G) K79) with
    | (Q_Arrow S1 S2 T1 T2 jm4 jm5) => (wfKind_star (domainEnv G))
    | (Q_Abs K1 K2 S2 T2 jm6 H24 H25) => (wfKind_karr (domainEnv G) H24 H25)
    | (Q_App K1 K2 S1 S2 T1 T2 jm7 jm8) => (inversion_wfKind_karr_1 (domainEnv G) K1 K2 (TyEq_wf_2 G S1 T1 (karr K1 K2) jm7))
    | (Q_AppAbs K11 K12 T12 T2 jm9 jm10 H35) => H35
    | (Q_Refl K T jm11) => (Kinding_wf_1 G T K jm11)
    | (Q_Symm K S1 T jm12) => (TyEq_wf_2 G T S1 K jm12)
    | (Q_Trans K S1 T U jm13 jm14) => (TyEq_wf_2 G U T K jm14)
  end.
Fixpoint Typing_wf_0 (G : Env) (t12 : Tm) (T103 : Ty) (jm47 : (Typing G t12 T103)) {struct jm47} :
(wfTm (domainEnv G) t12) :=
  match jm47 in (Typing _ t12 T103) return (wfTm (domainEnv G) t12) with
    | (T_Var T y lk3 H19 H20) => (wfTm_var (domainEnv G) _ H20)
    | (T_Abs T1 T2 t jm15 jm16 H22) => (wfTm_abs (domainEnv G) (Kinding_wf_0 G T1 (star) jm15) (Typing_wf_0 (evar G T1) t (weakenTy T2 (HS tm H0)) jm16))
    | (T_App T11 T12 t1 t2 jm17 jm18) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tarr T11 T12) jm17) (Typing_wf_0 G t2 T11 jm18))
    | (T_Eq S1 T t jm19 jm20) => (Typing_wf_0 G t S1 jm19)
  end
with Typing_wf_1 (G : Env) (t12 : Tm) (T103 : Ty) (jm48 : (Typing G t12 T103)) {struct jm48} :
(wfTy (domainEnv G) T103) :=
  match jm48 in (Typing _ t12 T103) return (wfTy (domainEnv G) T103) with
    | (T_Var T y lk4 H19 H20) => H19
    | (T_Abs T1 T2 t jm15 jm16 H22) => (wfTy_tarr (domainEnv G) (Kinding_wf_0 G T1 (star) jm15) H22)
    | (T_App T11 T12 t1 t2 jm17 jm18) => (inversion_wfTy_tarr_1 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tarr T11 T12) jm17))
    | (T_Eq S1 T t jm19 jm20) => (TyEq_wf_1 G S1 T (star) jm20)
  end.
 Hint Extern 8 => match goal with
  | H68 : (TRed _ _ _ _) |- _ => pose proof ((TRed_wf_0 _ _ _ _ H68)); pose proof ((TRed_wf_1 _ _ _ _ H68)); pose proof ((TRed_wf_2 _ _ _ _ H68)); clear H68
end : wf.
 Hint Extern 8 => match goal with
  | H69 : (Kinding _ _ _) |- _ => pose proof ((Kinding_wf_0 _ _ _ H69)); pose proof ((Kinding_wf_1 _ _ _ H69)); clear H69
end : wf.
 Hint Extern 8 => match goal with
  | H70 : (TRedStar _ _ _ _) |- _ => pose proof ((TRedStar_wf_0 _ _ _ _ H70)); pose proof ((TRedStar_wf_1 _ _ _ _ H70)); pose proof ((TRedStar_wf_2 _ _ _ _ H70)); clear H70
end : wf.
 Hint Extern 8 => match goal with
  | H71 : (TyEq _ _ _ _) |- _ => pose proof ((TyEq_wf_0 _ _ _ _ H71)); pose proof ((TyEq_wf_1 _ _ _ _ H71)); pose proof ((TyEq_wf_2 _ _ _ _ H71)); clear H71
end : wf.
 Hint Extern 8 => match goal with
  | H72 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H72)); pose proof ((Typing_wf_1 _ _ _ H72)); clear H72
end : wf.
Lemma subst_evar_lookup_evar (G9 : Env) (s2 : Tm) (T104 : Ty) (jm49 : (Typing G9 s2 T104)) :
  (forall (d : (Trace tm)) (G10 : Env) (G12 : Env) (sub : (subst_evar G9 T104 s2 d G10 G12)) (x11 : (Index tm)) (T105 : Ty) ,
    (lookup_evar G10 x11 T105) -> (Typing G12 (substIndex d s2 x11) T105)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Lemma subst_etvar_lookup_etvar (G9 : Env) (S36 : Ty) (K80 : Kind) (jm49 : (Kinding G9 S36 K80)) :
  (forall (d : (Trace ty)) (G10 : Env) (G12 : Env) (sub : (subst_etvar G9 K80 S36 d G10 G12)) (X34 : (Index ty)) (K81 : Kind) ,
    (lookup_etvar G10 X34 K81) -> (Kinding G12 (tsubstIndex d S36 X34) K81)).
Proof.
  needleGenericSubstEnvLookupHom (K_TVar).
Qed.
Class Obligation_Env_reg_TRed : Prop := { Env_reg_QR_Var (G : Env) (K : Kind) (S36 : Ty) (jm49 : (Kinding G S36 K)) (H20 : (wfKind (domainEnv G) K)) (H73 : (wfTy (domainEnv G) S36)) : (TRed G (weakenTy S36 H0) (weakenTy S36 H0) K) }.
Context {obligation_Env_reg_TRed : Obligation_Env_reg_TRed} .
Fixpoint subst_evar_TRed (G10 : Env) (s2 : Tm) (T104 : Ty) (jm57 : (Typing G10 s2 T104)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm58 : (TRed G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H97 : (subst_evar G10 T104 s2 d G9 G11)) ,
  (TRed G11 T1 T2 K)) :=
  match jm58 in (TRed _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H97 : (subst_evar G10 T104 s2 d G9 G11)) ,
    (TRed G11 T1 T2 K)) with
    | (QR_Var K80 X34 lk5 H75 H76) => (fun (G11 : Env) (d : (Trace tm)) (H97 : (subst_evar G10 T104 s2 d G9 G11)) =>
      (QR_Var G11 K80 X34 (subst_evar_lookup_etvar T104 H97 K80 lk5) (substhvl_tm_wfKind _ _ H75 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H97))) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H97)) H76)))
    | (QR_Arrow S37 S38 T105 T106 jm50 jm51) => (fun (G11 : Env) (d : (Trace tm)) (H97 : (subst_evar G10 T104 s2 d G9 G11)) =>
      (QR_Arrow G11 S37 S38 T105 T106 (subst_evar_TRed G10 s2 T104 jm57 G9 S37 T105 (star) jm50 G11 d (weaken_subst_evar _ empty H97)) (subst_evar_TRed G10 s2 T104 jm57 G9 S38 T106 (star) jm51 G11 d (weaken_subst_evar _ empty H97))))
    | (QR_Abs K81 K82 S38 T106 jm52 H81 H82) => (fun (G11 : Env) (d : (Trace tm)) (H97 : (subst_evar G10 T104 s2 d G9 G11)) =>
      (QR_Abs G11 K81 K82 S38 T106 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TRed G10 s2 T104 jm57 (etvar G9 K81) S38 T106 (weakenKind K82 (HS ty H0)) jm52 (appendEnv G11 (etvar empty K81)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K81) H97))) (substhvl_tm_wfKind _ _ H81 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H97))) (substhvl_tm_wfKind _ _ H82 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H97)))))
    | (QR_App K81 K82 S37 S38 T105 T106 jm53 jm54) => (fun (G11 : Env) (d : (Trace tm)) (H97 : (subst_evar G10 T104 s2 d G9 G11)) =>
      (QR_App G11 K81 K82 S37 S38 T105 T106 (subst_evar_TRed G10 s2 T104 jm57 G9 S37 T105 (karr K82 K81) jm53 G11 d (weaken_subst_evar _ empty H97)) (subst_evar_TRed G10 s2 T104 jm57 G9 S38 T106 K82 jm54 G11 d (weaken_subst_evar _ empty H97))))
    | (QR_AppAbs K81 K82 S37 S38 T105 T106 jm55 jm56 H91) => (fun (G11 : Env) (d : (Trace tm)) (H97 : (subst_evar G10 T104 s2 d G9 G11)) =>
      (QR_AppAbs G11 K81 K82 S37 S38 T105 T106 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TRed G10 s2 T104 jm57 (etvar G9 K82) S37 T105 (weakenKind K81 (HS ty H0)) jm55 (appendEnv G11 (etvar empty K82)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K82) H97))) (subst_evar_TRed G10 s2 T104 jm57 G9 S38 T106 K82 jm56 G11 d (weaken_subst_evar _ empty H97)) (substhvl_tm_wfKind _ _ H91 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H97)))))
  end.
Fixpoint subst_etvar_TRed (G10 : Env) (S39 : Ty) (K80 : Kind) (jm57 : (Kinding G10 S39 K80)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm58 : (TRed G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H98 : (subst_etvar G10 K80 S39 d G9 G11)) ,
  (TRed G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) :=
  match jm58 in (TRed _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H98 : (subst_etvar G10 K80 S39 d G9 G11)) ,
    (TRed G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) with
    | (QR_Var K81 X34 lk5 H76 H77) => (fun (G11 : Env) (d : (Trace ty)) (H98 : (subst_etvar G10 K80 S39 d G9 G11)) =>
      (Env_reg_QR_Var G11 K81 _ (subst_etvar_lookup_etvar G10 S39 K80 jm57 d _ _ H98 X34 K81 lk5) (substhvl_ty_wfKind _ _ H76 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H98))) (substhvl_ty_wfindex_ty (Kinding_wf_0 G10 S39 K80 jm57) (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H98)) H77)))
    | (QR_Arrow S37 S38 T105 T106 jm50 jm51) => (fun (G11 : Env) (d : (Trace ty)) (H98 : (subst_etvar G10 K80 S39 d G9 G11)) =>
      (QR_Arrow G11 (tsubstTy (weakenTrace d H0) S39 S37) (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T105) (tsubstTy (weakenTrace d H0) S39 T106) (subst_etvar_TRed G10 S39 K80 jm57 G9 S37 T105 (star) jm50 G11 d (weaken_subst_etvar _ empty H98)) (subst_etvar_TRed G10 S39 K80 jm57 G9 S38 T106 (star) jm51 G11 d (weaken_subst_etvar _ empty H98))))
    | (QR_Abs K82 K83 S38 T106 jm52 H82 H83) => (fun (G11 : Env) (d : (Trace ty)) (H98 : (subst_etvar G10 K80 S39 d G9 G11)) =>
      (QR_Abs G11 K82 K83 (tsubstTy (weakenTrace d (HS ty H0)) S39 S38) (tsubstTy (weakenTrace d (HS ty H0)) S39 T106) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TRed G10 S39 K80 jm57 (etvar G9 K82) S38 T106 (weakenKind K83 (HS ty H0)) jm52 (appendEnv G11 (tsubstEnv d S39 (etvar empty K82))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K82) H98))) (substhvl_ty_wfKind _ _ H82 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H98))) (substhvl_ty_wfKind _ _ H83 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H98)))))
    | (QR_App K82 K83 S37 S38 T105 T106 jm53 jm54) => (fun (G11 : Env) (d : (Trace ty)) (H98 : (subst_etvar G10 K80 S39 d G9 G11)) =>
      (QR_App G11 K82 K83 (tsubstTy (weakenTrace d H0) S39 S37) (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T105) (tsubstTy (weakenTrace d H0) S39 T106) (subst_etvar_TRed G10 S39 K80 jm57 G9 S37 T105 (karr K83 K82) jm53 G11 d (weaken_subst_etvar _ empty H98)) (subst_etvar_TRed G10 S39 K80 jm57 G9 S38 T106 K83 jm54 G11 d (weaken_subst_etvar _ empty H98))))
    | (QR_AppAbs K82 K83 S37 S38 T105 T106 jm55 jm56 H92) => (fun (G11 : Env) (d : (Trace ty)) (H98 : (subst_etvar G10 K80 S39 d G9 G11)) =>
      (TRed_cast G11 _ _ _ G11 (tsubstTy d S39 (tapp (tabs K83 S37) S38)) (tsubstTy d S39 (tsubstTy X0 T106 T105)) K82 eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T105 d S39 T106)) eq_refl (QR_AppAbs G11 K82 K83 (tsubstTy (weakenTrace d (HS ty H0)) S39 S37) (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d (HS ty H0)) S39 T105) (tsubstTy (weakenTrace d H0) S39 T106) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TRed G10 S39 K80 jm57 (etvar G9 K83) S37 T105 (weakenKind K82 (HS ty H0)) jm55 (appendEnv G11 (tsubstEnv d S39 (etvar empty K83))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K83) H98))) (subst_etvar_TRed G10 S39 K80 jm57 G9 S38 T106 K83 jm56 G11 d (weaken_subst_etvar _ empty H98)) (substhvl_ty_wfKind _ _ H92 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H98))))))
  end.
Fixpoint subst_evar_Kinding (G10 : Env) (s2 : Tm) (T105 : Ty) (jm55 : (Typing G10 s2 T105)) (G9 : Env) (T : Ty) (K : Kind) (jm56 : (Kinding G9 T K)) :
(forall (G11 : Env) (d : (Trace tm)) (H88 : (subst_evar G10 T105 s2 d G9 G11)) ,
  (Kinding G11 T K)) :=
  match jm56 in (Kinding _ T K) return (forall (G11 : Env) (d : (Trace tm)) (H88 : (subst_evar G10 T105 s2 d G9 G11)) ,
    (Kinding G11 T K)) with
    | (K_TVar K81 X34 lk5 H77 H78) => (fun (G11 : Env) (d : (Trace tm)) (H88 : (subst_evar G10 T105 s2 d G9 G11)) =>
      (K_TVar G11 K81 X34 (subst_evar_lookup_etvar T105 H88 K81 lk5) (substhvl_tm_wfKind _ _ H77 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H88))) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H88)) H78)))
    | (K_Abs K82 K85 T107 jm50 H79 H80) => (fun (G11 : Env) (d : (Trace tm)) (H88 : (subst_evar G10 T105 s2 d G9 G11)) =>
      (K_Abs G11 K82 K85 T107 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Kinding G10 s2 T105 jm55 (etvar G9 K82) T107 (weakenKind K85 (HS ty H0)) jm50 (appendEnv G11 (etvar empty K82)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K82) H88))) (substhvl_tm_wfKind _ _ H79 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H88))) (substhvl_tm_wfKind _ _ H80 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H88)))))
    | (K_App K83 K84 T106 T107 jm51 jm52) => (fun (G11 : Env) (d : (Trace tm)) (H88 : (subst_evar G10 T105 s2 d G9 G11)) =>
      (K_App G11 K83 K84 T106 T107 (subst_evar_Kinding G10 s2 T105 jm55 G9 T106 (karr K83 K84) jm51 G11 d (weaken_subst_evar _ empty H88)) (subst_evar_Kinding G10 s2 T105 jm55 G9 T107 K83 jm52 G11 d (weaken_subst_evar _ empty H88))))
    | (K_Arr T106 T107 jm53 jm54) => (fun (G11 : Env) (d : (Trace tm)) (H88 : (subst_evar G10 T105 s2 d G9 G11)) =>
      (K_Arr G11 T106 T107 (subst_evar_Kinding G10 s2 T105 jm55 G9 T106 (star) jm53 G11 d (weaken_subst_evar _ empty H88)) (subst_evar_Kinding G10 s2 T105 jm55 G9 T107 (star) jm54 G11 d (weaken_subst_evar _ empty H88))))
  end.
Fixpoint subst_etvar_Kinding (G10 : Env) (S37 : Ty) (K81 : Kind) (jm55 : (Kinding G10 S37 K81)) (G9 : Env) (T : Ty) (K : Kind) (jm56 : (Kinding G9 T K)) :
(forall (G11 : Env) (d : (Trace ty)) (H89 : (subst_etvar G10 K81 S37 d G9 G11)) ,
  (Kinding G11 (tsubstTy d S37 T) K)) :=
  match jm56 in (Kinding _ T K) return (forall (G11 : Env) (d : (Trace ty)) (H89 : (subst_etvar G10 K81 S37 d G9 G11)) ,
    (Kinding G11 (tsubstTy d S37 T) K)) with
    | (K_TVar K82 X34 lk5 H78 H79) => (fun (G11 : Env) (d : (Trace ty)) (H89 : (subst_etvar G10 K81 S37 d G9 G11)) =>
      (subst_etvar_lookup_etvar G10 S37 K81 jm55 d G9 G11 H89 X34 K82 lk5))
    | (K_Abs K83 K86 T107 jm50 H80 H81) => (fun (G11 : Env) (d : (Trace ty)) (H89 : (subst_etvar G10 K81 S37 d G9 G11)) =>
      (K_Abs G11 K83 K86 (tsubstTy (weakenTrace d (HS ty H0)) S37 T107) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_Kinding G10 S37 K81 jm55 (etvar G9 K83) T107 (weakenKind K86 (HS ty H0)) jm50 (appendEnv G11 (tsubstEnv d S37 (etvar empty K83))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K83) H89))) (substhvl_ty_wfKind _ _ H80 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H89))) (substhvl_ty_wfKind _ _ H81 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H89)))))
    | (K_App K84 K85 T106 T107 jm51 jm52) => (fun (G11 : Env) (d : (Trace ty)) (H89 : (subst_etvar G10 K81 S37 d G9 G11)) =>
      (K_App G11 K84 K85 (tsubstTy (weakenTrace d H0) S37 T106) (tsubstTy (weakenTrace d H0) S37 T107) (subst_etvar_Kinding G10 S37 K81 jm55 G9 T106 (karr K84 K85) jm51 G11 d (weaken_subst_etvar _ empty H89)) (subst_etvar_Kinding G10 S37 K81 jm55 G9 T107 K84 jm52 G11 d (weaken_subst_etvar _ empty H89))))
    | (K_Arr T106 T107 jm53 jm54) => (fun (G11 : Env) (d : (Trace ty)) (H89 : (subst_etvar G10 K81 S37 d G9 G11)) =>
      (K_Arr G11 (tsubstTy (weakenTrace d H0) S37 T106) (tsubstTy (weakenTrace d H0) S37 T107) (subst_etvar_Kinding G10 S37 K81 jm55 G9 T106 (star) jm53 G11 d (weaken_subst_etvar _ empty H89)) (subst_etvar_Kinding G10 S37 K81 jm55 G9 T107 (star) jm54 G11 d (weaken_subst_etvar _ empty H89))))
  end.
Fixpoint subst_evar_TRedStar (G10 : Env) (s2 : Tm) (T106 : Ty) (jm53 : (Typing G10 s2 T106)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm54 : (TRedStar G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H85 : (subst_evar G10 T106 s2 d G9 G11)) ,
  (TRedStar G11 T1 T2 K)) :=
  match jm54 in (TRedStar _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H85 : (subst_evar G10 T106 s2 d G9 G11)) ,
    (TRedStar G11 T1 T2 K)) with
    | (QRS_Nil K82 T107 jm50) => (fun (G11 : Env) (d : (Trace tm)) (H85 : (subst_evar G10 T106 s2 d G9 G11)) =>
      (QRS_Nil G11 K82 T107 (subst_evar_Kinding G10 s2 T106 jm53 G9 T107 K82 jm50 G11 d (weaken_subst_evar _ empty H85))))
    | (QRS_Cons K82 S37 T107 U3 jm51 jm52) => (fun (G11 : Env) (d : (Trace tm)) (H85 : (subst_evar G10 T106 s2 d G9 G11)) =>
      (QRS_Cons G11 K82 S37 T107 U3 (subst_evar_TRedStar G10 s2 T106 jm53 G9 S37 T107 K82 jm51 G11 d (weaken_subst_evar _ empty H85)) (subst_evar_TRed G10 s2 T106 jm53 G9 T107 U3 K82 jm52 G11 d (weaken_subst_evar _ empty H85))))
  end.
Fixpoint subst_etvar_TRedStar (G10 : Env) (S38 : Ty) (K82 : Kind) (jm53 : (Kinding G10 S38 K82)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm54 : (TRedStar G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H86 : (subst_etvar G10 K82 S38 d G9 G11)) ,
  (TRedStar G11 (tsubstTy d S38 T1) (tsubstTy d S38 T2) K)) :=
  match jm54 in (TRedStar _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H86 : (subst_etvar G10 K82 S38 d G9 G11)) ,
    (TRedStar G11 (tsubstTy d S38 T1) (tsubstTy d S38 T2) K)) with
    | (QRS_Nil K83 T107 jm50) => (fun (G11 : Env) (d : (Trace ty)) (H86 : (subst_etvar G10 K82 S38 d G9 G11)) =>
      (QRS_Nil G11 K83 (tsubstTy (weakenTrace d H0) S38 T107) (subst_etvar_Kinding G10 S38 K82 jm53 G9 T107 K83 jm50 G11 d (weaken_subst_etvar _ empty H86))))
    | (QRS_Cons K83 S37 T107 U3 jm51 jm52) => (fun (G11 : Env) (d : (Trace ty)) (H86 : (subst_etvar G10 K82 S38 d G9 G11)) =>
      (QRS_Cons G11 K83 (tsubstTy (weakenTrace d H0) S38 S37) (tsubstTy (weakenTrace d H0) S38 T107) (tsubstTy (weakenTrace d H0) S38 U3) (subst_etvar_TRedStar G10 S38 K82 jm53 G9 S37 T107 K83 jm51 G11 d (weaken_subst_etvar _ empty H86)) (subst_etvar_TRed G10 S38 K82 jm53 G9 T107 U3 K83 jm52 G11 d (weaken_subst_etvar _ empty H86))))
  end.
Fixpoint subst_evar_TyEq (G10 : Env) (s2 : Tm) (T107 : Ty) (jm61 : (Typing G10 s2 T107)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm62 : (TyEq G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) ,
  (TyEq G11 T1 T2 K)) :=
  match jm62 in (TyEq _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) ,
    (TyEq G11 T1 T2 K)) with
    | (Q_Arrow S37 S38 T109 T111 jm55 jm56) => (fun (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) =>
      (Q_Arrow G11 S37 S38 T109 T111 (subst_evar_TyEq G10 s2 T107 jm61 G9 S37 T109 (star) jm55 G11 d (weaken_subst_evar _ empty H108)) (subst_evar_TyEq G10 s2 T107 jm61 G9 S38 T111 (star) jm56 G11 d (weaken_subst_evar _ empty H108))))
    | (Q_Abs K84 K87 S38 T111 jm57 H85 H86) => (fun (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) =>
      (Q_Abs G11 K84 K87 S38 T111 (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TyEq G10 s2 T107 jm61 (etvar G9 K84) S38 T111 (weakenKind K87 (HS ty H0)) jm57 (appendEnv G11 (etvar empty K84)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K84) H108))) (substhvl_tm_wfKind _ _ H85 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H108))) (substhvl_tm_wfKind _ _ H86 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H108)))))
    | (Q_App K84 K87 S37 S38 T109 T111 jm58 jm59) => (fun (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) =>
      (Q_App G11 K84 K87 S37 S38 T109 T111 (subst_evar_TyEq G10 s2 T107 jm61 G9 S37 T109 (karr K84 K87) jm58 G11 d (weaken_subst_evar _ empty H108)) (subst_evar_TyEq G10 s2 T107 jm61 G9 S38 T111 K84 jm59 G11 d (weaken_subst_evar _ empty H108))))
    | (Q_AppAbs K85 K86 T110 T111 jm60 jm50 H96) => (fun (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) =>
      (Q_AppAbs G11 K85 K86 T110 T111 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Kinding G10 s2 T107 jm61 (etvar G9 K85) T110 (weakenKind K86 (HS ty H0)) jm60 (appendEnv G11 (etvar empty K85)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K85) H108))) (subst_evar_Kinding G10 s2 T107 jm61 G9 T111 K85 jm50 G11 d (weaken_subst_evar _ empty H108)) (substhvl_tm_wfKind _ _ H96 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H108)))))
    | (Q_Refl K83 T108 jm51) => (fun (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) =>
      (Q_Refl G11 K83 T108 (subst_evar_Kinding G10 s2 T107 jm61 G9 T108 K83 jm51 G11 d (weaken_subst_evar _ empty H108))))
    | (Q_Symm K83 S37 T108 jm52) => (fun (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) =>
      (Q_Symm G11 K83 S37 T108 (subst_evar_TyEq G10 s2 T107 jm61 G9 T108 S37 K83 jm52 G11 d (weaken_subst_evar _ empty H108))))
    | (Q_Trans K83 S37 T108 U3 jm53 jm54) => (fun (G11 : Env) (d : (Trace tm)) (H108 : (subst_evar G10 T107 s2 d G9 G11)) =>
      (Q_Trans G11 K83 S37 T108 U3 (subst_evar_TyEq G10 s2 T107 jm61 G9 S37 U3 K83 jm53 G11 d (weaken_subst_evar _ empty H108)) (subst_evar_TyEq G10 s2 T107 jm61 G9 U3 T108 K83 jm54 G11 d (weaken_subst_evar _ empty H108))))
  end.
Fixpoint subst_etvar_TyEq (G10 : Env) (S39 : Ty) (K83 : Kind) (jm61 : (Kinding G10 S39 K83)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm62 : (TyEq G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) ,
  (TyEq G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) :=
  match jm62 in (TyEq _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) ,
    (TyEq G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) with
    | (Q_Arrow S37 S38 T109 T111 jm55 jm56) => (fun (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) =>
      (Q_Arrow G11 (tsubstTy (weakenTrace d H0) S39 S37) (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T109) (tsubstTy (weakenTrace d H0) S39 T111) (subst_etvar_TyEq G10 S39 K83 jm61 G9 S37 T109 (star) jm55 G11 d (weaken_subst_etvar _ empty H109)) (subst_etvar_TyEq G10 S39 K83 jm61 G9 S38 T111 (star) jm56 G11 d (weaken_subst_etvar _ empty H109))))
    | (Q_Abs K85 K88 S38 T111 jm57 H86 H87) => (fun (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) =>
      (Q_Abs G11 K85 K88 (tsubstTy (weakenTrace d (HS ty H0)) S39 S38) (tsubstTy (weakenTrace d (HS ty H0)) S39 T111) (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TyEq G10 S39 K83 jm61 (etvar G9 K85) S38 T111 (weakenKind K88 (HS ty H0)) jm57 (appendEnv G11 (tsubstEnv d S39 (etvar empty K85))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K85) H109))) (substhvl_ty_wfKind _ _ H86 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H109))) (substhvl_ty_wfKind _ _ H87 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H109)))))
    | (Q_App K85 K88 S37 S38 T109 T111 jm58 jm59) => (fun (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) =>
      (Q_App G11 K85 K88 (tsubstTy (weakenTrace d H0) S39 S37) (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T109) (tsubstTy (weakenTrace d H0) S39 T111) (subst_etvar_TyEq G10 S39 K83 jm61 G9 S37 T109 (karr K85 K88) jm58 G11 d (weaken_subst_etvar _ empty H109)) (subst_etvar_TyEq G10 S39 K83 jm61 G9 S38 T111 K85 jm59 G11 d (weaken_subst_etvar _ empty H109))))
    | (Q_AppAbs K86 K87 T110 T111 jm60 jm50 H97) => (fun (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) =>
      (TyEq_cast G11 _ _ _ G11 (tsubstTy d S39 (tapp (tabs K86 T110) T111)) (tsubstTy d S39 (tsubstTy X0 T111 T110)) K87 eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T110 d S39 T111)) eq_refl (Q_AppAbs G11 K86 K87 (tsubstTy (weakenTrace d (HS ty H0)) S39 T110) (tsubstTy (weakenTrace d H0) S39 T111) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_Kinding G10 S39 K83 jm61 (etvar G9 K86) T110 (weakenKind K87 (HS ty H0)) jm60 (appendEnv G11 (tsubstEnv d S39 (etvar empty K86))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K86) H109))) (subst_etvar_Kinding G10 S39 K83 jm61 G9 T111 K86 jm50 G11 d (weaken_subst_etvar _ empty H109)) (substhvl_ty_wfKind _ _ H97 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H109))))))
    | (Q_Refl K84 T108 jm51) => (fun (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) =>
      (Q_Refl G11 K84 (tsubstTy (weakenTrace d H0) S39 T108) (subst_etvar_Kinding G10 S39 K83 jm61 G9 T108 K84 jm51 G11 d (weaken_subst_etvar _ empty H109))))
    | (Q_Symm K84 S37 T108 jm52) => (fun (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) =>
      (Q_Symm G11 K84 (tsubstTy (weakenTrace d H0) S39 S37) (tsubstTy (weakenTrace d H0) S39 T108) (subst_etvar_TyEq G10 S39 K83 jm61 G9 T108 S37 K84 jm52 G11 d (weaken_subst_etvar _ empty H109))))
    | (Q_Trans K84 S37 T108 U3 jm53 jm54) => (fun (G11 : Env) (d : (Trace ty)) (H109 : (subst_etvar G10 K83 S39 d G9 G11)) =>
      (Q_Trans G11 K84 (tsubstTy (weakenTrace d H0) S39 S37) (tsubstTy (weakenTrace d H0) S39 T108) (tsubstTy (weakenTrace d H0) S39 U3) (subst_etvar_TyEq G10 S39 K83 jm61 G9 S37 U3 K84 jm53 G11 d (weaken_subst_etvar _ empty H109)) (subst_etvar_TyEq G10 S39 K83 jm61 G9 U3 T108 K84 jm54 G11 d (weaken_subst_etvar _ empty H109))))
  end.
Fixpoint subst_evar_Typing (G10 : Env) (s2 : Tm) (T108 : Ty) (jm56 : (Typing G10 s2 T108)) (G9 : Env) (t : Tm) (T : Ty) (jm57 : (Typing G9 t T)) :
(forall (G11 : Env) (d : (Trace tm)) (H95 : (subst_evar G10 T108 s2 d G9 G11)) ,
  (Typing G11 (substTm d s2 t) T)) :=
  match jm57 in (Typing _ t T) return (forall (G11 : Env) (d : (Trace tm)) (H95 : (subst_evar G10 T108 s2 d G9 G11)) ,
    (Typing G11 (substTm d s2 t) T)) with
    | (T_Var T109 y1 lk5 H83 H84) => (fun (G11 : Env) (d : (Trace tm)) (H95 : (subst_evar G10 T108 s2 d G9 G11)) =>
      (subst_evar_lookup_evar G10 s2 T108 jm56 d G9 G11 H95 y1 T109 lk5))
    | (T_Abs T110 T113 t13 jm50 jm51 H86) => (fun (G11 : Env) (d : (Trace tm)) (H95 : (subst_evar G10 T108 s2 d G9 G11)) =>
      (T_Abs G11 T110 T113 (substTm (weakenTrace d (HS tm H0)) s2 t13) (subst_evar_Kinding G10 s2 T108 jm56 G9 T110 (star) jm50 G11 d (weaken_subst_evar _ empty H95)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G10 s2 T108 jm56 (evar G9 T110) t13 (weakenTy T113 (HS tm H0)) jm51 (appendEnv G11 (evar empty T110)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T110) H95))) (substhvl_tm_wfTy _ _ H86 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H95)))))
    | (T_App T111 T112 t14 t15 jm52 jm53) => (fun (G11 : Env) (d : (Trace tm)) (H95 : (subst_evar G10 T108 s2 d G9 G11)) =>
      (T_App G11 T111 T112 (substTm (weakenTrace d H0) s2 t14) (substTm (weakenTrace d H0) s2 t15) (subst_evar_Typing G10 s2 T108 jm56 G9 t14 (tarr T111 T112) jm52 G11 d (weaken_subst_evar _ empty H95)) (subst_evar_Typing G10 s2 T108 jm56 G9 t15 T111 jm53 G11 d (weaken_subst_evar _ empty H95))))
    | (T_Eq S37 T109 t13 jm54 jm55) => (fun (G11 : Env) (d : (Trace tm)) (H95 : (subst_evar G10 T108 s2 d G9 G11)) =>
      (T_Eq G11 S37 T109 (substTm (weakenTrace d H0) s2 t13) (subst_evar_Typing G10 s2 T108 jm56 G9 t13 S37 jm54 G11 d (weaken_subst_evar _ empty H95)) (subst_evar_TyEq G10 s2 T108 jm56 G9 S37 T109 (star) jm55 G11 d (weaken_subst_evar _ empty H95))))
  end.
Fixpoint subst_etvar_Typing (G10 : Env) (S38 : Ty) (K84 : Kind) (jm56 : (Kinding G10 S38 K84)) (G9 : Env) (t : Tm) (T : Ty) (jm57 : (Typing G9 t T)) :
(forall (G11 : Env) (d : (Trace ty)) (H96 : (subst_etvar G10 K84 S38 d G9 G11)) ,
  (Typing G11 (tsubstTm d S38 t) (tsubstTy d S38 T))) :=
  match jm57 in (Typing _ t T) return (forall (G11 : Env) (d : (Trace ty)) (H96 : (subst_etvar G10 K84 S38 d G9 G11)) ,
    (Typing G11 (tsubstTm d S38 t) (tsubstTy d S38 T))) with
    | (T_Var T109 y1 lk5 H84 H85) => (fun (G11 : Env) (d : (Trace ty)) (H96 : (subst_etvar G10 K84 S38 d G9 G11)) =>
      (T_Var G11 (tsubstTy (weakenTrace d H0) S38 T109) y1 (subst_etvar_lookup_evar K84 (Kinding_wf_0 G10 S38 K84 jm56) H96 T109 lk5) (substhvl_ty_wfTy (Kinding_wf_0 G10 S38 K84 jm56) _ _ H84 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H96))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H96)) H85)))
    | (T_Abs T110 T113 t13 jm50 jm51 H87) => (fun (G11 : Env) (d : (Trace ty)) (H96 : (subst_etvar G10 K84 S38 d G9 G11)) =>
      (T_Abs G11 (tsubstTy (weakenTrace d H0) S38 T110) (tsubstTy (weakenTrace d H0) S38 T113) (tsubstTm (weakenTrace d (HS tm H0)) S38 t13) (subst_etvar_Kinding G10 S38 K84 jm56 G9 T110 (star) jm50 G11 d (weaken_subst_etvar _ empty H96)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d S38 T113)) (subst_etvar_Typing G10 S38 K84 jm56 (evar G9 T110) t13 (weakenTy T113 (HS tm H0)) jm51 (appendEnv G11 (tsubstEnv d S38 (evar empty T110))) (weakenTrace d (HS tm H0)) (weaken_subst_etvar _ (evar empty T110) H96))) (substhvl_ty_wfTy (Kinding_wf_0 G10 S38 K84 jm56) _ _ H87 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H96)))))
    | (T_App T111 T112 t14 t15 jm52 jm53) => (fun (G11 : Env) (d : (Trace ty)) (H96 : (subst_etvar G10 K84 S38 d G9 G11)) =>
      (T_App G11 (tsubstTy (weakenTrace d H0) S38 T111) (tsubstTy (weakenTrace d H0) S38 T112) (tsubstTm (weakenTrace d H0) S38 t14) (tsubstTm (weakenTrace d H0) S38 t15) (subst_etvar_Typing G10 S38 K84 jm56 G9 t14 (tarr T111 T112) jm52 G11 d (weaken_subst_etvar _ empty H96)) (subst_etvar_Typing G10 S38 K84 jm56 G9 t15 T111 jm53 G11 d (weaken_subst_etvar _ empty H96))))
    | (T_Eq S37 T109 t13 jm54 jm55) => (fun (G11 : Env) (d : (Trace ty)) (H96 : (subst_etvar G10 K84 S38 d G9 G11)) =>
      (T_Eq G11 (tsubstTy (weakenTrace d H0) S38 S37) (tsubstTy (weakenTrace d H0) S38 T109) (tsubstTm (weakenTrace d H0) S38 t13) (subst_etvar_Typing G10 S38 K84 jm56 G9 t13 S37 jm54 G11 d (weaken_subst_etvar _ empty H96)) (subst_etvar_TyEq G10 S38 K84 jm56 G9 S37 T109 (star) jm55 G11 d (weaken_subst_etvar _ empty H96))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenKind_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.