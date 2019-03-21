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
  Fixpoint weakenIndexty (X46 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X46
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X46 k))
        | _ => (weakenIndexty X46 k)
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x6 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x6 k) k0) = (weakenIndextm x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexty_append  :
    (forall (X46 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X46 k) k0) = (weakenIndexty X46 (appendHvl k k0)))).
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
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (K : Kind) (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tyabs (K : Kind) (t : Tm)
    | tyapp (t : Tm) (T : Ty).
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
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X46 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X46)
      | (CS c) => match X46 with
        | (I0) => I0
        | (IS X46) => (IS (tshiftIndex c X46))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S32 : Ty) {struct S32} :
  Ty :=
    match S32 with
      | (tvar X46) => (tvar (tshiftIndex c X46))
      | (tabs K77 T95) => (tabs K77 (tshiftTy (CS c) T95))
      | (tapp T96 T97) => (tapp (tshiftTy c T96) (tshiftTy c T97))
      | (tarr T98 T99) => (tarr (tshiftTy c T98) (tshiftTy c T99))
      | (tall K78 T100) => (tall K78 (tshiftTy (CS c) T100))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var (shiftIndex c x6))
      | (abs T95 t17) => (abs T95 (shiftTm (CS c) t17))
      | (app t18 t19) => (app (shiftTm c t18) (shiftTm c t19))
      | (tyabs K77 t20) => (tyabs K77 (shiftTm c t20))
      | (tyapp t21 T96) => (tyapp (shiftTm c t21) T96)
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T95 t17) => (abs (tshiftTy c T95) (tshiftTm c t17))
      | (app t18 t19) => (app (tshiftTm c t18) (tshiftTm c t19))
      | (tyabs K77 t20) => (tyabs K77 (tshiftTm (CS c) t20))
      | (tyapp t21 T96) => (tyapp (tshiftTm c t21) (tshiftTy c T96))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenKind (K77 : Kind) (k : Hvl) {struct k} :
  Kind :=
    match k with
      | (H0) => K77
      | (HS tm k) => (weakenKind K77 k)
      | (HS ty k) => (weakenKind K77 k)
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
        (T95 : (Trace a)).
  
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
  Fixpoint tsubstIndex (d : (Trace ty)) (S32 : Ty) (X46 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X46 with
        | (I0) => S32
        | (IS X46) => (tvar X46)
      end
      | (XS tm d) => (tsubstIndex d S32 X46)
      | (XS ty d) => match X46 with
        | (I0) => (tvar I0)
        | (IS X46) => (tshiftTy C0 (tsubstIndex d S32 X46))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct S33} :
  Ty :=
    match S33 with
      | (tvar X46) => (tsubstIndex d S32 X46)
      | (tabs K77 T95) => (tabs K77 (tsubstTy (weakenTrace d (HS ty H0)) S32 T95))
      | (tapp T96 T97) => (tapp (tsubstTy d S32 T96) (tsubstTy d S32 T97))
      | (tarr T98 T99) => (tarr (tsubstTy d S32 T98) (tsubstTy d S32 T99))
      | (tall K78 T100) => (tall K78 (tsubstTy (weakenTrace d (HS ty H0)) S32 T100))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x6) => (substIndex d s x6)
      | (abs T95 t17) => (abs T95 (substTm (weakenTrace d (HS tm H0)) s t17))
      | (app t18 t19) => (app (substTm d s t18) (substTm d s t19))
      | (tyabs K77 t20) => (tyabs K77 (substTm (weakenTrace d (HS ty H0)) s t20))
      | (tyapp t21 T96) => (tyapp (substTm d s t21) T96)
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S32 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T95 t17) => (abs (tsubstTy d S32 T95) (tsubstTm (weakenTrace d (HS tm H0)) S32 t17))
      | (app t18 t19) => (app (tsubstTm d S32 t18) (tsubstTm d S32 t19))
      | (tyabs K77 t20) => (tyabs K77 (tsubstTm (weakenTrace d (HS ty H0)) S32 t20))
      | (tyapp t21 T96) => (tyapp (tsubstTm d S32 t21) (tsubstTy d S32 T96))
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
    (forall (k : Hvl) (X46 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S32 (tshiftIndex (weakenCutoffty C0 k) X46)) = (tvar X46))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S33 : Ty) (k : Hvl) (S32 : Ty) {struct S33} :
  ((tsubstTy (weakenTrace X0 k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = S33) :=
    match S33 return ((tsubstTy (weakenTrace X0 k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = S33) with
      | (tvar X46) => (tsubstIndex0_tshiftIndex0_reflection_ind S32 k X46)
      | (tabs K77 T95) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T95 (HS ty k) S32)))
      | (tapp T96 T97) => (f_equal2 tapp (tsubst0_tshift0_Ty_reflection_ind T96 k S32) (tsubst0_tshift0_Ty_reflection_ind T97 k S32))
      | (tarr T96 T97) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T96 k S32) (tsubst0_tshift0_Ty_reflection_ind T97 k S32))
      | (tall K77 T95) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T95 (HS ty k) S32)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x6) => (substIndex0_shiftIndex0_reflection_ind s k x6)
      | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t17 (HS tm k) s)))
      | (app t18 t19) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t18 k s) (subst0_shift0_Tm_reflection_ind t19 k s))
      | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t17 (HS ty k) s)))
      | (tyapp t17 T95) => (f_equal2 tyapp (subst0_shift0_Tm_reflection_ind t17 k s) eq_refl)
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S32 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x6) => eq_refl
      | (abs T95 t17) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T95 k S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t17 (HS tm k) S32)))
      | (app t18 t19) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t18 k S32) (tsubst0_tshift0_Tm_reflection_ind t19 k S32))
      | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t17 (HS ty k) S32)))
      | (tyapp t17 T95) => (f_equal2 tyapp (tsubst0_tshift0_Tm_reflection_ind t17 k S32) (tsubst0_tshift0_Ty_reflection_ind T95 k S32))
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
      (forall (k : Hvl) (c : (Cutoff ty)) (X46 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c) k) (tshiftIndex (weakenCutoffty C0 k) X46)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c k) X46)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S32 : Ty) (k : Hvl) (c : (Cutoff ty)) {struct S32} :
    ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S32)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S32))) :=
      match S32 return ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S32)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S32))) with
        | (tvar X46) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c X46))
        | (tabs K77 T95) => (f_equal2 tabs eq_refl (tshift_tshift0_Ty_comm_ind T95 (HS ty k) c))
        | (tapp T96 T97) => (f_equal2 tapp (tshift_tshift0_Ty_comm_ind T96 k c) (tshift_tshift0_Ty_comm_ind T97 k c))
        | (tarr T96 T97) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T96 k c) (tshift_tshift0_Ty_comm_ind T97 k c))
        | (tall K77 T95) => (f_equal2 tall eq_refl (tshift_tshift0_Ty_comm_ind T95 (HS ty k) c))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x6))
        | (abs T95 t17) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (shift_shift0_Tm_comm_ind t18 k c) (shift_shift0_Tm_comm_ind t19 k c))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (shift_shift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T95) => (f_equal2 tyapp (shift_shift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (shift_tshift0_Tm_comm_ind t18 k c) (shift_tshift0_Tm_comm_ind t19 k c))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (shift_tshift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T95) => (f_equal2 tyapp (shift_tshift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (tshift_shift0_Tm_comm_ind t18 k c) (tshift_shift0_Tm_comm_ind t19 k c))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (tshift_shift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T95) => (f_equal2 tyapp (tshift_shift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T95 k c) (tshift_tshift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t18 k c) (tshift_tshift0_Tm_comm_ind t19 k c))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (tshift_tshift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T95) => (f_equal2 tyapp (tshift_tshift0_Tm_comm_ind t17 k c) (tshift_tshift0_Ty_comm_ind T95 k c))
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
      (forall (k : Hvl) (X46 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c k) (tsubstIndex (weakenTrace X0 k) S32 X46)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c S32) (tshiftIndex (weakenCutoffty (CS c) k) X46)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S33 : Ty) (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) {struct S33} :
    ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S32 S33)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S32) (tshiftTy (weakenCutoffty (CS c) k) S33))) :=
      match S33 return ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S32 S33)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S32) (tshiftTy (weakenCutoffty (CS c) k) S33))) with
        | (tvar X46) => (tshiftTy_tsubstIndex0_comm_ind c S32 k X46)
        | (tabs K77 T95) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T95 (HS ty k) c S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp T96 T97) => (f_equal2 tapp (tshift_tsubst0_Ty_comm_ind T96 k c S32) (tshift_tsubst0_Ty_comm_ind T97 k c S32))
        | (tarr T96 T97) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T96 k c S32) (tshift_tsubst0_Ty_comm_ind T97 k c S32))
        | (tall K77 T95) => (f_equal2 tall eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T95 (HS ty k) c S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x6) => (shiftTm_substIndex0_comm_ind c s k x6)
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t17 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (shift_subst0_Tm_comm_ind t18 k c s) (shift_subst0_Tm_comm_ind t19 k c s))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t17 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T95) => (f_equal2 tyapp (shift_subst0_Tm_comm_ind t17 k c s) eq_refl)
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) (S32 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) S32 (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) S32 (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t17 (HS tm k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t18 k c S32) (shift_tsubst0_Tm_comm_ind t19 k c S32))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t17 (HS ty k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T95) => (f_equal2 tyapp (shift_tsubst0_Tm_comm_ind t17 k c S32) eq_refl)
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) with
        | (var x6) => (tshiftTm_substIndex0_comm_ind c s k x6)
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t17 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tshift_subst0_Tm_comm_ind t18 k c s) (tshift_subst0_Tm_comm_ind t19 k c s))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t17 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T95) => (f_equal2 tyapp (tshift_subst0_Tm_comm_ind t17 k c s) eq_refl)
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S32) (tshiftTm (weakenCutoffty (CS c) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S32) (tshiftTm (weakenCutoffty (CS c) k) s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T95 k c S32) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t17 (HS tm k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t18 k c S32) (tshift_tsubst0_Tm_comm_ind t19 k c S32))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t17 (HS ty k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T95) => (f_equal2 tyapp (tshift_tsubst0_Tm_comm_ind t17 k c S32) (tshift_tsubst0_Ty_comm_ind T95 k c S32))
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
      (forall (k : Hvl) (X46 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k) S32 X46) = (tsubstIndex (weakenTrace d k) S32 X46))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S32 : Ty) :
      (forall (k : Hvl) (X46 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k) S32 (tshiftIndex (weakenCutoffty C0 k) X46)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d k) S32 X46)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S33 : Ty) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct S33} :
    ((tsubstTy (weakenTrace (XS ty d) k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S32 S33))) :=
      match S33 return ((tsubstTy (weakenTrace (XS ty d) k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S32 S33))) with
        | (tvar X46) => (tsubstIndex_tshiftTy0_comm_ind d S32 k X46)
        | (tabs K77 T95) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T95 (HS ty k) d S32) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp T96 T97) => (f_equal2 tapp (tsubst_tshift0_Ty_comm_ind T96 k d S32) (tsubst_tshift0_Ty_comm_ind T97 k d S32))
        | (tarr T96 T97) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T96 k d S32) (tsubst_tshift0_Ty_comm_ind T97 k d S32))
        | (tall K77 T95) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T95 (HS ty k) d S32) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_shiftTm0_comm_ind d s k x6)
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t17 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_shift0_Tm_comm_ind t18 k d s) (subst_shift0_Tm_comm_ind t19 k d s))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t17 (HS ty k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (subst_shift0_Tm_comm_ind t17 k d s) eq_refl)
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_tshiftTm0_comm_ind d s k x6)
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t17 (HS tm k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_tshift0_Tm_comm_ind t18 k d s) (subst_tshift0_Tm_comm_ind t19 k d s))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t17 (HS ty k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (subst_tshift0_Tm_comm_ind t17 k d s) eq_refl)
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S32 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S32 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t17 (HS tm k) d S32) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t18 k d S32) (tsubst_shift0_Tm_comm_ind t19 k d S32))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t17 (HS ty k) d S32) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (tsubst_shift0_Tm_comm_ind t17 k d S32) eq_refl)
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d) k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d) k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T95 k d S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t17 (HS tm k) d S32) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t18 k d S32) (tsubst_tshift0_Tm_comm_ind t19 k d S32))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t17 (HS ty k) d S32) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (tsubst_tshift0_Tm_comm_ind t17 k d S32) (tsubst_tshift0_Ty_comm_ind T95 k d S32))
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
        | (tvar X46) => (tsubstIndex_shiftTy0_comm_ind d S32 k X46)
        | (tabs K77 T95) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T95 (HS ty k) d S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tapp T96 T97) => (f_equal2 tapp (tsubst_tm_Ty_ind T96 k d S32) (tsubst_tm_Ty_ind T97 k d S32))
        | (tarr T96 T97) => (f_equal2 tarr (tsubst_tm_Ty_ind T96 k d S32) (tsubst_tm_Ty_ind T97 k d S32))
        | (tall K77 T95) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T95 (HS ty k) d S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d) k) S32 s) = (tsubstTm (weakenTrace d k) S32 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d) k) S32 s) = (tsubstTm (weakenTrace d k) S32 s)) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs (tsubst_tm_Ty_ind T95 k d S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t17 (HS tm k) d S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tsubst_tm_Tm_ind t18 k d S32) (tsubst_tm_Tm_ind t19 k d S32))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t17 (HS ty k) d S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T95) => (f_equal2 tyapp (tsubst_tm_Tm_ind t17 k d S32) (tsubst_tm_Ty_ind T95 k d S32))
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
      (forall (k : Hvl) (X46 : (Index ty)) ,
        ((tsubstTy (weakenTrace d k) S32 (tsubstIndex (weakenTrace X0 k) S33 X46)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstIndex (weakenTrace (XS ty d) k) S32 X46)))).
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
        | (tvar X46) => (tsubstTy_tsubstIndex0_commright_ind d S32 S33 k X46)
        | (tabs K77 T95) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T95 (HS ty k) d S32 S33) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp T96 T97) => (f_equal2 tapp (tsubst_tsubst0_Ty_comm_ind T96 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T97 k d S32 S33))
        | (tarr T96 T97) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T96 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T97 k d S32 S33))
        | (tall K77 T95) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T95 (HS ty k) d S32 S33) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x6) => (substTm_substIndex0_commright_ind d s s0 k x6)
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t17 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_subst0_Tm_comm_ind t18 k d s s0) (subst_subst0_Tm_comm_ind t19 k d s s0))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t17 (HS ty k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (subst_subst0_Tm_comm_ind t17 k d s s0) eq_refl)
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (S32 : Ty) {struct s0} :
    ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S32 s0)) = (tsubstTm (weakenTrace X0 k) S32 (substTm (weakenTrace (XS ty d) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S32 s0)) = (tsubstTm (weakenTrace X0 k) S32 (substTm (weakenTrace (XS ty d) k) s s0))) with
        | (var x6) => (substTy_tsubstIndex0_commleft_ind d s S32 k x6)
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t17 (HS tm k) d s S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t18 k d s S32) (subst_tsubst0_Tm_comm_ind t19 k d s S32))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t17 (HS ty k) d s S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (subst_tsubst0_Tm_comm_ind t17 k d s S32) eq_refl)
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d k) S32 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S32 s) (tsubstTm (weakenTrace d k) S32 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d k) S32 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S32 s) (tsubstTm (weakenTrace d k) S32 s0))) with
        | (var x6) => (tsubstTm_substIndex0_commright_ind d S32 s k x6)
        | (abs T95 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t17 (HS tm k) d S32 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t18 k d S32 s) (tsubst_subst0_Tm_comm_ind t19 k d S32 s))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t17 (HS ty k) d S32 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (tsubst_subst0_Tm_comm_ind t17 k d S32 s) eq_refl)
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S32 (tsubstTm (weakenTrace X0 k) S33 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTm (weakenTrace (XS ty d) k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S32 (tsubstTm (weakenTrace X0 k) S33 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTm (weakenTrace (XS ty d) k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T95 t17) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T95 k d S32 S33) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t17 (HS tm k) d S32 S33) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t18 k d S32 S33) (tsubst_tsubst0_Tm_comm_ind t19 k d S32 S33))
        | (tyabs K77 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t17 (HS ty k) d S32 S33) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T95) => (f_equal2 tyapp (tsubst_tsubst0_Tm_comm_ind t17 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T95 k d S32 S33))
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
    | wfKind_karr {K77 : Kind}
        (wf : (wfKind k K77))
        {K78 : Kind}
        (wf0 : (wfKind k K78)) :
        (wfKind k (karr K77 K78)).
  Inductive wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tvar (X46 : (Index ty))
        (wfi : (wfindex k X46)) :
        (wfTy k (tvar X46))
    | wfTy_tabs {K77 : Kind}
        (wf : (wfKind k K77)) {T95 : Ty}
        (wf0 : (wfTy (HS ty k) T95)) :
        (wfTy k (tabs K77 T95))
    | wfTy_tapp {T96 : Ty}
        (wf : (wfTy k T96)) {T97 : Ty}
        (wf0 : (wfTy k T97)) :
        (wfTy k (tapp T96 T97))
    | wfTy_tarr {T98 : Ty}
        (wf : (wfTy k T98)) {T99 : Ty}
        (wf0 : (wfTy k T99)) :
        (wfTy k (tarr T98 T99))
    | wfTy_tall {K78 : Kind}
        (wf : (wfKind k K78))
        {T100 : Ty}
        (wf0 : (wfTy (HS ty k) T100)) :
        (wfTy k (tall K78 T100)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x6 : (Index tm))
        (wfi : (wfindex k x6)) :
        (wfTm k (var x6))
    | wfTm_abs {T95 : Ty}
        (wf : (wfTy k T95)) {t17 : Tm}
        (wf0 : (wfTm (HS tm k) t17)) :
        (wfTm k (abs T95 t17))
    | wfTm_app {t18 : Tm}
        (wf : (wfTm k t18)) {t19 : Tm}
        (wf0 : (wfTm k t19)) :
        (wfTm k (app t18 t19))
    | wfTm_tyabs {K77 : Kind}
        (wf : (wfKind k K77)) {t20 : Tm}
        (wf0 : (wfTm (HS ty k) t20)) :
        (wfTm k (tyabs K77 t20))
    | wfTm_tyapp {t21 : Tm}
        (wf : (wfTm k t21)) {T96 : Ty}
        (wf0 : (wfTy k T96)) :
        (wfTm k (tyapp t21 T96)).
  Definition inversion_wfKind_karr_0 (k0 : Hvl) (K1 : Kind) (K2 : Kind) (H24 : (wfKind k0 (karr K1 K2))) : (wfKind k0 K1) := match H24 in (wfKind _ K78) return match K78 return Prop with
    | (karr K1 K2) => (wfKind k0 K1)
    | _ => True
  end with
    | (wfKind_karr K1 H1 K2 H2) => H1
    | _ => I
  end.
  Definition inversion_wfKind_karr_1 (k0 : Hvl) (K1 : Kind) (K2 : Kind) (H24 : (wfKind k0 (karr K1 K2))) : (wfKind k0 K2) := match H24 in (wfKind _ K78) return match K78 return Prop with
    | (karr K1 K2) => (wfKind k0 K2)
    | _ => True
  end with
    | (wfKind_karr K1 H1 K2 H2) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tvar_1 (k1 : Hvl) (X : (Index ty)) (H25 : (wfTy k1 (tvar X))) : (wfindex k1 X) := match H25 in (wfTy _ S32) return match S32 return Prop with
    | (tvar X) => (wfindex k1 X)
    | _ => True
  end with
    | (wfTy_tvar X H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tabs_1 (k2 : Hvl) (K : Kind) (T : Ty) (H26 : (wfTy k2 (tabs K T))) : (wfKind k2 K) := match H26 in (wfTy _ S33) return match S33 return Prop with
    | (tabs K T) => (wfKind k2 K)
    | _ => True
  end with
    | (wfTy_tabs K H4 T H5) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tabs_2 (k2 : Hvl) (K : Kind) (T : Ty) (H26 : (wfTy k2 (tabs K T))) : (wfTy (HS ty k2) T) := match H26 in (wfTy _ S33) return match S33 return Prop with
    | (tabs K T) => (wfTy (HS ty k2) T)
    | _ => True
  end with
    | (wfTy_tabs K H4 T H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tapp_0 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k3 (tapp T1 T2))) : (wfTy k3 T1) := match H27 in (wfTy _ S34) return match S34 return Prop with
    | (tapp T1 T2) => (wfTy k3 T1)
    | _ => True
  end with
    | (wfTy_tapp T1 H6 T2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTy_tapp_1 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k3 (tapp T1 T2))) : (wfTy k3 T2) := match H27 in (wfTy _ S34) return match S34 return Prop with
    | (tapp T1 T2) => (wfTy k3 T2)
    | _ => True
  end with
    | (wfTy_tapp T1 H6 T2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H28 : (wfTy k4 (tarr T1 T2))) : (wfTy k4 T1) := match H28 in (wfTy _ S35) return match S35 return Prop with
    | (tarr T1 T2) => (wfTy k4 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H8 T2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H28 : (wfTy k4 (tarr T1 T2))) : (wfTy k4 T2) := match H28 in (wfTy _ S35) return match S35 return Prop with
    | (tarr T1 T2) => (wfTy k4 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H8 T2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k5 : Hvl) (K : Kind) (T : Ty) (H29 : (wfTy k5 (tall K T))) : (wfKind k5 K) := match H29 in (wfTy _ S36) return match S36 return Prop with
    | (tall K T) => (wfKind k5 K)
    | _ => True
  end with
    | (wfTy_tall K H10 T H11) => H10
    | _ => I
  end.
  Definition inversion_wfTy_tall_2 (k5 : Hvl) (K : Kind) (T : Ty) (H29 : (wfTy k5 (tall K T))) : (wfTy (HS ty k5) T) := match H29 in (wfTy _ S36) return match S36 return Prop with
    | (tall K T) => (wfTy (HS ty k5) T)
    | _ => True
  end with
    | (wfTy_tall K H10 T H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k6 : Hvl) (x : (Index tm)) (H30 : (wfTm k6 (var x))) : (wfindex k6 x) := match H30 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k6 x)
    | _ => True
  end with
    | (wfTm_var x H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k7 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTm k7 (abs T t))) : (wfTy k7 T) := match H31 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_abs T H13 t H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k7 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTm k7 (abs T t))) : (wfTm (HS tm k7) t) := match H31 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k7) t)
    | _ => True
  end with
    | (wfTm_abs T H13 t H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H32 : (wfTm k8 (app t1 t2))) : (wfTm k8 t1) := match H32 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_app t1 H15 t2 H16) => H15
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H32 : (wfTm k8 (app t1 t2))) : (wfTm k8 t2) := match H32 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_app t1 H15 t2 H16) => H16
    | _ => I
  end.
  Definition inversion_wfTm_tyabs_1 (k9 : Hvl) (K : Kind) (t : Tm) (H33 : (wfTm k9 (tyabs K t))) : (wfKind k9 K) := match H33 in (wfTm _ s2) return match s2 return Prop with
    | (tyabs K t) => (wfKind k9 K)
    | _ => True
  end with
    | (wfTm_tyabs K H17 t H18) => H17
    | _ => I
  end.
  Definition inversion_wfTm_tyabs_2 (k9 : Hvl) (K : Kind) (t : Tm) (H33 : (wfTm k9 (tyabs K t))) : (wfTm (HS ty k9) t) := match H33 in (wfTm _ s2) return match s2 return Prop with
    | (tyabs K t) => (wfTm (HS ty k9) t)
    | _ => True
  end with
    | (wfTm_tyabs K H17 t H18) => H18
    | _ => I
  end.
  Definition inversion_wfTm_tyapp_0 (k10 : Hvl) (t : Tm) (T : Ty) (H34 : (wfTm k10 (tyapp t T))) : (wfTm k10 t) := match H34 in (wfTm _ s3) return match s3 return Prop with
    | (tyapp t T) => (wfTm k10 t)
    | _ => True
  end with
    | (wfTm_tyapp t H19 T H20) => H19
    | _ => I
  end.
  Definition inversion_wfTm_tyapp_1 (k10 : Hvl) (t : Tm) (T : Ty) (H34 : (wfTm k10 (tyapp t T))) : (wfTy k10 T) := match H34 in (wfTm _ s3) return match s3 return Prop with
    | (tyapp t T) => (wfTy k10 T)
    | _ => True
  end with
    | (wfTm_tyapp t H19 T H20) => H20
    | _ => I
  end.
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c : (Cutoff tm)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k11 : Hvl)
        :
        (shifthvl_tm C0 k11 (HS tm k11))
    | shifthvl_tm_there_tm
        (c : (Cutoff tm)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_tm c k11 k12) -> (shifthvl_tm (CS c) (HS tm k11) (HS tm k12))
    | shifthvl_tm_there_ty
        (c : (Cutoff tm)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_tm c k11 k12) -> (shifthvl_tm c (HS ty k11) (HS ty k12)).
  Inductive shifthvl_ty : (forall (c : (Cutoff ty)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k11 : Hvl)
        :
        (shifthvl_ty C0 k11 (HS ty k11))
    | shifthvl_ty_there_tm
        (c : (Cutoff ty)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_ty c k11 k12) -> (shifthvl_ty c (HS tm k11) (HS tm k12))
    | shifthvl_ty_there_ty
        (c : (Cutoff ty)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_ty c k11 k12) -> (shifthvl_ty (CS c) (HS ty k11) (HS ty k12)).
  Lemma weaken_shifthvl_tm  :
    (forall (k11 : Hvl) {c : (Cutoff tm)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_tm c k12 k13) -> (shifthvl_tm (weakenCutofftm c k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k11 : Hvl) {c : (Cutoff ty)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_ty c k12 k13) -> (shifthvl_ty (weakenCutoffty c k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) (x6 : (Index tm)) ,
      (wfindex k11 x6) -> (wfindex k12 (shiftIndex c x6))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c : (Cutoff tm)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) (X46 : (Index ty)) ,
      (wfindex k11 X46) -> (wfindex k12 X46)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c : (Cutoff ty)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) (x6 : (Index tm)) ,
      (wfindex k11 x6) -> (wfindex k12 x6)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c : (Cutoff ty)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) (X46 : (Index ty)) ,
      (wfindex k11 X46) -> (wfindex k12 (tshiftIndex c X46))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfKind : (forall (k11 : Hvl) ,
    (forall (K79 : Kind) (wf : (wfKind k11 K79)) ,
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfKind k12 K79)))) := (fun (k11 : Hvl) =>
    (ind_wfKind k11 (fun (K79 : Kind) (wf : (wfKind k11 K79)) =>
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfKind k12 K79))) (fun (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
      (wfKind_star k12)) (fun (K1 : Kind) (wf : (wfKind k11 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k11 K2)) IHK2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
      (wfKind_karr k12 (IHK1 c k12 (weaken_shifthvl_tm H0 ins)) (IHK2 c k12 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfKind : (forall (k11 : Hvl) ,
    (forall (K79 : Kind) (wf : (wfKind k11 K79)) ,
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfKind k12 K79)))) := (fun (k11 : Hvl) =>
    (ind_wfKind k11 (fun (K79 : Kind) (wf : (wfKind k11 K79)) =>
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfKind k12 K79))) (fun (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
      (wfKind_star k12)) (fun (K1 : Kind) (wf : (wfKind k11 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k11 K2)) IHK2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
      (wfKind_karr k12 (IHK1 c k12 (weaken_shifthvl_ty H0 ins)) (IHK2 c k12 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTy : (forall (k11 : Hvl) ,
    (forall (S37 : Ty) (wf : (wfTy k11 S37)) ,
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfTy k12 S37)))) := (ind_wfTy (fun (k11 : Hvl) (S37 : Ty) (wf : (wfTy k11 S37)) =>
    (forall (c : (Cutoff tm)) (k12 : Hvl) ,
      (shifthvl_tm c k11 k12) -> (wfTy k12 S37))) (fun (k11 : Hvl) (X46 : (Index ty)) (wfi : (wfindex k11 X46)) (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tvar k12 _ (shift_wfindex_ty c k11 k12 ins X46 wfi))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tabs k12 (shift_wfKind k11 K wf c k12 (weaken_shifthvl_tm H0 ins)) (IHT c (HS ty k12) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tapp k12 (IHT1 c k12 (weaken_shifthvl_tm H0 ins)) (IHT2 c k12 (weaken_shifthvl_tm H0 ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tarr k12 (IHT1 c k12 (weaken_shifthvl_tm H0 ins)) (IHT2 c k12 (weaken_shifthvl_tm H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tall k12 (shift_wfKind k11 K wf c k12 (weaken_shifthvl_tm H0 ins)) (IHT c (HS ty k12) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k11 : Hvl) ,
    (forall (S37 : Ty) (wf : (wfTy k11 S37)) ,
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfTy k12 (tshiftTy c S37))))) := (ind_wfTy (fun (k11 : Hvl) (S37 : Ty) (wf : (wfTy k11 S37)) =>
    (forall (c : (Cutoff ty)) (k12 : Hvl) ,
      (shifthvl_ty c k11 k12) -> (wfTy k12 (tshiftTy c S37)))) (fun (k11 : Hvl) (X46 : (Index ty)) (wfi : (wfindex k11 X46)) (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tvar k12 _ (tshift_wfindex_ty c k11 k12 ins X46 wfi))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tabs k12 (tshift_wfKind k11 K wf c k12 (weaken_shifthvl_ty H0 ins)) (IHT (CS c) (HS ty k12) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tapp k12 (IHT1 c k12 (weaken_shifthvl_ty H0 ins)) (IHT2 c k12 (weaken_shifthvl_ty H0 ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tarr k12 (IHT1 c k12 (weaken_shifthvl_ty H0 ins)) (IHT2 c k12 (weaken_shifthvl_ty H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tall k12 (tshift_wfKind k11 K wf c k12 (weaken_shifthvl_ty H0 ins)) (IHT (CS c) (HS ty k12) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k11 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k11 s4)) ,
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfTm k12 (shiftTm c s4))))) := (ind_wfTm (fun (k11 : Hvl) (s4 : Tm) (wf : (wfTm k11 s4)) =>
    (forall (c : (Cutoff tm)) (k12 : Hvl) ,
      (shifthvl_tm c k11 k12) -> (wfTm k12 (shiftTm c s4)))) (fun (k11 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k11 x6)) (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_var k12 _ (shift_wfindex_tm c k11 k12 ins x6 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) (t : Tm) (wf0 : (wfTm (HS tm k11) t)) IHt (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_abs k12 (shift_wfTy k11 T wf c k12 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k12) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_app k12 (IHt1 c k12 (weaken_shifthvl_tm H0 ins)) (IHt2 c k12 (weaken_shifthvl_tm H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (t : Tm) (wf0 : (wfTm (HS ty k11) t)) IHt (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_tyabs k12 (shift_wfKind k11 K wf c k12 (weaken_shifthvl_tm H0 ins)) (IHt c (HS ty k12) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (T : Ty) (wf0 : (wfTy k11 T)) (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_tyapp k12 (IHt c k12 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k11 T wf0 c k12 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k11 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k11 s4)) ,
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfTm k12 (tshiftTm c s4))))) := (ind_wfTm (fun (k11 : Hvl) (s4 : Tm) (wf : (wfTm k11 s4)) =>
    (forall (c : (Cutoff ty)) (k12 : Hvl) ,
      (shifthvl_ty c k11 k12) -> (wfTm k12 (tshiftTm c s4)))) (fun (k11 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k11 x6)) (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_var k12 _ (tshift_wfindex_tm c k11 k12 ins x6 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) (t : Tm) (wf0 : (wfTm (HS tm k11) t)) IHt (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_abs k12 (tshift_wfTy k11 T wf c k12 (weaken_shifthvl_ty H0 ins)) (IHt c (HS tm k12) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_app k12 (IHt1 c k12 (weaken_shifthvl_ty H0 ins)) (IHt2 c k12 (weaken_shifthvl_ty H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (t : Tm) (wf0 : (wfTm (HS ty k11) t)) IHt (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_tyabs k12 (tshift_wfKind k11 K wf c k12 (weaken_shifthvl_ty H0 ins)) (IHt (CS c) (HS ty k12) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (T : Ty) (wf0 : (wfTy k11 T)) (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_tyapp k12 (IHt c k12 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k11 T wf0 c k12 (weaken_shifthvl_ty H0 ins))))).
  Fixpoint weaken_wfKind (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (K79 : Kind) (wf : (wfKind k12 K79)) ,
    (wfKind (appendHvl k12 k11) (weakenKind K79 k11))) :=
    match k11 return (forall (k12 : Hvl) (K79 : Kind) (wf : (wfKind k12 K79)) ,
      (wfKind (appendHvl k12 k11) (weakenKind K79 k11))) with
      | (H0) => (fun (k12 : Hvl) (K79 : Kind) (wf : (wfKind k12 K79)) =>
        wf)
      | (HS tm k11) => (fun (k12 : Hvl) (K79 : Kind) (wf : (wfKind k12 K79)) =>
        (shift_wfKind (appendHvl k12 k11) (weakenKind K79 k11) (weaken_wfKind k11 k12 K79 wf) C0 (HS tm (appendHvl k12 k11)) (shifthvl_tm_here (appendHvl k12 k11))))
      | (HS ty k11) => (fun (k12 : Hvl) (K79 : Kind) (wf : (wfKind k12 K79)) =>
        (tshift_wfKind (appendHvl k12 k11) (weakenKind K79 k11) (weaken_wfKind k11 k12 K79 wf) C0 (HS ty (appendHvl k12 k11)) (shifthvl_ty_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfTy (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) ,
    (wfTy (appendHvl k12 k11) (weakenTy S37 k11))) :=
    match k11 return (forall (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) ,
      (wfTy (appendHvl k12 k11) (weakenTy S37 k11))) with
      | (H0) => (fun (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) =>
        wf)
      | (HS tm k11) => (fun (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) =>
        (shift_wfTy (appendHvl k12 k11) (weakenTy S37 k11) (weaken_wfTy k11 k12 S37 wf) C0 (HS tm (appendHvl k12 k11)) (shifthvl_tm_here (appendHvl k12 k11))))
      | (HS ty k11) => (fun (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) =>
        (tshift_wfTy (appendHvl k12 k11) (weakenTy S37 k11) (weaken_wfTy k11 k12 S37 wf) C0 (HS ty (appendHvl k12 k11)) (shifthvl_ty_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfTm (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) ,
    (wfTm (appendHvl k12 k11) (weakenTm s4 k11))) :=
    match k11 return (forall (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) ,
      (wfTm (appendHvl k12 k11) (weakenTm s4 k11))) with
      | (H0) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        wf)
      | (HS tm k11) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        (shift_wfTm (appendHvl k12 k11) (weakenTm s4 k11) (weaken_wfTm k11 k12 s4 wf) C0 (HS tm (appendHvl k12 k11)) (shifthvl_tm_here (appendHvl k12 k11))))
      | (HS ty k11) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        (tshift_wfTm (appendHvl k12 k11) (weakenTm s4 k11) (weaken_wfTm k11 k12 s4 wf) C0 (HS ty (appendHvl k12 k11)) (shifthvl_ty_here (appendHvl k12 k11))))
    end.
End ShiftWellFormed.
Lemma wfKind_cast  :
  (forall (k11 : Hvl) (K79 : Kind) (k12 : Hvl) (K80 : Kind) ,
    (k11 = k12) -> (K79 = K80) -> (wfKind k11 K79) -> (wfKind k12 K80)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k11 : Hvl) (S37 : Ty) (k12 : Hvl) (S38 : Ty) ,
    (k11 = k12) -> (S37 = S38) -> (wfTy k11 S37) -> (wfTy k12 S38)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k11 : Hvl) (s4 : Tm) (k12 : Hvl) (s5 : Tm) ,
    (k11 = k12) -> (s4 = s5) -> (wfTm k11 s4) -> (wfTm k12 s5)).
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
  Inductive substhvl_tm (k11 : Hvl) : (forall (d : (Trace tm)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k11 X0 (HS tm k11) k11)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_tm k11 d k12 k13) -> (substhvl_tm k11 (XS tm d) (HS tm k12) (HS tm k13))
    | substhvl_tm_there_ty
        {d : (Trace tm)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_tm k11 d k12 k13) -> (substhvl_tm k11 (XS ty d) (HS ty k12) (HS ty k13)).
  Inductive substhvl_ty (k11 : Hvl) : (forall (d : (Trace ty)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k11 X0 (HS ty k11) k11)
    | substhvl_ty_there_tm
        {d : (Trace ty)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_ty k11 d k12 k13) -> (substhvl_ty k11 (XS tm d) (HS tm k12) (HS tm k13))
    | substhvl_ty_there_ty
        {d : (Trace ty)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_ty k11 d k12 k13) -> (substhvl_ty k11 (XS ty d) (HS ty k12) (HS ty k13)).
  Lemma weaken_substhvl_tm  :
    (forall {k12 : Hvl} (k11 : Hvl) {d : (Trace tm)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_tm k12 d k13 k14) -> (substhvl_tm k12 (weakenTrace d k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k12 : Hvl} (k11 : Hvl) {d : (Trace ty)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_ty k12 d k13 k14) -> (substhvl_ty k12 (weakenTrace d k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k11 : Hvl} {s4 : Tm} (wft : (wfTm k11 s4)) :
    (forall {d : (Trace tm)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (forall {x6 : (Index tm)} ,
        (wfindex k12 x6) -> (wfTm k13 (substIndex d s4 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k11 : Hvl} {S37 : Ty} (wft : (wfTy k11 S37)) :
    (forall {d : (Trace ty)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (forall {X46 : (Index ty)} ,
        (wfindex k12 X46) -> (wfTy k13 (tsubstIndex d S37 X46)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k11 : Hvl} :
    (forall {d : (Trace tm)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (forall {X46 : (Index ty)} ,
        (wfindex k12 X46) -> (wfindex k13 X46))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k11 : Hvl} :
    (forall {d : (Trace ty)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (forall {x6 : (Index tm)} ,
        (wfindex k12 x6) -> (wfindex k13 x6))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfKind {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (K79 : Kind) (wf0 : (wfKind k12 K79)) ,
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfKind k13 K79)))) := (fun (k12 : Hvl) =>
    (ind_wfKind k12 (fun (K79 : Kind) (wf0 : (wfKind k12 K79)) =>
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfKind k13 K79))) (fun {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
      (wfKind_star k13)) (fun (K1 : Kind) (wf0 : (wfKind k12 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k12 K2)) IHK2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
      (wfKind_karr k13 (IHK1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHK2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfKind {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (K79 : Kind) (wf0 : (wfKind k12 K79)) ,
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfKind k13 K79)))) := (fun (k12 : Hvl) =>
    (ind_wfKind k12 (fun (K79 : Kind) (wf0 : (wfKind k12 K79)) =>
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfKind k13 K79))) (fun {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
      (wfKind_star k13)) (fun (K1 : Kind) (wf0 : (wfKind k12 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k12 K2)) IHK2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
      (wfKind_karr k13 (IHK1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHK2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTy {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (S37 : Ty) (wf0 : (wfTy k12 S37)) ,
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfTy k13 S37)))) := (ind_wfTy (fun (k12 : Hvl) (S37 : Ty) (wf0 : (wfTy k12 S37)) =>
    (forall {d : (Trace tm)} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (wfTy k13 S37))) (fun (k12 : Hvl) {X46 : (Index ty)} (wfi : (wfindex k12 X46)) {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tvar k13 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tabs k13 (substhvl_tm_wfKind k12 K wf0 (weaken_substhvl_tm H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tapp k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tarr k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tall k13 (substhvl_tm_wfKind k12 K wf0 (weaken_substhvl_tm H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k11 : Hvl} {S37 : Ty} (wf : (wfTy k11 S37)) : (forall (k12 : Hvl) ,
    (forall (S38 : Ty) (wf0 : (wfTy k12 S38)) ,
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfTy k13 (tsubstTy d S37 S38))))) := (ind_wfTy (fun (k12 : Hvl) (S38 : Ty) (wf0 : (wfTy k12 S38)) =>
    (forall {d : (Trace ty)} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (wfTy k13 (tsubstTy d S37 S38)))) (fun (k12 : Hvl) {X46 : (Index ty)} (wfi : (wfindex k12 X46)) {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tabs k13 (substhvl_ty_wfKind k12 K wf0 (weaken_substhvl_ty H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tapp k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tarr k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tall k13 (substhvl_ty_wfKind k12 K wf0 (weaken_substhvl_ty H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k11 : Hvl} {s4 : Tm} (wf : (wfTm k11 s4)) : (forall (k12 : Hvl) ,
    (forall (s5 : Tm) (wf0 : (wfTm k12 s5)) ,
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfTm k13 (substTm d s4 s5))))) := (ind_wfTm (fun (k12 : Hvl) (s5 : Tm) (wf0 : (wfTm k12 s5)) =>
    (forall {d : (Trace tm)} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (wfTm k13 (substTm d s4 s5)))) (fun (k12 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k12 x6)) {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (t : Tm) (wf1 : (wfTm (HS tm k12) t)) IHt {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_abs k13 (substhvl_tm_wfTy k12 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k13) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_app k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (t : Tm) (wf1 : (wfTm (HS ty k12) t)) IHt {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_tyabs k13 (substhvl_tm_wfKind k12 K wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt (T : Ty) (wf1 : (wfTy k12 T)) {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_tyapp k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k12 T wf1 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k11 : Hvl} {S37 : Ty} (wf : (wfTy k11 S37)) : (forall (k12 : Hvl) ,
    (forall (s4 : Tm) (wf0 : (wfTm k12 s4)) ,
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfTm k13 (tsubstTm d S37 s4))))) := (ind_wfTm (fun (k12 : Hvl) (s4 : Tm) (wf0 : (wfTm k12 s4)) =>
    (forall {d : (Trace ty)} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (wfTm k13 (tsubstTm d S37 s4)))) (fun (k12 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k12 x6)) {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_var k13 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (t : Tm) (wf1 : (wfTm (HS tm k12) t)) IHt {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_abs k13 (substhvl_ty_wfTy wf k12 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k13) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_app k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (t : Tm) (wf1 : (wfTm (HS ty k12) t)) IHt {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_tyabs k13 (substhvl_ty_wfKind k12 K wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt (T : Ty) (wf1 : (wfTy k12 T)) {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_tyapp k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k12 T wf1 (weaken_substhvl_ty H0 del))))).
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
  Fixpoint weakenEnv (G : Env) (k11 : Hvl) {struct k11} :
  Env :=
    match k11 with
      | (H0) => G
      | (HS tm k11) => (weakenEnv G k11)
      | (HS ty k11) => (tshiftEnv C0 (weakenEnv G k11))
    end.
  Fixpoint substEnv (d : (Trace tm)) (s4 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s4 G0) T)
      | (etvar G0 K) => (etvar (substEnv d s4 G0) K)
    end.
  Fixpoint tsubstEnv (d : (Trace ty)) (S37 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d S37 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S37 T))
      | (etvar G0 K) => (etvar (tsubstEnv d S37 G0) K)
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
    (forall (d : (Trace ty)) (S37 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d S37 G)) = (domainEnv G))).
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
      (forall (d : (Trace ty)) (S37 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d S37 (appendEnv G G0)) = (appendEnv (tsubstEnv d S37 G) (tsubstEnv (weakenTrace d (domainEnv G)) S37 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenKind_append  :
    (forall (K79 : Kind) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenKind (weakenKind K79 k11) k12) = (weakenKind K79 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S37 : Ty) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTy (weakenTy S37 k11) k12) = (weakenTy S37 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s4 : Tm) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTm (weakenTm s4 k11) k12) = (weakenTm s4 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T95 : Ty) :
          (wfTy (domainEnv G) T95) -> (lookup_evar (evar G T95) I0 T95)
      | lookup_evar_there_evar
          {G : Env} {x6 : (Index tm)}
          (T96 : Ty) (T97 : Ty) :
          (lookup_evar G x6 T96) -> (lookup_evar (evar G T97) (IS x6) T96)
      | lookup_evar_there_etvar
          {G : Env} {x6 : (Index tm)}
          (T96 : Ty) (K79 : Kind) :
          (lookup_evar G x6 T96) -> (lookup_evar (etvar G K79) x6 (tshiftTy C0 T96)).
    Inductive lookup_etvar : Env -> (Index ty) -> Kind -> Prop :=
      | lookup_etvar_here {G : Env}
          (K79 : Kind) :
          (wfKind (domainEnv G) K79) -> (lookup_etvar (etvar G K79) I0 K79)
      | lookup_etvar_there_evar
          {G : Env} {X46 : (Index ty)}
          (K80 : Kind) (T96 : Ty) :
          (lookup_etvar G X46 K80) -> (lookup_etvar (evar G T96) X46 K80)
      | lookup_etvar_there_etvar
          {G : Env} {X46 : (Index ty)}
          (K80 : Kind) (K81 : Kind) :
          (lookup_etvar G X46 K80) -> (lookup_etvar (etvar G K81) (IS X46) K80).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T96 : Ty) (T97 : Ty) ,
        (lookup_evar (evar G T96) I0 T97) -> (T96 = T97)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (K80 : Kind) (K81 : Kind) ,
        (lookup_etvar (etvar G K80) I0 K81) -> (K80 = K81)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x6 : (Index tm)} ,
        (forall (T96 : Ty) ,
          (lookup_evar G x6 T96) -> (forall (T97 : Ty) ,
            (lookup_evar G x6 T97) -> (T96 = T97)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X46 : (Index ty)} ,
        (forall (K80 : Kind) ,
          (lookup_etvar G X46 K80) -> (forall (K81 : Kind) ,
            (lookup_etvar G X46 K81) -> (K80 = K81)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x6 : (Index tm)} (T96 : Ty) ,
        (lookup_evar G x6 T96) -> (wfTy (domainEnv G) T96)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X46 : (Index ty)} (K80 : Kind) ,
        (lookup_etvar G X46 K80) -> (wfKind (domainEnv G) K80)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x6 : (Index tm)} (T96 : Ty) ,
        (lookup_evar G x6 T96) -> (lookup_evar (appendEnv G G0) (weakenIndextm x6 (domainEnv G0)) (weakenTy T96 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X46 : (Index ty)} (K80 : Kind) ,
        (lookup_etvar G X46 K80) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X46 (domainEnv G0)) (weakenKind K80 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x6 : (Index tm)} (T98 : Ty) ,
        (lookup_evar G x6 T98) -> (wfindex (domainEnv G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X46 : (Index ty)} (K82 : Kind) ,
        (lookup_etvar G X46 K82) -> (wfindex (domainEnv G) X46)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T96 : Ty} :
        (shift_evar C0 G (evar G T96))
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
        {K80 : Kind} :
        (shift_etvar C0 G (etvar G K80))
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
  Inductive subst_evar (G : Env) (T96 : Ty) (s4 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T96 s4 X0 (evar G T96) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T97 : Ty) :
        (subst_evar G T96 s4 d G0 G1) -> (subst_evar G T96 s4 (XS tm d) (evar G0 T97) (evar G1 T97))
    | subst_evar_there_etvar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (K80 : Kind) :
        (subst_evar G T96 s4 d G0 G1) -> (subst_evar G T96 s4 (XS ty d) (etvar G0 K80) (etvar G1 K80)).
  Lemma weaken_subst_evar {G : Env} (T96 : Ty) {s4 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T96 s4 d G1 G2) -> (subst_evar G T96 s4 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (K80 : Kind) (S37 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K80 S37 X0 (etvar G K80) G)
    | subst_etvar_there_evar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T96 : Ty) :
        (subst_etvar G K80 S37 d G0 G1) -> (subst_etvar G K80 S37 (XS tm d) (evar G0 T96) (evar G1 (tsubstTy d S37 T96)))
    | subst_etvar_there_etvar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (K81 : Kind) :
        (subst_etvar G K80 S37 d G0 G1) -> (subst_etvar G K80 S37 (XS ty d) (etvar G0 K81) (etvar G1 K81)).
  Lemma weaken_subst_etvar {G : Env} (K80 : Kind) {S37 : Ty} :
    (forall (G0 : Env) {d : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G K80 S37 d G1 G2) -> (subst_etvar G K80 S37 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d S37 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s4 : Tm} (T96 : Ty) :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T96 s4 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S37 : Ty} (K80 : Kind) :
    (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G K80 S37 d G0 G1) -> (substhvl_ty (domainEnv G) d (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T96 : Ty} (wf : (wfTy (domainEnv G) T96)) ,
    (lookup_evar (appendEnv (evar G T96) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T96 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {K80 : Kind} (wf : (wfKind (domainEnv G) K80)) ,
    (lookup_etvar (appendEnv (etvar G K80) G0) (weakenIndexty I0 (domainEnv G0)) (weakenKind K80 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfKind wfTm wfTy : infra.
 Hint Constructors wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H41 : (wfKind _ (star)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfKind _ (karr _ _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H41 : (wfTy _ (tvar _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tabs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tapp _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tarr _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tall _ _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H41 : (wfTm _ (var _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (abs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (app _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (tyabs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (tyapp _ _)) |- _ => inversion H41; subst; clear H41
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
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x6 : (Index tm)} {T96 : Ty} ,
    (lookup_evar G x6 T96) -> (lookup_evar G0 (shiftIndex c x6) T96)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X46 : (Index ty)} {K80 : Kind} ,
    (lookup_etvar G X46 K80) -> (lookup_etvar G0 X46 K80)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x6 : (Index tm)} {T96 : Ty} ,
    (lookup_evar G x6 T96) -> (lookup_evar G0 x6 (tshiftTy c T96))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X46 : (Index ty)} {K80 : Kind} ,
    (lookup_etvar G X46 K80) -> (lookup_etvar G0 (tshiftIndex c X46) K80)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T97 : Ty) {s4 : Tm} :
  (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T97 s4 d G0 G1)) {X46 : (Index ty)} (K81 : Kind) ,
    (lookup_etvar G0 X46 K81) -> (lookup_etvar G1 X46 K81)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} (K81 : Kind) {S37 : Ty} (wf : (wfTy (domainEnv G) S37)) :
  (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G K81 S37 d G0 G1)) {x6 : (Index tm)} (T97 : Ty) ,
    (lookup_evar G0 x6 T97) -> (lookup_evar G1 x6 (tsubstTy d S37 T97))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Kind (K77 : Kind) {struct K77} :
nat :=
  match K77 with
    | (star) => 1
    | (karr K78 K79) => (plus 1 (plus (size_Kind K78) (size_Kind K79)))
  end.
Fixpoint size_Ty (S32 : Ty) {struct S32} :
nat :=
  match S32 with
    | (tvar X46) => 1
    | (tabs K77 T95) => (plus 1 (plus (size_Kind K77) (size_Ty T95)))
    | (tapp T96 T97) => (plus 1 (plus (size_Ty T96) (size_Ty T97)))
    | (tarr T98 T99) => (plus 1 (plus (size_Ty T98) (size_Ty T99)))
    | (tall K78 T100) => (plus 1 (plus (size_Kind K78) (size_Ty T100)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x6) => 1
    | (abs T95 t17) => (plus 1 (plus (size_Ty T95) (size_Tm t17)))
    | (app t18 t19) => (plus 1 (plus (size_Tm t18) (size_Tm t19)))
    | (tyabs K77 t20) => (plus 1 (plus (size_Kind K77) (size_Tm t20)))
    | (tyapp t21 T96) => (plus 1 (plus (size_Tm t21) (size_Ty T96)))
  end.
Fixpoint tshift_size_Ty (S32 : Ty) (c : (Cutoff ty)) {struct S32} :
((size_Ty (tshiftTy c S32)) = (size_Ty S32)) :=
  match S32 return ((size_Ty (tshiftTy c S32)) = (size_Ty S32)) with
    | (tvar _) => eq_refl
    | (tabs K T) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (tshift_size_Ty T (CS c))))
    | (tapp T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tall K T) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (tshift_size_Ty T (CS c))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (tyabs K t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t c)))
    | (tyapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c) eq_refl))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
    | (tyabs K t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (tshift_size_Tm t (CS c))))
    | (tyapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c) (tshift_size_Ty T c)))
  end.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Kind  :
  (forall (k : Hvl) (K77 : Kind) ,
    ((size_Kind (weakenKind K77 k)) = (size_Kind K77))).
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
      (H26 : (wfKind (domainEnv G) K))
      (H27 : (wfindex (domainEnv G) X))
      : (TRed G (tvar X) (tvar X) K)
  | QR_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm26 : (TRed G S1 T1 (star)))
      (jm27 : (TRed G S2 T2 (star))) :
      (TRed G (tarr S1 S2) (tarr T1 T2) (star))
  | QR_Abs (K1 : Kind) (K2 : Kind)
      (S2 : Ty) (T2 : Ty)
      (jm28 : (TRed (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0))))
      (H32 : (wfKind (domainEnv G) K1))
      (H33 : (wfKind (domainEnv G) K2))
      :
      (TRed G (tabs K1 S2) (tabs K1 T2) (karr K1 K2))
  | QR_App (K1 : Kind) (K2 : Kind)
      (S1 : Ty) (S2 : Ty) (T1 : Ty)
      (T2 : Ty)
      (jm29 : (TRed G S1 T1 (karr K2 K1)))
      (jm30 : (TRed G S2 T2 K2)) :
      (TRed G (tapp S1 S2) (tapp T1 T2) K1)
  | QR_All (K1 : Kind) (S2 : Ty)
      (T2 : Ty)
      (jm31 : (TRed (etvar G K1) S2 T2 (star)))
      (H42 : (wfKind (domainEnv G) K1))
      :
      (TRed G (tall K1 S2) (tall K1 T2) (star))
  | QR_Beta (K1 : Kind)
      (K2 : Kind) (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm32 : (TRed (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0))))
      (jm33 : (TRed G S2 T2 K2))
      (H45 : (wfKind (domainEnv G) K1))
      :
      (TRed G (tapp (tabs K2 S1) S2) (tsubstTy X0 T2 T1) K1).
Inductive Kinding (G : Env) : Ty -> Kind -> Prop :=
  | K_TVar (K : Kind)
      (X : (Index ty))
      (lk : (lookup_etvar G X K))
      (H25 : (wfKind (domainEnv G) K))
      (H26 : (wfindex (domainEnv G) X))
      : (Kinding G (tvar X) K)
  | K_Abs (K1 : Kind) (K2 : Kind)
      (T2 : Ty)
      (jm : (Kinding (etvar G K1) T2 (weakenKind K2 (HS ty H0))))
      (H27 : (wfKind (domainEnv G) K1))
      (H28 : (wfKind (domainEnv G) K2))
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
      (Kinding G (tarr T1 T2) (star))
  | K_All (K1 : Kind) (T2 : Ty)
      (jm4 : (Kinding (etvar G K1) T2 (star)))
      (H36 : (wfKind (domainEnv G) K1))
      :
      (Kinding G (tall K1 T2) (star)).
Inductive TRedStar (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | QRS_Nil (K : Kind) (T : Ty)
      (jm34 : (Kinding G T K)) :
      (TRedStar G T T K)
  | QRS_Cons (K : Kind) (S1 : Ty)
      (T : Ty) (U : Ty)
      (jm35 : (TRedStar G S1 T K))
      (jm36 : (TRed G T U K)) :
      (TRedStar G S1 U K).
Inductive TyEq (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | Q_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm14 : (TyEq G S1 T1 (star)))
      (jm15 : (TyEq G S2 T2 (star))) :
      (TyEq G (tarr S1 S2) (tarr T1 T2) (star))
  | Q_Abs (K1 : Kind) (K2 : Kind)
      (S2 : Ty) (T2 : Ty)
      (jm16 : (TyEq (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0))))
      (H30 : (wfKind (domainEnv G) K1))
      (H31 : (wfKind (domainEnv G) K2))
      :
      (TyEq G (tabs K1 S2) (tabs K1 T2) (karr K1 K2))
  | Q_App (K1 : Kind) (K2 : Kind)
      (S1 : Ty) (S2 : Ty) (T1 : Ty)
      (T2 : Ty)
      (jm17 : (TyEq G S1 T1 (karr K1 K2)))
      (jm18 : (TyEq G S2 T2 K1)) :
      (TyEq G (tapp S1 S2) (tapp T1 T2) K2)
  | Q_All (K1 : Kind) (S2 : Ty)
      (T2 : Ty)
      (jm19 : (TyEq (etvar G K1) S2 T2 (star)))
      (H40 : (wfKind (domainEnv G) K1))
      :
      (TyEq G (tall K1 S2) (tall K1 T2) (star))
  | Q_Beta (K11 : Kind)
      (K12 : Kind) (T12 : Ty)
      (T2 : Ty)
      (jm20 : (Kinding (etvar G K11) T12 (weakenKind K12 (HS ty H0))))
      (jm21 : (Kinding G T2 K11))
      (H44 : (wfKind (domainEnv G) K12))
      :
      (TyEq G (tapp (tabs K11 T12) T2) (tsubstTy X0 T2 T12) K12)
  | Q_Refl (K : Kind) (T : Ty)
      (jm22 : (Kinding G T K)) :
      (TyEq G T T K)
  | Q_Symm (K : Kind) (T : Ty)
      (U : Ty) (jm23 : (TyEq G T U K))
      : (TyEq G U T K)
  | Q_Trans (K : Kind) (T : Ty)
      (U : Ty) (V : Ty)
      (jm24 : (TyEq G T U K))
      (jm25 : (TyEq G U V K)) :
      (TyEq G T V K).
Inductive Typing (G : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (y : (Index tm))
      (lk0 : (lookup_evar G y T))
      (H25 : (wfTy (domainEnv G) T))
      (H26 : (wfindex (domainEnv G) y))
      : (Typing G (var y) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm5 : (Kinding G T1 (star)))
      (jm6 : (Typing (evar G T1) t (weakenTy T2 (HS tm H0))))
      (H28 : (wfTy (domainEnv G) T2))
      :
      (Typing G (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm7 : (Typing G t1 (tarr T11 T12)))
      (jm8 : (Typing G t2 T11)) :
      (Typing G (app t1 t2) T12)
  | T_TAbs (K : Kind) (T : Ty)
      (t : Tm)
      (jm9 : (Typing (etvar G K) t T))
      (H34 : (wfKind (domainEnv G) K))
      :
      (Typing G (tyabs K t) (tall K T))
  | T_TApp (K11 : Kind) (T12 : Ty)
      (T2 : Ty) (t1 : Tm)
      (jm10 : (Typing G t1 (tall K11 T12)))
      (jm11 : (Kinding G T2 K11)) :
      (Typing G (tyapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Eq (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm12 : (Typing G t S1))
      (jm13 : (TyEq G S1 T (star))) :
      (Typing G t T).
Lemma TRed_cast  :
  (forall (G : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (G0 : Env) (T100 : Ty) (T101 : Ty) (K83 : Kind) ,
    (G = G0) -> (T98 = T100) -> (T99 = T101) -> (K82 = K83) -> (TRed G T98 T99 K82) -> (TRed G0 T100 T101 K83)).
Proof.
  congruence .
Qed.
Lemma Kinding_cast  :
  (forall (G : Env) (T98 : Ty) (K82 : Kind) (G0 : Env) (T99 : Ty) (K83 : Kind) ,
    (G = G0) -> (T98 = T99) -> (K82 = K83) -> (Kinding G T98 K82) -> (Kinding G0 T99 K83)).
Proof.
  congruence .
Qed.
Lemma TRedStar_cast  :
  (forall (G : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (G0 : Env) (T100 : Ty) (T101 : Ty) (K83 : Kind) ,
    (G = G0) -> (T98 = T100) -> (T99 = T101) -> (K82 = K83) -> (TRedStar G T98 T99 K82) -> (TRedStar G0 T100 T101 K83)).
Proof.
  congruence .
Qed.
Lemma TyEq_cast  :
  (forall (G : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (G0 : Env) (T100 : Ty) (T101 : Ty) (K83 : Kind) ,
    (G = G0) -> (T98 = T100) -> (T99 = T101) -> (K82 = K83) -> (TyEq G T98 T99 K82) -> (TyEq G0 T100 T101 K83)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G : Env) (t17 : Tm) (T98 : Ty) (G0 : Env) (t18 : Tm) (T99 : Ty) ,
    (G = G0) -> (t17 = t18) -> (T98 = T99) -> (Typing G t17 T98) -> (Typing G0 t18 T99)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_TRed (G9 : Env) (T113 : Ty) (T114 : Ty) (K94 : Kind) (jm50 : (TRed G9 T113 T114 K94)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) ,
  (TRed G10 T113 T114 K94)) :=
  match jm50 in (TRed _ T113 T114 K94) return (forall (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) ,
    (TRed G10 T113 T114 K94)) with
    | (QR_Var K91 X51 lk1 H64 H65) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Var G10 K91 X51 (shift_evar_lookup_etvar H92 lk1) (shift_wfKind _ _ H64 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92))) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)) _ H65)))
    | (QR_Arrow S37 S38 T111 T112 jm42 jm43) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Arrow G10 S37 S38 T111 T112 (shift_evar_TRed G9 S37 T111 (star) jm42 c G10 (weaken_shift_evar empty H92)) (shift_evar_TRed G9 S38 T112 (star) jm43 c G10 (weaken_shift_evar empty H92))))
    | (QR_Abs K92 K93 S38 T112 jm44 H70 H71) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Abs G10 K92 K93 S38 T112 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TRed (etvar G9 K92) S38 T112 (weakenKind K93 (HS ty H0)) jm44 c (etvar G10 K92) (weaken_shift_evar (etvar empty K92) H92))) (shift_wfKind _ _ H70 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92))) (shift_wfKind _ _ H71 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)))))
    | (QR_App K92 K93 S37 S38 T111 T112 jm45 jm46) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_App G10 K92 K93 S37 S38 T111 T112 (shift_evar_TRed G9 S37 T111 (karr K93 K92) jm45 c G10 (weaken_shift_evar empty H92)) (shift_evar_TRed G9 S38 T112 K93 jm46 c G10 (weaken_shift_evar empty H92))))
    | (QR_All K92 S38 T112 jm47 H80) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_All G10 K92 S38 T112 (shift_evar_TRed (etvar G9 K92) S38 T112 (star) jm47 c (etvar G10 K92) (weaken_shift_evar (etvar empty K92) H92)) (shift_wfKind _ _ H80 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)))))
    | (QR_Beta K92 K93 S37 S38 T111 T112 jm48 jm49 H83) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Beta G10 K92 K93 S37 S38 T111 T112 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TRed (etvar G9 K93) S37 T111 (weakenKind K92 (HS ty H0)) jm48 c (etvar G10 K93) (weaken_shift_evar (etvar empty K93) H92))) (shift_evar_TRed G9 S38 T112 K93 jm49 c G10 (weaken_shift_evar empty H92)) (shift_wfKind _ _ H83 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)))))
  end.
Fixpoint shift_etvar_TRed (G9 : Env) (T113 : Ty) (T114 : Ty) (K94 : Kind) (jm50 : (TRed G9 T113 T114 K94)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) ,
  (TRed G10 (tshiftTy c T113) (tshiftTy c T114) K94)) :=
  match jm50 in (TRed _ T113 T114 K94) return (forall (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) ,
    (TRed G10 (tshiftTy c T113) (tshiftTy c T114) K94)) with
    | (QR_Var K91 X51 lk1 H64 H65) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_Var G10 K91 (tshiftIndex c X51) (shift_etvar_lookup_etvar H92 lk1) (tshift_wfKind _ _ H64 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92))) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92)) _ H65)))
    | (QR_Arrow S37 S38 T111 T112 jm42 jm43) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_Arrow G10 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T111) (tshiftTy c T112) (shift_etvar_TRed G9 S37 T111 (star) jm42 c G10 (weaken_shift_etvar empty H92)) (shift_etvar_TRed G9 S38 T112 (star) jm43 c G10 (weaken_shift_etvar empty H92))))
    | (QR_Abs K92 K93 S38 T112 jm44 H70 H71) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_Abs G10 K92 K93 (tshiftTy (CS c) S38) (tshiftTy (CS c) T112) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TRed (etvar G9 K92) S38 T112 (weakenKind K93 (HS ty H0)) jm44 (CS c) (etvar G10 K92) (weaken_shift_etvar (etvar empty K92) H92))) (tshift_wfKind _ _ H70 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92))) (tshift_wfKind _ _ H71 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92)))))
    | (QR_App K92 K93 S37 S38 T111 T112 jm45 jm46) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_App G10 K92 K93 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T111) (tshiftTy c T112) (shift_etvar_TRed G9 S37 T111 (karr K93 K92) jm45 c G10 (weaken_shift_etvar empty H92)) (shift_etvar_TRed G9 S38 T112 K93 jm46 c G10 (weaken_shift_etvar empty H92))))
    | (QR_All K92 S38 T112 jm47 H80) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_All G10 K92 (tshiftTy (CS c) S38) (tshiftTy (CS c) T112) (shift_etvar_TRed (etvar G9 K92) S38 T112 (star) jm47 (CS c) (etvar G10 K92) (weaken_shift_etvar (etvar empty K92) H92)) (tshift_wfKind _ _ H80 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92)))))
    | (QR_Beta K92 K93 S37 S38 T111 T112 jm48 jm49 H83) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (TRed_cast G10 _ _ _ G10 (tshiftTy c (tapp (tabs K93 S37) S38)) (tshiftTy c (tsubstTy X0 T112 T111)) K92 eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T111 c T112)) eq_refl (QR_Beta G10 K92 K93 (tshiftTy (CS c) S37) (tshiftTy c S38) (tshiftTy (CS c) T111) (tshiftTy c T112) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TRed (etvar G9 K93) S37 T111 (weakenKind K92 (HS ty H0)) jm48 (CS c) (etvar G10 K93) (weaken_shift_etvar (etvar empty K93) H92))) (shift_etvar_TRed G9 S38 T112 K93 jm49 c G10 (weaken_shift_etvar empty H92)) (tshift_wfKind _ _ H83 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92))))))
  end.
Fixpoint shift_evar_Kinding (G9 : Env) (T113 : Ty) (K96 : Kind) (jm48 : (Kinding G9 T113 K96)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) ,
  (Kinding G10 T113 K96)) :=
  match jm48 in (Kinding _ T113 K96) return (forall (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) ,
    (Kinding G10 T113 K96)) with
    | (K_TVar K91 X51 lk1 H64 H65) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_TVar G10 K91 X51 (shift_evar_lookup_etvar H79 lk1) (shift_wfKind _ _ H64 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79))) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79)) _ H65)))
    | (K_Abs K92 K95 T112 jm42 H66 H67) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_Abs G10 K92 K95 T112 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Kinding (etvar G9 K92) T112 (weakenKind K95 (HS ty H0)) jm42 c (etvar G10 K92) (weaken_shift_evar (etvar empty K92) H79))) (shift_wfKind _ _ H66 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79))) (shift_wfKind _ _ H67 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79)))))
    | (K_App K93 K94 T111 T112 jm43 jm44) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_App G10 K93 K94 T111 T112 (shift_evar_Kinding G9 T111 (karr K93 K94) jm43 c G10 (weaken_shift_evar empty H79)) (shift_evar_Kinding G9 T112 K93 jm44 c G10 (weaken_shift_evar empty H79))))
    | (K_Arr T111 T112 jm45 jm46) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_Arr G10 T111 T112 (shift_evar_Kinding G9 T111 (star) jm45 c G10 (weaken_shift_evar empty H79)) (shift_evar_Kinding G9 T112 (star) jm46 c G10 (weaken_shift_evar empty H79))))
    | (K_All K92 T112 jm47 H75) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_All G10 K92 T112 (shift_evar_Kinding (etvar G9 K92) T112 (star) jm47 c (etvar G10 K92) (weaken_shift_evar (etvar empty K92) H79)) (shift_wfKind _ _ H75 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79)))))
  end.
Fixpoint shift_etvar_Kinding (G9 : Env) (T113 : Ty) (K96 : Kind) (jm48 : (Kinding G9 T113 K96)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) ,
  (Kinding G10 (tshiftTy c T113) K96)) :=
  match jm48 in (Kinding _ T113 K96) return (forall (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) ,
    (Kinding G10 (tshiftTy c T113) K96)) with
    | (K_TVar K91 X51 lk1 H64 H65) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_TVar G10 K91 (tshiftIndex c X51) (shift_etvar_lookup_etvar H79 lk1) (tshift_wfKind _ _ H64 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79))) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79)) _ H65)))
    | (K_Abs K92 K95 T112 jm42 H66 H67) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_Abs G10 K92 K95 (tshiftTy (CS c) T112) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_Kinding (etvar G9 K92) T112 (weakenKind K95 (HS ty H0)) jm42 (CS c) (etvar G10 K92) (weaken_shift_etvar (etvar empty K92) H79))) (tshift_wfKind _ _ H66 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79))) (tshift_wfKind _ _ H67 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79)))))
    | (K_App K93 K94 T111 T112 jm43 jm44) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_App G10 K93 K94 (tshiftTy c T111) (tshiftTy c T112) (shift_etvar_Kinding G9 T111 (karr K93 K94) jm43 c G10 (weaken_shift_etvar empty H79)) (shift_etvar_Kinding G9 T112 K93 jm44 c G10 (weaken_shift_etvar empty H79))))
    | (K_Arr T111 T112 jm45 jm46) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_Arr G10 (tshiftTy c T111) (tshiftTy c T112) (shift_etvar_Kinding G9 T111 (star) jm45 c G10 (weaken_shift_etvar empty H79)) (shift_etvar_Kinding G9 T112 (star) jm46 c G10 (weaken_shift_etvar empty H79))))
    | (K_All K92 T112 jm47 H75) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_All G10 K92 (tshiftTy (CS c) T112) (shift_etvar_Kinding (etvar G9 K92) T112 (star) jm47 (CS c) (etvar G10 K92) (weaken_shift_etvar (etvar empty K92) H79)) (tshift_wfKind _ _ H75 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79)))))
  end.
Fixpoint shift_evar_TRedStar (G9 : Env) (T112 : Ty) (T113 : Ty) (K92 : Kind) (jm45 : (TRedStar G9 T112 T113 K92)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) ,
  (TRedStar G10 T112 T113 K92)) :=
  match jm45 in (TRedStar _ T112 T113 K92) return (forall (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) ,
    (TRedStar G10 T112 T113 K92)) with
    | (QRS_Nil K91 T111 jm42) => (fun (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) =>
      (QRS_Nil G10 K91 T111 (shift_evar_Kinding G9 T111 K91 jm42 c G10 (weaken_shift_evar empty H73))))
    | (QRS_Cons K91 S37 T111 U5 jm43 jm44) => (fun (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) =>
      (QRS_Cons G10 K91 S37 T111 U5 (shift_evar_TRedStar G9 S37 T111 K91 jm43 c G10 (weaken_shift_evar empty H73)) (shift_evar_TRed G9 T111 U5 K91 jm44 c G10 (weaken_shift_evar empty H73))))
  end.
Fixpoint shift_etvar_TRedStar (G9 : Env) (T112 : Ty) (T113 : Ty) (K92 : Kind) (jm45 : (TRedStar G9 T112 T113 K92)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) ,
  (TRedStar G10 (tshiftTy c T112) (tshiftTy c T113) K92)) :=
  match jm45 in (TRedStar _ T112 T113 K92) return (forall (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) ,
    (TRedStar G10 (tshiftTy c T112) (tshiftTy c T113) K92)) with
    | (QRS_Nil K91 T111 jm42) => (fun (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) =>
      (QRS_Nil G10 K91 (tshiftTy c T111) (shift_etvar_Kinding G9 T111 K91 jm42 c G10 (weaken_shift_etvar empty H73))))
    | (QRS_Cons K91 S37 T111 U5 jm43 jm44) => (fun (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) =>
      (QRS_Cons G10 K91 (tshiftTy c S37) (tshiftTy c T111) (tshiftTy c U5) (shift_etvar_TRedStar G9 S37 T111 K91 jm43 c G10 (weaken_shift_etvar empty H73)) (shift_etvar_TRed G9 T111 U5 K91 jm44 c G10 (weaken_shift_etvar empty H73))))
  end.
Fixpoint shift_evar_TyEq (G9 : Env) (T115 : Ty) (T116 : Ty) (K96 : Kind) (jm54 : (TyEq G9 T115 T116 K96)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) ,
  (TyEq G10 T115 T116 K96)) :=
  match jm54 in (TyEq _ T115 T116 K96) return (forall (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) ,
    (TyEq G10 T115 T116 K96)) with
    | (Q_Arrow S37 S38 T112 T114 jm42 jm43) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_Arrow G10 S37 S38 T112 T114 (shift_evar_TyEq G9 S37 T112 (star) jm42 c G10 (weaken_shift_evar empty H97)) (shift_evar_TyEq G9 S38 T114 (star) jm43 c G10 (weaken_shift_evar empty H97))))
    | (Q_Abs K92 K95 S38 T114 jm44 H68 H69) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_Abs G10 K92 K95 S38 T114 (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TyEq (etvar G9 K92) S38 T114 (weakenKind K95 (HS ty H0)) jm44 c (etvar G10 K92) (weaken_shift_evar (etvar empty K92) H97))) (shift_wfKind _ _ H68 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H97))) (shift_wfKind _ _ H69 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H97)))))
    | (Q_App K92 K95 S37 S38 T112 T114 jm45 jm46) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_App G10 K92 K95 S37 S38 T112 T114 (shift_evar_TyEq G9 S37 T112 (karr K92 K95) jm45 c G10 (weaken_shift_evar empty H97)) (shift_evar_TyEq G9 S38 T114 K92 jm46 c G10 (weaken_shift_evar empty H97))))
    | (Q_All K92 S38 T114 jm47 H78) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_All G10 K92 S38 T114 (shift_evar_TyEq (etvar G9 K92) S38 T114 (star) jm47 c (etvar G10 K92) (weaken_shift_evar (etvar empty K92) H97)) (shift_wfKind _ _ H78 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H97)))))
    | (Q_Beta K93 K94 T113 T114 jm48 jm49 H82) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_Beta G10 K93 K94 T113 T114 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Kinding (etvar G9 K93) T113 (weakenKind K94 (HS ty H0)) jm48 c (etvar G10 K93) (weaken_shift_evar (etvar empty K93) H97))) (shift_evar_Kinding G9 T114 K93 jm49 c G10 (weaken_shift_evar empty H97)) (shift_wfKind _ _ H82 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H97)))))
    | (Q_Refl K91 T111 jm50) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_Refl G10 K91 T111 (shift_evar_Kinding G9 T111 K91 jm50 c G10 (weaken_shift_evar empty H97))))
    | (Q_Symm K91 T111 U5 jm51) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_Symm G10 K91 T111 U5 (shift_evar_TyEq G9 T111 U5 K91 jm51 c G10 (weaken_shift_evar empty H97))))
    | (Q_Trans K91 T111 U5 V1 jm52 jm53) => (fun (c : (Cutoff tm)) (G10 : Env) (H97 : (shift_evar c G9 G10)) =>
      (Q_Trans G10 K91 T111 U5 V1 (shift_evar_TyEq G9 T111 U5 K91 jm52 c G10 (weaken_shift_evar empty H97)) (shift_evar_TyEq G9 U5 V1 K91 jm53 c G10 (weaken_shift_evar empty H97))))
  end.
Fixpoint shift_etvar_TyEq (G9 : Env) (T115 : Ty) (T116 : Ty) (K96 : Kind) (jm54 : (TyEq G9 T115 T116 K96)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) ,
  (TyEq G10 (tshiftTy c T115) (tshiftTy c T116) K96)) :=
  match jm54 in (TyEq _ T115 T116 K96) return (forall (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) ,
    (TyEq G10 (tshiftTy c T115) (tshiftTy c T116) K96)) with
    | (Q_Arrow S37 S38 T112 T114 jm42 jm43) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (Q_Arrow G10 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T112) (tshiftTy c T114) (shift_etvar_TyEq G9 S37 T112 (star) jm42 c G10 (weaken_shift_etvar empty H97)) (shift_etvar_TyEq G9 S38 T114 (star) jm43 c G10 (weaken_shift_etvar empty H97))))
    | (Q_Abs K92 K95 S38 T114 jm44 H68 H69) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (Q_Abs G10 K92 K95 (tshiftTy (CS c) S38) (tshiftTy (CS c) T114) (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TyEq (etvar G9 K92) S38 T114 (weakenKind K95 (HS ty H0)) jm44 (CS c) (etvar G10 K92) (weaken_shift_etvar (etvar empty K92) H97))) (tshift_wfKind _ _ H68 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H97))) (tshift_wfKind _ _ H69 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H97)))))
    | (Q_App K92 K95 S37 S38 T112 T114 jm45 jm46) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (Q_App G10 K92 K95 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T112) (tshiftTy c T114) (shift_etvar_TyEq G9 S37 T112 (karr K92 K95) jm45 c G10 (weaken_shift_etvar empty H97)) (shift_etvar_TyEq G9 S38 T114 K92 jm46 c G10 (weaken_shift_etvar empty H97))))
    | (Q_All K92 S38 T114 jm47 H78) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (Q_All G10 K92 (tshiftTy (CS c) S38) (tshiftTy (CS c) T114) (shift_etvar_TyEq (etvar G9 K92) S38 T114 (star) jm47 (CS c) (etvar G10 K92) (weaken_shift_etvar (etvar empty K92) H97)) (tshift_wfKind _ _ H78 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H97)))))
    | (Q_Beta K93 K94 T113 T114 jm48 jm49 H82) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (TyEq_cast G10 _ _ _ G10 (tshiftTy c (tapp (tabs K93 T113) T114)) (tshiftTy c (tsubstTy X0 T114 T113)) K94 eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T113 c T114)) eq_refl (Q_Beta G10 K93 K94 (tshiftTy (CS c) T113) (tshiftTy c T114) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_Kinding (etvar G9 K93) T113 (weakenKind K94 (HS ty H0)) jm48 (CS c) (etvar G10 K93) (weaken_shift_etvar (etvar empty K93) H97))) (shift_etvar_Kinding G9 T114 K93 jm49 c G10 (weaken_shift_etvar empty H97)) (tshift_wfKind _ _ H82 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H97))))))
    | (Q_Refl K91 T111 jm50) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (Q_Refl G10 K91 (tshiftTy c T111) (shift_etvar_Kinding G9 T111 K91 jm50 c G10 (weaken_shift_etvar empty H97))))
    | (Q_Symm K91 T111 U5 jm51) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (Q_Symm G10 K91 (tshiftTy c T111) (tshiftTy c U5) (shift_etvar_TyEq G9 T111 U5 K91 jm51 c G10 (weaken_shift_etvar empty H97))))
    | (Q_Trans K91 T111 U5 V1 jm52 jm53) => (fun (c : (Cutoff ty)) (G10 : Env) (H97 : (shift_etvar c G9 G10)) =>
      (Q_Trans G10 K91 (tshiftTy c T111) (tshiftTy c U5) (tshiftTy c V1) (shift_etvar_TyEq G9 T111 U5 K91 jm52 c G10 (weaken_shift_etvar empty H97)) (shift_etvar_TyEq G9 U5 V1 K91 jm53 c G10 (weaken_shift_etvar empty H97))))
  end.
Fixpoint shift_evar_Typing (G9 : Env) (t21 : Tm) (T116 : Ty) (jm51 : (Typing G9 t21 T116)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) ,
  (Typing G10 (shiftTm c t21) T116)) :=
  match jm51 in (Typing _ t21 T116) return (forall (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) ,
    (Typing G10 (shiftTm c t21) T116)) with
    | (T_Var T111 y1 lk1 H64 H65) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_Var G10 T111 (shiftIndex c y1) (shift_evar_lookup_evar H85 lk1) (shift_wfTy _ _ H64 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)) _ H65)))
    | (T_Abs T112 T115 t18 jm46 jm47 H67) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_Abs G10 T112 T115 (shiftTm (CS c) t18) (shift_evar_Kinding G9 T112 (star) jm46 c G10 (weaken_shift_evar empty H85)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G9 T112) t18 (weakenTy T115 (HS tm H0)) jm47 (CS c) (evar G10 T112) (weaken_shift_evar (evar empty T112) H85))) (shift_wfTy _ _ H67 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)))))
    | (T_App T113 T114 t19 t20 jm48 jm49) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_App G10 T113 T114 (shiftTm c t19) (shiftTm c t20) (shift_evar_Typing G9 t19 (tarr T113 T114) jm48 c G10 (weaken_shift_evar empty H85)) (shift_evar_Typing G9 t20 T113 jm49 c G10 (weaken_shift_evar empty H85))))
    | (T_TAbs K91 T111 t18 jm50 H73) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_TAbs G10 K91 T111 (shiftTm c t18) (shift_evar_Typing (etvar G9 K91) t18 T111 jm50 c (etvar G10 K91) (weaken_shift_evar (etvar empty K91) H85)) (shift_wfKind _ _ H73 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)))))
    | (T_TApp K92 T114 T115 t19 jm42 jm43) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_TApp G10 K92 T114 T115 (shiftTm c t19) (shift_evar_Typing G9 t19 (tall K92 T114) jm42 c G10 (weaken_shift_evar empty H85)) (shift_evar_Kinding G9 T115 K92 jm43 c G10 (weaken_shift_evar empty H85))))
    | (T_Eq S37 T111 t18 jm44 jm45) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_Eq G10 S37 T111 (shiftTm c t18) (shift_evar_Typing G9 t18 S37 jm44 c G10 (weaken_shift_evar empty H85)) (shift_evar_TyEq G9 S37 T111 (star) jm45 c G10 (weaken_shift_evar empty H85))))
  end.
Fixpoint shift_etvar_Typing (G9 : Env) (t21 : Tm) (T116 : Ty) (jm51 : (Typing G9 t21 T116)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) ,
  (Typing G10 (tshiftTm c t21) (tshiftTy c T116))) :=
  match jm51 in (Typing _ t21 T116) return (forall (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) ,
    (Typing G10 (tshiftTm c t21) (tshiftTy c T116))) with
    | (T_Var T111 y1 lk1 H64 H65) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_Var G10 (tshiftTy c T111) y1 (shift_etvar_lookup_evar H85 lk1) (tshift_wfTy _ _ H64 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85)) _ H65)))
    | (T_Abs T112 T115 t18 jm46 jm47 H67) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_Abs G10 (tshiftTy c T112) (tshiftTy c T115) (tshiftTm c t18) (shift_etvar_Kinding G9 T112 (star) jm46 c G10 (weaken_shift_etvar empty H85)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c T115)) (shift_etvar_Typing (evar G9 T112) t18 (weakenTy T115 (HS tm H0)) jm47 c (evar G10 (tshiftTy c T112)) (weaken_shift_etvar (evar empty T112) H85))) (tshift_wfTy _ _ H67 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85)))))
    | (T_App T113 T114 t19 t20 jm48 jm49) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_App G10 (tshiftTy c T113) (tshiftTy c T114) (tshiftTm c t19) (tshiftTm c t20) (shift_etvar_Typing G9 t19 (tarr T113 T114) jm48 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_Typing G9 t20 T113 jm49 c G10 (weaken_shift_etvar empty H85))))
    | (T_TAbs K91 T111 t18 jm50 H73) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_TAbs G10 K91 (tshiftTy (CS c) T111) (tshiftTm (CS c) t18) (shift_etvar_Typing (etvar G9 K91) t18 T111 jm50 (CS c) (etvar G10 K91) (weaken_shift_etvar (etvar empty K91) H85)) (tshift_wfKind _ _ H73 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85)))))
    | (T_TApp K92 T114 T115 t19 jm42 jm43) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Typing_cast G10 _ _ G10 (tshiftTm c (tyapp t19 T115)) (tshiftTy c (tsubstTy X0 T115 T114)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T114 c T115)) (T_TApp G10 K92 (tshiftTy (CS c) T114) (tshiftTy c T115) (tshiftTm c t19) (shift_etvar_Typing G9 t19 (tall K92 T114) jm42 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_Kinding G9 T115 K92 jm43 c G10 (weaken_shift_etvar empty H85)))))
    | (T_Eq S37 T111 t18 jm44 jm45) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_Eq G10 (tshiftTy c S37) (tshiftTy c T111) (tshiftTm c t18) (shift_etvar_Typing G9 t18 S37 jm44 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_TyEq G9 S37 T111 (star) jm45 c G10 (weaken_shift_etvar empty H85))))
  end.
 Hint Resolve shift_evar_Kinding shift_etvar_Kinding shift_evar_TRed shift_etvar_TRed shift_evar_TRedStar shift_etvar_TRedStar shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_Kinding shift_etvar_Kinding shift_evar_TRed shift_etvar_TRed shift_evar_TRedStar shift_etvar_TRedStar shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_TRed (G : Env) :
(forall (G0 : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (jm37 : (TRed G0 T98 T99 K82)) ,
  (TRed (appendEnv G0 G) (weakenTy T98 (domainEnv G)) (weakenTy T99 (domainEnv G)) (weakenKind K82 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (jm37 : (TRed G0 T98 T99 K82)) ,
    (TRed (appendEnv G0 G) (weakenTy T98 (domainEnv G)) (weakenTy T99 (domainEnv G)) (weakenKind K82 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (jm37 : (TRed G0 T98 T99 K82)) =>
      jm37)
    | (evar G T100) => (fun (G0 : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (jm37 : (TRed G0 T98 T99 K82)) =>
      (shift_evar_TRed (appendEnv G0 G) (weakenTy T98 (domainEnv G)) (weakenTy T99 (domainEnv G)) (weakenKind K82 (domainEnv G)) (weaken_TRed G G0 T98 T99 K82 jm37) C0 (evar (appendEnv G0 G) T100) shift_evar_here))
    | (etvar G K83) => (fun (G0 : Env) (T98 : Ty) (T99 : Ty) (K82 : Kind) (jm37 : (TRed G0 T98 T99 K82)) =>
      (shift_etvar_TRed (appendEnv G0 G) (weakenTy T98 (domainEnv G)) (weakenTy T99 (domainEnv G)) (weakenKind K82 (domainEnv G)) (weaken_TRed G G0 T98 T99 K82 jm37) C0 (etvar (appendEnv G0 G) K83) shift_etvar_here))
  end.
Fixpoint weaken_Kinding (G1 : Env) :
(forall (G2 : Env) (T101 : Ty) (K84 : Kind) (jm38 : (Kinding G2 T101 K84)) ,
  (Kinding (appendEnv G2 G1) (weakenTy T101 (domainEnv G1)) (weakenKind K84 (domainEnv G1)))) :=
  match G1 return (forall (G2 : Env) (T101 : Ty) (K84 : Kind) (jm38 : (Kinding G2 T101 K84)) ,
    (Kinding (appendEnv G2 G1) (weakenTy T101 (domainEnv G1)) (weakenKind K84 (domainEnv G1)))) with
    | (empty) => (fun (G2 : Env) (T101 : Ty) (K84 : Kind) (jm38 : (Kinding G2 T101 K84)) =>
      jm38)
    | (evar G1 T102) => (fun (G2 : Env) (T101 : Ty) (K84 : Kind) (jm38 : (Kinding G2 T101 K84)) =>
      (shift_evar_Kinding (appendEnv G2 G1) (weakenTy T101 (domainEnv G1)) (weakenKind K84 (domainEnv G1)) (weaken_Kinding G1 G2 T101 K84 jm38) C0 (evar (appendEnv G2 G1) T102) shift_evar_here))
    | (etvar G1 K85) => (fun (G2 : Env) (T101 : Ty) (K84 : Kind) (jm38 : (Kinding G2 T101 K84)) =>
      (shift_etvar_Kinding (appendEnv G2 G1) (weakenTy T101 (domainEnv G1)) (weakenKind K84 (domainEnv G1)) (weaken_Kinding G1 G2 T101 K84 jm38) C0 (etvar (appendEnv G2 G1) K85) shift_etvar_here))
  end.
Fixpoint weaken_TRedStar (G3 : Env) :
(forall (G4 : Env) (T103 : Ty) (T104 : Ty) (K86 : Kind) (jm39 : (TRedStar G4 T103 T104 K86)) ,
  (TRedStar (appendEnv G4 G3) (weakenTy T103 (domainEnv G3)) (weakenTy T104 (domainEnv G3)) (weakenKind K86 (domainEnv G3)))) :=
  match G3 return (forall (G4 : Env) (T103 : Ty) (T104 : Ty) (K86 : Kind) (jm39 : (TRedStar G4 T103 T104 K86)) ,
    (TRedStar (appendEnv G4 G3) (weakenTy T103 (domainEnv G3)) (weakenTy T104 (domainEnv G3)) (weakenKind K86 (domainEnv G3)))) with
    | (empty) => (fun (G4 : Env) (T103 : Ty) (T104 : Ty) (K86 : Kind) (jm39 : (TRedStar G4 T103 T104 K86)) =>
      jm39)
    | (evar G3 T105) => (fun (G4 : Env) (T103 : Ty) (T104 : Ty) (K86 : Kind) (jm39 : (TRedStar G4 T103 T104 K86)) =>
      (shift_evar_TRedStar (appendEnv G4 G3) (weakenTy T103 (domainEnv G3)) (weakenTy T104 (domainEnv G3)) (weakenKind K86 (domainEnv G3)) (weaken_TRedStar G3 G4 T103 T104 K86 jm39) C0 (evar (appendEnv G4 G3) T105) shift_evar_here))
    | (etvar G3 K87) => (fun (G4 : Env) (T103 : Ty) (T104 : Ty) (K86 : Kind) (jm39 : (TRedStar G4 T103 T104 K86)) =>
      (shift_etvar_TRedStar (appendEnv G4 G3) (weakenTy T103 (domainEnv G3)) (weakenTy T104 (domainEnv G3)) (weakenKind K86 (domainEnv G3)) (weaken_TRedStar G3 G4 T103 T104 K86 jm39) C0 (etvar (appendEnv G4 G3) K87) shift_etvar_here))
  end.
Fixpoint weaken_TyEq (G5 : Env) :
(forall (G6 : Env) (T106 : Ty) (T107 : Ty) (K88 : Kind) (jm40 : (TyEq G6 T106 T107 K88)) ,
  (TyEq (appendEnv G6 G5) (weakenTy T106 (domainEnv G5)) (weakenTy T107 (domainEnv G5)) (weakenKind K88 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (T106 : Ty) (T107 : Ty) (K88 : Kind) (jm40 : (TyEq G6 T106 T107 K88)) ,
    (TyEq (appendEnv G6 G5) (weakenTy T106 (domainEnv G5)) (weakenTy T107 (domainEnv G5)) (weakenKind K88 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (T106 : Ty) (T107 : Ty) (K88 : Kind) (jm40 : (TyEq G6 T106 T107 K88)) =>
      jm40)
    | (evar G5 T108) => (fun (G6 : Env) (T106 : Ty) (T107 : Ty) (K88 : Kind) (jm40 : (TyEq G6 T106 T107 K88)) =>
      (shift_evar_TyEq (appendEnv G6 G5) (weakenTy T106 (domainEnv G5)) (weakenTy T107 (domainEnv G5)) (weakenKind K88 (domainEnv G5)) (weaken_TyEq G5 G6 T106 T107 K88 jm40) C0 (evar (appendEnv G6 G5) T108) shift_evar_here))
    | (etvar G5 K89) => (fun (G6 : Env) (T106 : Ty) (T107 : Ty) (K88 : Kind) (jm40 : (TyEq G6 T106 T107 K88)) =>
      (shift_etvar_TyEq (appendEnv G6 G5) (weakenTy T106 (domainEnv G5)) (weakenTy T107 (domainEnv G5)) (weakenKind K88 (domainEnv G5)) (weaken_TyEq G5 G6 T106 T107 K88 jm40) C0 (etvar (appendEnv G6 G5) K89) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G7 : Env) :
(forall (G8 : Env) (t17 : Tm) (T109 : Ty) (jm41 : (Typing G8 t17 T109)) ,
  (Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T109 (domainEnv G7)))) :=
  match G7 return (forall (G8 : Env) (t17 : Tm) (T109 : Ty) (jm41 : (Typing G8 t17 T109)) ,
    (Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T109 (domainEnv G7)))) with
    | (empty) => (fun (G8 : Env) (t17 : Tm) (T109 : Ty) (jm41 : (Typing G8 t17 T109)) =>
      jm41)
    | (evar G7 T110) => (fun (G8 : Env) (t17 : Tm) (T109 : Ty) (jm41 : (Typing G8 t17 T109)) =>
      (shift_evar_Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T109 (domainEnv G7)) (weaken_Typing G7 G8 t17 T109 jm41) C0 (evar (appendEnv G8 G7) T110) shift_evar_here))
    | (etvar G7 K90) => (fun (G8 : Env) (t17 : Tm) (T109 : Ty) (jm41 : (Typing G8 t17 T109)) =>
      (shift_etvar_Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T109 (domainEnv G7)) (weaken_Typing G7 G8 t17 T109 jm41) C0 (etvar (appendEnv G8 G7) K90) shift_etvar_here))
  end.
Fixpoint TRed_wf_0 (G : Env) (T111 : Ty) (T112 : Ty) (K91 : Kind) (jm42 : (TRed G T111 T112 K91)) {struct jm42} :
(wfTy (domainEnv G) T111) :=
  match jm42 in (TRed _ T111 T112 K91) return (wfTy (domainEnv G) T111) with
    | (QR_Var K X lk H26 H27) => (wfTy_tvar (domainEnv G) _ H27)
    | (QR_Arrow S1 S2 T1 T2 jm26 jm27) => (wfTy_tarr (domainEnv G) (TRed_wf_0 G S1 T1 (star) jm26) (TRed_wf_0 G S2 T2 (star) jm27))
    | (QR_Abs K1 K2 S2 T2 jm28 H32 H33) => (wfTy_tabs (domainEnv G) H32 (TRed_wf_0 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm28))
    | (QR_App K1 K2 S1 S2 T1 T2 jm29 jm30) => (wfTy_tapp (domainEnv G) (TRed_wf_0 G S1 T1 (karr K2 K1) jm29) (TRed_wf_0 G S2 T2 K2 jm30))
    | (QR_All K1 S2 T2 jm31 H42) => (wfTy_tall (domainEnv G) H42 (TRed_wf_0 (etvar G K1) S2 T2 (star) jm31))
    | (QR_Beta K1 K2 S1 S2 T1 T2 jm32 jm33 H45) => (wfTy_tapp (domainEnv G) (wfTy_tabs (domainEnv G) (TRed_wf_2 G S2 T2 K2 jm33) (TRed_wf_0 (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0)) jm32)) (TRed_wf_0 G S2 T2 K2 jm33))
  end
with TRed_wf_1 (G : Env) (T111 : Ty) (T112 : Ty) (K91 : Kind) (jm43 : (TRed G T111 T112 K91)) {struct jm43} :
(wfTy (domainEnv G) T112) :=
  match jm43 in (TRed _ T111 T112 K91) return (wfTy (domainEnv G) T112) with
    | (QR_Var K X lk H26 H27) => (wfTy_tvar (domainEnv G) _ H27)
    | (QR_Arrow S1 S2 T1 T2 jm26 jm27) => (wfTy_tarr (domainEnv G) (TRed_wf_1 G S1 T1 (star) jm26) (TRed_wf_1 G S2 T2 (star) jm27))
    | (QR_Abs K1 K2 S2 T2 jm28 H32 H33) => (wfTy_tabs (domainEnv G) H32 (TRed_wf_1 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm28))
    | (QR_App K1 K2 S1 S2 T1 T2 jm29 jm30) => (wfTy_tapp (domainEnv G) (TRed_wf_1 G S1 T1 (karr K2 K1) jm29) (TRed_wf_1 G S2 T2 K2 jm30))
    | (QR_All K1 S2 T2 jm31 H42) => (wfTy_tall (domainEnv G) H42 (TRed_wf_1 (etvar G K1) S2 T2 (star) jm31))
    | (QR_Beta K1 K2 S1 S2 T1 T2 jm32 jm33 H45) => (substhvl_ty_wfTy (TRed_wf_1 G S2 T2 K2 jm33) (HS ty (domainEnv G)) T1 (TRed_wf_1 (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0)) jm32) (substhvl_ty_here (domainEnv G)))
  end
with TRed_wf_2 (G : Env) (T111 : Ty) (T112 : Ty) (K91 : Kind) (jm44 : (TRed G T111 T112 K91)) {struct jm44} :
(wfKind (domainEnv G) K91) :=
  match jm44 in (TRed _ T111 T112 K91) return (wfKind (domainEnv G) K91) with
    | (QR_Var K X lk H26 H27) => H26
    | (QR_Arrow S1 S2 T1 T2 jm26 jm27) => (wfKind_star (domainEnv G))
    | (QR_Abs K1 K2 S2 T2 jm28 H32 H33) => (wfKind_karr (domainEnv G) H32 H33)
    | (QR_App K1 K2 S1 S2 T1 T2 jm29 jm30) => (inversion_wfKind_karr_1 (domainEnv G) K2 K1 (TRed_wf_2 G S1 T1 (karr K2 K1) jm29))
    | (QR_All K1 S2 T2 jm31 H42) => (wfKind_star (domainEnv G))
    | (QR_Beta K1 K2 S1 S2 T1 T2 jm32 jm33 H45) => H45
  end.
Fixpoint Kinding_wf_0 (G : Env) (T113 : Ty) (K92 : Kind) (jm45 : (Kinding G T113 K92)) {struct jm45} :
(wfTy (domainEnv G) T113) :=
  match jm45 in (Kinding _ T113 K92) return (wfTy (domainEnv G) T113) with
    | (K_TVar K X lk1 H25 H26) => (wfTy_tvar (domainEnv G) _ H26)
    | (K_Abs K1 K2 T2 jm H27 H28) => (wfTy_tabs (domainEnv G) H27 (Kinding_wf_0 (etvar G K1) T2 (weakenKind K2 (HS ty H0)) jm))
    | (K_App K11 K12 T1 T2 jm0 jm1) => (wfTy_tapp (domainEnv G) (Kinding_wf_0 G T1 (karr K11 K12) jm0) (Kinding_wf_0 G T2 K11 jm1))
    | (K_Arr T1 T2 jm2 jm3) => (wfTy_tarr (domainEnv G) (Kinding_wf_0 G T1 (star) jm2) (Kinding_wf_0 G T2 (star) jm3))
    | (K_All K1 T2 jm4 H36) => (wfTy_tall (domainEnv G) H36 (Kinding_wf_0 (etvar G K1) T2 (star) jm4))
  end
with Kinding_wf_1 (G : Env) (T113 : Ty) (K92 : Kind) (jm46 : (Kinding G T113 K92)) {struct jm46} :
(wfKind (domainEnv G) K92) :=
  match jm46 in (Kinding _ T113 K92) return (wfKind (domainEnv G) K92) with
    | (K_TVar K X lk2 H25 H26) => H25
    | (K_Abs K1 K2 T2 jm H27 H28) => (wfKind_karr (domainEnv G) H27 H28)
    | (K_App K11 K12 T1 T2 jm0 jm1) => (inversion_wfKind_karr_1 (domainEnv G) K11 K12 (Kinding_wf_1 G T1 (karr K11 K12) jm0))
    | (K_Arr T1 T2 jm2 jm3) => (wfKind_star (domainEnv G))
    | (K_All K1 T2 jm4 H36) => (wfKind_star (domainEnv G))
  end.
Fixpoint TRedStar_wf_0 (G : Env) (T114 : Ty) (T115 : Ty) (K93 : Kind) (jm47 : (TRedStar G T114 T115 K93)) {struct jm47} :
(wfTy (domainEnv G) T114) :=
  match jm47 in (TRedStar _ T114 T115 K93) return (wfTy (domainEnv G) T114) with
    | (QRS_Nil K T jm34) => (Kinding_wf_0 G T K jm34)
    | (QRS_Cons K S1 T U jm35 jm36) => (TRedStar_wf_0 G S1 T K jm35)
  end
with TRedStar_wf_1 (G : Env) (T114 : Ty) (T115 : Ty) (K93 : Kind) (jm48 : (TRedStar G T114 T115 K93)) {struct jm48} :
(wfTy (domainEnv G) T115) :=
  match jm48 in (TRedStar _ T114 T115 K93) return (wfTy (domainEnv G) T115) with
    | (QRS_Nil K T jm34) => (Kinding_wf_0 G T K jm34)
    | (QRS_Cons K S1 T U jm35 jm36) => (TRed_wf_1 G T U K jm36)
  end
with TRedStar_wf_2 (G : Env) (T114 : Ty) (T115 : Ty) (K93 : Kind) (jm49 : (TRedStar G T114 T115 K93)) {struct jm49} :
(wfKind (domainEnv G) K93) :=
  match jm49 in (TRedStar _ T114 T115 K93) return (wfKind (domainEnv G) K93) with
    | (QRS_Nil K T jm34) => (Kinding_wf_1 G T K jm34)
    | (QRS_Cons K S1 T U jm35 jm36) => (TRed_wf_2 G T U K jm36)
  end.
Fixpoint TyEq_wf_0 (G : Env) (T116 : Ty) (T117 : Ty) (K94 : Kind) (jm50 : (TyEq G T116 T117 K94)) {struct jm50} :
(wfTy (domainEnv G) T116) :=
  match jm50 in (TyEq _ T116 T117 K94) return (wfTy (domainEnv G) T116) with
    | (Q_Arrow S1 S2 T1 T2 jm14 jm15) => (wfTy_tarr (domainEnv G) (TyEq_wf_0 G S1 T1 (star) jm14) (TyEq_wf_0 G S2 T2 (star) jm15))
    | (Q_Abs K1 K2 S2 T2 jm16 H30 H31) => (wfTy_tabs (domainEnv G) H30 (TyEq_wf_0 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm16))
    | (Q_App K1 K2 S1 S2 T1 T2 jm17 jm18) => (wfTy_tapp (domainEnv G) (TyEq_wf_0 G S1 T1 (karr K1 K2) jm17) (TyEq_wf_0 G S2 T2 K1 jm18))
    | (Q_All K1 S2 T2 jm19 H40) => (wfTy_tall (domainEnv G) H40 (TyEq_wf_0 (etvar G K1) S2 T2 (star) jm19))
    | (Q_Beta K11 K12 T12 T2 jm20 jm21 H44) => (wfTy_tapp (domainEnv G) (wfTy_tabs (domainEnv G) (Kinding_wf_1 G T2 K11 jm21) (Kinding_wf_0 (etvar G K11) T12 (weakenKind K12 (HS ty H0)) jm20)) (Kinding_wf_0 G T2 K11 jm21))
    | (Q_Refl K T jm22) => (Kinding_wf_0 G T K jm22)
    | (Q_Symm K T U jm23) => (TyEq_wf_1 G T U K jm23)
    | (Q_Trans K T U V jm24 jm25) => (TyEq_wf_0 G T U K jm24)
  end
with TyEq_wf_1 (G : Env) (T116 : Ty) (T117 : Ty) (K94 : Kind) (jm51 : (TyEq G T116 T117 K94)) {struct jm51} :
(wfTy (domainEnv G) T117) :=
  match jm51 in (TyEq _ T116 T117 K94) return (wfTy (domainEnv G) T117) with
    | (Q_Arrow S1 S2 T1 T2 jm14 jm15) => (wfTy_tarr (domainEnv G) (TyEq_wf_1 G S1 T1 (star) jm14) (TyEq_wf_1 G S2 T2 (star) jm15))
    | (Q_Abs K1 K2 S2 T2 jm16 H30 H31) => (wfTy_tabs (domainEnv G) H30 (TyEq_wf_1 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm16))
    | (Q_App K1 K2 S1 S2 T1 T2 jm17 jm18) => (wfTy_tapp (domainEnv G) (TyEq_wf_1 G S1 T1 (karr K1 K2) jm17) (TyEq_wf_1 G S2 T2 K1 jm18))
    | (Q_All K1 S2 T2 jm19 H40) => (wfTy_tall (domainEnv G) H40 (TyEq_wf_1 (etvar G K1) S2 T2 (star) jm19))
    | (Q_Beta K11 K12 T12 T2 jm20 jm21 H44) => (substhvl_ty_wfTy (Kinding_wf_0 G T2 K11 jm21) (HS ty (domainEnv G)) T12 (Kinding_wf_0 (etvar G K11) T12 (weakenKind K12 (HS ty H0)) jm20) (substhvl_ty_here (domainEnv G)))
    | (Q_Refl K T jm22) => (Kinding_wf_0 G T K jm22)
    | (Q_Symm K T U jm23) => (TyEq_wf_0 G T U K jm23)
    | (Q_Trans K T U V jm24 jm25) => (TyEq_wf_1 G U V K jm25)
  end
with TyEq_wf_2 (G : Env) (T116 : Ty) (T117 : Ty) (K94 : Kind) (jm52 : (TyEq G T116 T117 K94)) {struct jm52} :
(wfKind (domainEnv G) K94) :=
  match jm52 in (TyEq _ T116 T117 K94) return (wfKind (domainEnv G) K94) with
    | (Q_Arrow S1 S2 T1 T2 jm14 jm15) => (wfKind_star (domainEnv G))
    | (Q_Abs K1 K2 S2 T2 jm16 H30 H31) => (wfKind_karr (domainEnv G) H30 H31)
    | (Q_App K1 K2 S1 S2 T1 T2 jm17 jm18) => (inversion_wfKind_karr_1 (domainEnv G) K1 K2 (TyEq_wf_2 G S1 T1 (karr K1 K2) jm17))
    | (Q_All K1 S2 T2 jm19 H40) => (wfKind_star (domainEnv G))
    | (Q_Beta K11 K12 T12 T2 jm20 jm21 H44) => H44
    | (Q_Refl K T jm22) => (Kinding_wf_1 G T K jm22)
    | (Q_Symm K T U jm23) => (TyEq_wf_2 G T U K jm23)
    | (Q_Trans K T U V jm24 jm25) => (TyEq_wf_2 G U V K jm25)
  end.
Fixpoint Typing_wf_0 (G : Env) (t18 : Tm) (T118 : Ty) (jm53 : (Typing G t18 T118)) {struct jm53} :
(wfTm (domainEnv G) t18) :=
  match jm53 in (Typing _ t18 T118) return (wfTm (domainEnv G) t18) with
    | (T_Var T y lk3 H25 H26) => (wfTm_var (domainEnv G) _ H26)
    | (T_Abs T1 T2 t jm5 jm6 H28) => (wfTm_abs (domainEnv G) (Kinding_wf_0 G T1 (star) jm5) (Typing_wf_0 (evar G T1) t (weakenTy T2 (HS tm H0)) jm6))
    | (T_App T11 T12 t1 t2 jm7 jm8) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tarr T11 T12) jm7) (Typing_wf_0 G t2 T11 jm8))
    | (T_TAbs K T t jm9 H34) => (wfTm_tyabs (domainEnv G) H34 (Typing_wf_0 (etvar G K) t T jm9))
    | (T_TApp K11 T12 T2 t1 jm10 jm11) => (wfTm_tyapp (domainEnv G) (Typing_wf_0 G t1 (tall K11 T12) jm10) (Kinding_wf_0 G T2 K11 jm11))
    | (T_Eq S1 T t jm12 jm13) => (Typing_wf_0 G t S1 jm12)
  end
with Typing_wf_1 (G : Env) (t18 : Tm) (T118 : Ty) (jm54 : (Typing G t18 T118)) {struct jm54} :
(wfTy (domainEnv G) T118) :=
  match jm54 in (Typing _ t18 T118) return (wfTy (domainEnv G) T118) with
    | (T_Var T y lk4 H25 H26) => H25
    | (T_Abs T1 T2 t jm5 jm6 H28) => (wfTy_tarr (domainEnv G) (Kinding_wf_0 G T1 (star) jm5) H28)
    | (T_App T11 T12 t1 t2 jm7 jm8) => (inversion_wfTy_tarr_1 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tarr T11 T12) jm7))
    | (T_TAbs K T t jm9 H34) => (wfTy_tall (domainEnv G) H34 (Typing_wf_1 (etvar G K) t T jm9))
    | (T_TApp K11 T12 T2 t1 jm10 jm11) => (substhvl_ty_wfTy (Kinding_wf_0 G T2 K11 jm11) (HS ty (domainEnv G)) T12 (inversion_wfTy_tall_2 (domainEnv G) K11 T12 (Typing_wf_1 G t1 (tall K11 T12) jm10)) (substhvl_ty_here (domainEnv G)))
    | (T_Eq S1 T t jm12 jm13) => (TyEq_wf_1 G S1 T (star) jm13)
  end.
 Hint Extern 8 => match goal with
  | H77 : (TRed _ _ _ _) |- _ => pose proof ((TRed_wf_0 _ _ _ _ H77)); pose proof ((TRed_wf_1 _ _ _ _ H77)); pose proof ((TRed_wf_2 _ _ _ _ H77)); clear H77
end : wf.
 Hint Extern 8 => match goal with
  | H78 : (Kinding _ _ _) |- _ => pose proof ((Kinding_wf_0 _ _ _ H78)); pose proof ((Kinding_wf_1 _ _ _ H78)); clear H78
end : wf.
 Hint Extern 8 => match goal with
  | H79 : (TRedStar _ _ _ _) |- _ => pose proof ((TRedStar_wf_0 _ _ _ _ H79)); pose proof ((TRedStar_wf_1 _ _ _ _ H79)); pose proof ((TRedStar_wf_2 _ _ _ _ H79)); clear H79
end : wf.
 Hint Extern 8 => match goal with
  | H80 : (TyEq _ _ _ _) |- _ => pose proof ((TyEq_wf_0 _ _ _ _ H80)); pose proof ((TyEq_wf_1 _ _ _ _ H80)); pose proof ((TyEq_wf_2 _ _ _ _ H80)); clear H80
end : wf.
 Hint Extern 8 => match goal with
  | H81 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H81)); pose proof ((Typing_wf_1 _ _ _ H81)); clear H81
end : wf.
Lemma subst_evar_lookup_evar (G9 : Env) (s4 : Tm) (T119 : Ty) (jm55 : (Typing G9 s4 T119)) :
  (forall (d : (Trace tm)) (G10 : Env) (G12 : Env) (sub : (subst_evar G9 T119 s4 d G10 G12)) (x11 : (Index tm)) (T120 : Ty) ,
    (lookup_evar G10 x11 T120) -> (Typing G12 (substIndex d s4 x11) T120)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Lemma subst_etvar_lookup_etvar (G9 : Env) (S37 : Ty) (K95 : Kind) (jm55 : (Kinding G9 S37 K95)) :
  (forall (d : (Trace ty)) (G10 : Env) (G12 : Env) (sub : (subst_etvar G9 K95 S37 d G10 G12)) (X51 : (Index ty)) (K96 : Kind) ,
    (lookup_etvar G10 X51 K96) -> (Kinding G12 (tsubstIndex d S37 X51) K96)).
Proof.
  needleGenericSubstEnvLookupHom (K_TVar).
Qed.
Class Obligation_Env_reg_TRed : Prop := { Env_reg_QR_Var (G : Env) (K : Kind) (S37 : Ty) (jm55 : (Kinding G S37 K)) (H26 : (wfKind (domainEnv G) K)) (H82 : (wfTy (domainEnv G) S37)) : (TRed G (weakenTy S37 H0) (weakenTy S37 H0) K) }.
Context {obligation_Env_reg_TRed : Obligation_Env_reg_TRed} .
Fixpoint subst_evar_TRed (G10 : Env) (s4 : Tm) (T119 : Ty) (jm64 : (Typing G10 s4 T119)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm65 : (TRed G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) ,
  (TRed G11 T1 T2 K)) :=
  match jm65 in (TRed _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) ,
    (TRed G11 T1 T2 K)) with
    | (QR_Var K95 X51 lk5 H84 H85) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) =>
      (QR_Var G11 K95 X51 (subst_evar_lookup_etvar T119 H109 K95 lk5) (substhvl_tm_wfKind _ _ H84 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109))) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)) H85)))
    | (QR_Arrow S38 S39 T120 T121 jm56 jm57) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) =>
      (QR_Arrow G11 S38 S39 T120 T121 (subst_evar_TRed G10 s4 T119 jm64 G9 S38 T120 (star) jm56 G11 d (weaken_subst_evar _ empty H109)) (subst_evar_TRed G10 s4 T119 jm64 G9 S39 T121 (star) jm57 G11 d (weaken_subst_evar _ empty H109))))
    | (QR_Abs K96 K97 S39 T121 jm58 H90 H91) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) =>
      (QR_Abs G11 K96 K97 S39 T121 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TRed G10 s4 T119 jm64 (etvar G9 K96) S39 T121 (weakenKind K97 (HS ty H0)) jm58 (appendEnv G11 (etvar empty K96)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K96) H109))) (substhvl_tm_wfKind _ _ H90 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109))) (substhvl_tm_wfKind _ _ H91 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)))))
    | (QR_App K96 K97 S38 S39 T120 T121 jm59 jm60) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) =>
      (QR_App G11 K96 K97 S38 S39 T120 T121 (subst_evar_TRed G10 s4 T119 jm64 G9 S38 T120 (karr K97 K96) jm59 G11 d (weaken_subst_evar _ empty H109)) (subst_evar_TRed G10 s4 T119 jm64 G9 S39 T121 K97 jm60 G11 d (weaken_subst_evar _ empty H109))))
    | (QR_All K96 S39 T121 jm61 H100) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) =>
      (QR_All G11 K96 S39 T121 (subst_evar_TRed G10 s4 T119 jm64 (etvar G9 K96) S39 T121 (star) jm61 (appendEnv G11 (etvar empty K96)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K96) H109)) (substhvl_tm_wfKind _ _ H100 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)))))
    | (QR_Beta K96 K97 S38 S39 T120 T121 jm62 jm63 H103) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T119 s4 d G9 G11)) =>
      (QR_Beta G11 K96 K97 S38 S39 T120 T121 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TRed G10 s4 T119 jm64 (etvar G9 K97) S38 T120 (weakenKind K96 (HS ty H0)) jm62 (appendEnv G11 (etvar empty K97)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K97) H109))) (subst_evar_TRed G10 s4 T119 jm64 G9 S39 T121 K97 jm63 G11 d (weaken_subst_evar _ empty H109)) (substhvl_tm_wfKind _ _ H103 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)))))
  end.
Fixpoint subst_etvar_TRed (G10 : Env) (S40 : Ty) (K95 : Kind) (jm64 : (Kinding G10 S40 K95)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm65 : (TRed G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) ,
  (TRed G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) :=
  match jm65 in (TRed _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) ,
    (TRed G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) with
    | (QR_Var K96 X51 lk5 H85 H86) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) =>
      (Env_reg_QR_Var G11 K96 _ (subst_etvar_lookup_etvar G10 S40 K95 jm64 d _ _ H110 X51 K96 lk5) (substhvl_ty_wfKind _ _ H85 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110))) (substhvl_ty_wfindex_ty (Kinding_wf_0 G10 S40 K95 jm64) (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110)) H86)))
    | (QR_Arrow S38 S39 T120 T121 jm56 jm57) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) =>
      (QR_Arrow G11 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T120) (tsubstTy (weakenTrace d H0) S40 T121) (subst_etvar_TRed G10 S40 K95 jm64 G9 S38 T120 (star) jm56 G11 d (weaken_subst_etvar _ empty H110)) (subst_etvar_TRed G10 S40 K95 jm64 G9 S39 T121 (star) jm57 G11 d (weaken_subst_etvar _ empty H110))))
    | (QR_Abs K97 K98 S39 T121 jm58 H91 H92) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) =>
      (QR_Abs G11 K97 K98 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T121) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TRed G10 S40 K95 jm64 (etvar G9 K97) S39 T121 (weakenKind K98 (HS ty H0)) jm58 (appendEnv G11 (tsubstEnv d S40 (etvar empty K97))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K97) H110))) (substhvl_ty_wfKind _ _ H91 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110))) (substhvl_ty_wfKind _ _ H92 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110)))))
    | (QR_App K97 K98 S38 S39 T120 T121 jm59 jm60) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) =>
      (QR_App G11 K97 K98 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T120) (tsubstTy (weakenTrace d H0) S40 T121) (subst_etvar_TRed G10 S40 K95 jm64 G9 S38 T120 (karr K98 K97) jm59 G11 d (weaken_subst_etvar _ empty H110)) (subst_etvar_TRed G10 S40 K95 jm64 G9 S39 T121 K98 jm60 G11 d (weaken_subst_etvar _ empty H110))))
    | (QR_All K97 S39 T121 jm61 H101) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) =>
      (QR_All G11 K97 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T121) (subst_etvar_TRed G10 S40 K95 jm64 (etvar G9 K97) S39 T121 (star) jm61 (appendEnv G11 (tsubstEnv d S40 (etvar empty K97))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K97) H110)) (substhvl_ty_wfKind _ _ H101 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110)))))
    | (QR_Beta K97 K98 S38 S39 T120 T121 jm62 jm63 H104) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K95 S40 d G9 G11)) =>
      (TRed_cast G11 _ _ _ G11 (tsubstTy d S40 (tapp (tabs K98 S38) S39)) (tsubstTy d S40 (tsubstTy X0 T121 T120)) K97 eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T120 d S40 T121)) eq_refl (QR_Beta G11 K97 K98 (tsubstTy (weakenTrace d (HS ty H0)) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T120) (tsubstTy (weakenTrace d H0) S40 T121) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TRed G10 S40 K95 jm64 (etvar G9 K98) S38 T120 (weakenKind K97 (HS ty H0)) jm62 (appendEnv G11 (tsubstEnv d S40 (etvar empty K98))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K98) H110))) (subst_etvar_TRed G10 S40 K95 jm64 G9 S39 T121 K98 jm63 G11 d (weaken_subst_etvar _ empty H110)) (substhvl_ty_wfKind _ _ H104 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110))))))
  end.
Fixpoint subst_evar_Kinding (G10 : Env) (s4 : Tm) (T120 : Ty) (jm62 : (Typing G10 s4 T120)) (G9 : Env) (T : Ty) (K : Kind) (jm63 : (Kinding G9 T K)) :
(forall (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T120 s4 d G9 G11)) ,
  (Kinding G11 T K)) :=
  match jm63 in (Kinding _ T K) return (forall (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T120 s4 d G9 G11)) ,
    (Kinding G11 T K)) with
    | (K_TVar K96 X51 lk5 H86 H87) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T120 s4 d G9 G11)) =>
      (K_TVar G11 K96 X51 (subst_evar_lookup_etvar T120 H99 K96 lk5) (substhvl_tm_wfKind _ _ H86 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99))) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99)) H87)))
    | (K_Abs K97 K100 T122 jm56 H88 H89) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T120 s4 d G9 G11)) =>
      (K_Abs G11 K97 K100 T122 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Kinding G10 s4 T120 jm62 (etvar G9 K97) T122 (weakenKind K100 (HS ty H0)) jm56 (appendEnv G11 (etvar empty K97)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K97) H99))) (substhvl_tm_wfKind _ _ H88 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99))) (substhvl_tm_wfKind _ _ H89 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99)))))
    | (K_App K98 K99 T121 T122 jm57 jm58) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T120 s4 d G9 G11)) =>
      (K_App G11 K98 K99 T121 T122 (subst_evar_Kinding G10 s4 T120 jm62 G9 T121 (karr K98 K99) jm57 G11 d (weaken_subst_evar _ empty H99)) (subst_evar_Kinding G10 s4 T120 jm62 G9 T122 K98 jm58 G11 d (weaken_subst_evar _ empty H99))))
    | (K_Arr T121 T122 jm59 jm60) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T120 s4 d G9 G11)) =>
      (K_Arr G11 T121 T122 (subst_evar_Kinding G10 s4 T120 jm62 G9 T121 (star) jm59 G11 d (weaken_subst_evar _ empty H99)) (subst_evar_Kinding G10 s4 T120 jm62 G9 T122 (star) jm60 G11 d (weaken_subst_evar _ empty H99))))
    | (K_All K97 T122 jm61 H97) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T120 s4 d G9 G11)) =>
      (K_All G11 K97 T122 (subst_evar_Kinding G10 s4 T120 jm62 (etvar G9 K97) T122 (star) jm61 (appendEnv G11 (etvar empty K97)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K97) H99)) (substhvl_tm_wfKind _ _ H97 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99)))))
  end.
Fixpoint subst_etvar_Kinding (G10 : Env) (S38 : Ty) (K96 : Kind) (jm62 : (Kinding G10 S38 K96)) (G9 : Env) (T : Ty) (K : Kind) (jm63 : (Kinding G9 T K)) :
(forall (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K96 S38 d G9 G11)) ,
  (Kinding G11 (tsubstTy d S38 T) K)) :=
  match jm63 in (Kinding _ T K) return (forall (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K96 S38 d G9 G11)) ,
    (Kinding G11 (tsubstTy d S38 T) K)) with
    | (K_TVar K97 X51 lk5 H87 H88) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K96 S38 d G9 G11)) =>
      (subst_etvar_lookup_etvar G10 S38 K96 jm62 d G9 G11 H100 X51 K97 lk5))
    | (K_Abs K98 K101 T122 jm56 H89 H90) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K96 S38 d G9 G11)) =>
      (K_Abs G11 K98 K101 (tsubstTy (weakenTrace d (HS ty H0)) S38 T122) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_Kinding G10 S38 K96 jm62 (etvar G9 K98) T122 (weakenKind K101 (HS ty H0)) jm56 (appendEnv G11 (tsubstEnv d S38 (etvar empty K98))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K98) H100))) (substhvl_ty_wfKind _ _ H89 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H100))) (substhvl_ty_wfKind _ _ H90 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H100)))))
    | (K_App K99 K100 T121 T122 jm57 jm58) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K96 S38 d G9 G11)) =>
      (K_App G11 K99 K100 (tsubstTy (weakenTrace d H0) S38 T121) (tsubstTy (weakenTrace d H0) S38 T122) (subst_etvar_Kinding G10 S38 K96 jm62 G9 T121 (karr K99 K100) jm57 G11 d (weaken_subst_etvar _ empty H100)) (subst_etvar_Kinding G10 S38 K96 jm62 G9 T122 K99 jm58 G11 d (weaken_subst_etvar _ empty H100))))
    | (K_Arr T121 T122 jm59 jm60) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K96 S38 d G9 G11)) =>
      (K_Arr G11 (tsubstTy (weakenTrace d H0) S38 T121) (tsubstTy (weakenTrace d H0) S38 T122) (subst_etvar_Kinding G10 S38 K96 jm62 G9 T121 (star) jm59 G11 d (weaken_subst_etvar _ empty H100)) (subst_etvar_Kinding G10 S38 K96 jm62 G9 T122 (star) jm60 G11 d (weaken_subst_etvar _ empty H100))))
    | (K_All K98 T122 jm61 H98) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K96 S38 d G9 G11)) =>
      (K_All G11 K98 (tsubstTy (weakenTrace d (HS ty H0)) S38 T122) (subst_etvar_Kinding G10 S38 K96 jm62 (etvar G9 K98) T122 (star) jm61 (appendEnv G11 (tsubstEnv d S38 (etvar empty K98))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K98) H100)) (substhvl_ty_wfKind _ _ H98 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H100)))))
  end.
Fixpoint subst_evar_TRedStar (G10 : Env) (s4 : Tm) (T121 : Ty) (jm59 : (Typing G10 s4 T121)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm60 : (TRedStar G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T121 s4 d G9 G11)) ,
  (TRedStar G11 T1 T2 K)) :=
  match jm60 in (TRedStar _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T121 s4 d G9 G11)) ,
    (TRedStar G11 T1 T2 K)) with
    | (QRS_Nil K97 T122 jm56) => (fun (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T121 s4 d G9 G11)) =>
      (QRS_Nil G11 K97 T122 (subst_evar_Kinding G10 s4 T121 jm59 G9 T122 K97 jm56 G11 d (weaken_subst_evar _ empty H94))))
    | (QRS_Cons K97 S38 T122 U5 jm57 jm58) => (fun (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T121 s4 d G9 G11)) =>
      (QRS_Cons G11 K97 S38 T122 U5 (subst_evar_TRedStar G10 s4 T121 jm59 G9 S38 T122 K97 jm57 G11 d (weaken_subst_evar _ empty H94)) (subst_evar_TRed G10 s4 T121 jm59 G9 T122 U5 K97 jm58 G11 d (weaken_subst_evar _ empty H94))))
  end.
Fixpoint subst_etvar_TRedStar (G10 : Env) (S39 : Ty) (K97 : Kind) (jm59 : (Kinding G10 S39 K97)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm60 : (TRedStar G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K97 S39 d G9 G11)) ,
  (TRedStar G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) :=
  match jm60 in (TRedStar _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K97 S39 d G9 G11)) ,
    (TRedStar G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) with
    | (QRS_Nil K98 T122 jm56) => (fun (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K97 S39 d G9 G11)) =>
      (QRS_Nil G11 K98 (tsubstTy (weakenTrace d H0) S39 T122) (subst_etvar_Kinding G10 S39 K97 jm59 G9 T122 K98 jm56 G11 d (weaken_subst_etvar _ empty H95))))
    | (QRS_Cons K98 S38 T122 U5 jm57 jm58) => (fun (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K97 S39 d G9 G11)) =>
      (QRS_Cons G11 K98 (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T122) (tsubstTy (weakenTrace d H0) S39 U5) (subst_etvar_TRedStar G10 S39 K97 jm59 G9 S38 T122 K98 jm57 G11 d (weaken_subst_etvar _ empty H95)) (subst_etvar_TRed G10 S39 K97 jm59 G9 T122 U5 K98 jm58 G11 d (weaken_subst_etvar _ empty H95))))
  end.
Fixpoint subst_evar_TyEq (G10 : Env) (s4 : Tm) (T122 : Ty) (jm68 : (Typing G10 s4 T122)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm69 : (TyEq G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) ,
  (TyEq G11 T1 T2 K)) :=
  match jm69 in (TyEq _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) ,
    (TyEq G11 T1 T2 K)) with
    | (Q_Arrow S38 S39 T124 T126 jm56 jm57) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_Arrow G11 S38 S39 T124 T126 (subst_evar_TyEq G10 s4 T122 jm68 G9 S38 T124 (star) jm56 G11 d (weaken_subst_evar _ empty H120)) (subst_evar_TyEq G10 s4 T122 jm68 G9 S39 T126 (star) jm57 G11 d (weaken_subst_evar _ empty H120))))
    | (Q_Abs K99 K102 S39 T126 jm58 H94 H95) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_Abs G11 K99 K102 S39 T126 (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TyEq G10 s4 T122 jm68 (etvar G9 K99) S39 T126 (weakenKind K102 (HS ty H0)) jm58 (appendEnv G11 (etvar empty K99)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K99) H120))) (substhvl_tm_wfKind _ _ H94 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H120))) (substhvl_tm_wfKind _ _ H95 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H120)))))
    | (Q_App K99 K102 S38 S39 T124 T126 jm59 jm60) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_App G11 K99 K102 S38 S39 T124 T126 (subst_evar_TyEq G10 s4 T122 jm68 G9 S38 T124 (karr K99 K102) jm59 G11 d (weaken_subst_evar _ empty H120)) (subst_evar_TyEq G10 s4 T122 jm68 G9 S39 T126 K99 jm60 G11 d (weaken_subst_evar _ empty H120))))
    | (Q_All K99 S39 T126 jm61 H104) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_All G11 K99 S39 T126 (subst_evar_TyEq G10 s4 T122 jm68 (etvar G9 K99) S39 T126 (star) jm61 (appendEnv G11 (etvar empty K99)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K99) H120)) (substhvl_tm_wfKind _ _ H104 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H120)))))
    | (Q_Beta K100 K101 T125 T126 jm62 jm63 H108) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_Beta G11 K100 K101 T125 T126 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Kinding G10 s4 T122 jm68 (etvar G9 K100) T125 (weakenKind K101 (HS ty H0)) jm62 (appendEnv G11 (etvar empty K100)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K100) H120))) (subst_evar_Kinding G10 s4 T122 jm68 G9 T126 K100 jm63 G11 d (weaken_subst_evar _ empty H120)) (substhvl_tm_wfKind _ _ H108 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H120)))))
    | (Q_Refl K98 T123 jm64) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_Refl G11 K98 T123 (subst_evar_Kinding G10 s4 T122 jm68 G9 T123 K98 jm64 G11 d (weaken_subst_evar _ empty H120))))
    | (Q_Symm K98 T123 U5 jm65) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_Symm G11 K98 T123 U5 (subst_evar_TyEq G10 s4 T122 jm68 G9 T123 U5 K98 jm65 G11 d (weaken_subst_evar _ empty H120))))
    | (Q_Trans K98 T123 U5 V1 jm66 jm67) => (fun (G11 : Env) (d : (Trace tm)) (H120 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (Q_Trans G11 K98 T123 U5 V1 (subst_evar_TyEq G10 s4 T122 jm68 G9 T123 U5 K98 jm66 G11 d (weaken_subst_evar _ empty H120)) (subst_evar_TyEq G10 s4 T122 jm68 G9 U5 V1 K98 jm67 G11 d (weaken_subst_evar _ empty H120))))
  end.
Fixpoint subst_etvar_TyEq (G10 : Env) (S40 : Ty) (K98 : Kind) (jm68 : (Kinding G10 S40 K98)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm69 : (TyEq G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) ,
  (TyEq G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) :=
  match jm69 in (TyEq _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) ,
    (TyEq G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) with
    | (Q_Arrow S38 S39 T124 T126 jm56 jm57) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (Q_Arrow G11 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T124) (tsubstTy (weakenTrace d H0) S40 T126) (subst_etvar_TyEq G10 S40 K98 jm68 G9 S38 T124 (star) jm56 G11 d (weaken_subst_etvar _ empty H121)) (subst_etvar_TyEq G10 S40 K98 jm68 G9 S39 T126 (star) jm57 G11 d (weaken_subst_etvar _ empty H121))))
    | (Q_Abs K100 K103 S39 T126 jm58 H95 H96) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (Q_Abs G11 K100 K103 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T126) (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TyEq G10 S40 K98 jm68 (etvar G9 K100) S39 T126 (weakenKind K103 (HS ty H0)) jm58 (appendEnv G11 (tsubstEnv d S40 (etvar empty K100))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K100) H121))) (substhvl_ty_wfKind _ _ H95 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H121))) (substhvl_ty_wfKind _ _ H96 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H121)))))
    | (Q_App K100 K103 S38 S39 T124 T126 jm59 jm60) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (Q_App G11 K100 K103 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T124) (tsubstTy (weakenTrace d H0) S40 T126) (subst_etvar_TyEq G10 S40 K98 jm68 G9 S38 T124 (karr K100 K103) jm59 G11 d (weaken_subst_etvar _ empty H121)) (subst_etvar_TyEq G10 S40 K98 jm68 G9 S39 T126 K100 jm60 G11 d (weaken_subst_etvar _ empty H121))))
    | (Q_All K100 S39 T126 jm61 H105) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (Q_All G11 K100 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T126) (subst_etvar_TyEq G10 S40 K98 jm68 (etvar G9 K100) S39 T126 (star) jm61 (appendEnv G11 (tsubstEnv d S40 (etvar empty K100))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K100) H121)) (substhvl_ty_wfKind _ _ H105 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H121)))))
    | (Q_Beta K101 K102 T125 T126 jm62 jm63 H109) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (TyEq_cast G11 _ _ _ G11 (tsubstTy d S40 (tapp (tabs K101 T125) T126)) (tsubstTy d S40 (tsubstTy X0 T126 T125)) K102 eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T125 d S40 T126)) eq_refl (Q_Beta G11 K101 K102 (tsubstTy (weakenTrace d (HS ty H0)) S40 T125) (tsubstTy (weakenTrace d H0) S40 T126) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_Kinding G10 S40 K98 jm68 (etvar G9 K101) T125 (weakenKind K102 (HS ty H0)) jm62 (appendEnv G11 (tsubstEnv d S40 (etvar empty K101))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K101) H121))) (subst_etvar_Kinding G10 S40 K98 jm68 G9 T126 K101 jm63 G11 d (weaken_subst_etvar _ empty H121)) (substhvl_ty_wfKind _ _ H109 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H121))))))
    | (Q_Refl K99 T123 jm64) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (Q_Refl G11 K99 (tsubstTy (weakenTrace d H0) S40 T123) (subst_etvar_Kinding G10 S40 K98 jm68 G9 T123 K99 jm64 G11 d (weaken_subst_etvar _ empty H121))))
    | (Q_Symm K99 T123 U5 jm65) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (Q_Symm G11 K99 (tsubstTy (weakenTrace d H0) S40 T123) (tsubstTy (weakenTrace d H0) S40 U5) (subst_etvar_TyEq G10 S40 K98 jm68 G9 T123 U5 K99 jm65 G11 d (weaken_subst_etvar _ empty H121))))
    | (Q_Trans K99 T123 U5 V1 jm66 jm67) => (fun (G11 : Env) (d : (Trace ty)) (H121 : (subst_etvar G10 K98 S40 d G9 G11)) =>
      (Q_Trans G11 K99 (tsubstTy (weakenTrace d H0) S40 T123) (tsubstTy (weakenTrace d H0) S40 U5) (tsubstTy (weakenTrace d H0) S40 V1) (subst_etvar_TyEq G10 S40 K98 jm68 G9 T123 U5 K99 jm66 G11 d (weaken_subst_etvar _ empty H121)) (subst_etvar_TyEq G10 S40 K98 jm68 G9 U5 V1 K99 jm67 G11 d (weaken_subst_etvar _ empty H121))))
  end.
Fixpoint subst_evar_Typing (G10 : Env) (s4 : Tm) (T123 : Ty) (jm65 : (Typing G10 s4 T123)) (G9 : Env) (t : Tm) (T : Ty) (jm66 : (Typing G9 t T)) :
(forall (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) ,
  (Typing G11 (substTm d s4 t) T)) :=
  match jm66 in (Typing _ t T) return (forall (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) ,
    (Typing G11 (substTm d s4 t) T)) with
    | (T_Var T124 y1 lk5 H92 H93) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (subst_evar_lookup_evar G10 s4 T123 jm65 d G9 G11 H111 y1 T124 lk5))
    | (T_Abs T125 T128 t19 jm60 jm61 H95) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (T_Abs G11 T125 T128 (substTm (weakenTrace d (HS tm H0)) s4 t19) (subst_evar_Kinding G10 s4 T123 jm65 G9 T125 (star) jm60 G11 d (weaken_subst_evar _ empty H111)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G10 s4 T123 jm65 (evar G9 T125) t19 (weakenTy T128 (HS tm H0)) jm61 (appendEnv G11 (evar empty T125)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T125) H111))) (substhvl_tm_wfTy _ _ H95 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H111)))))
    | (T_App T126 T127 t20 t21 jm62 jm63) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (T_App G11 T126 T127 (substTm (weakenTrace d H0) s4 t20) (substTm (weakenTrace d H0) s4 t21) (subst_evar_Typing G10 s4 T123 jm65 G9 t20 (tarr T126 T127) jm62 G11 d (weaken_subst_evar _ empty H111)) (subst_evar_Typing G10 s4 T123 jm65 G9 t21 T126 jm63 G11 d (weaken_subst_evar _ empty H111))))
    | (T_TAbs K99 T124 t19 jm64 H101) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (T_TAbs G11 K99 T124 (substTm (weakenTrace d (HS ty H0)) s4 t19) (subst_evar_Typing G10 s4 T123 jm65 (etvar G9 K99) t19 T124 jm64 (appendEnv G11 (etvar empty K99)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K99) H111)) (substhvl_tm_wfKind _ _ H101 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H111)))))
    | (T_TApp K100 T127 T128 t20 jm56 jm57) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (T_TApp G11 K100 T127 T128 (substTm (weakenTrace d H0) s4 t20) (subst_evar_Typing G10 s4 T123 jm65 G9 t20 (tall K100 T127) jm56 G11 d (weaken_subst_evar _ empty H111)) (subst_evar_Kinding G10 s4 T123 jm65 G9 T128 K100 jm57 G11 d (weaken_subst_evar _ empty H111))))
    | (T_Eq S38 T124 t19 jm58 jm59) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (T_Eq G11 S38 T124 (substTm (weakenTrace d H0) s4 t19) (subst_evar_Typing G10 s4 T123 jm65 G9 t19 S38 jm58 G11 d (weaken_subst_evar _ empty H111)) (subst_evar_TyEq G10 s4 T123 jm65 G9 S38 T124 (star) jm59 G11 d (weaken_subst_evar _ empty H111))))
  end.
Fixpoint subst_etvar_Typing (G10 : Env) (S39 : Ty) (K99 : Kind) (jm65 : (Kinding G10 S39 K99)) (G9 : Env) (t : Tm) (T : Ty) (jm66 : (Typing G9 t T)) :
(forall (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) ,
  (Typing G11 (tsubstTm d S39 t) (tsubstTy d S39 T))) :=
  match jm66 in (Typing _ t T) return (forall (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) ,
    (Typing G11 (tsubstTm d S39 t) (tsubstTy d S39 T))) with
    | (T_Var T124 y1 lk5 H93 H94) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) =>
      (T_Var G11 (tsubstTy (weakenTrace d H0) S39 T124) y1 (subst_etvar_lookup_evar K99 (Kinding_wf_0 G10 S39 K99 jm65) H112 T124 lk5) (substhvl_ty_wfTy (Kinding_wf_0 G10 S39 K99 jm65) _ _ H93 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112)) H94)))
    | (T_Abs T125 T128 t19 jm60 jm61 H96) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) =>
      (T_Abs G11 (tsubstTy (weakenTrace d H0) S39 T125) (tsubstTy (weakenTrace d H0) S39 T128) (tsubstTm (weakenTrace d (HS tm H0)) S39 t19) (subst_etvar_Kinding G10 S39 K99 jm65 G9 T125 (star) jm60 G11 d (weaken_subst_etvar _ empty H112)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d S39 T128)) (subst_etvar_Typing G10 S39 K99 jm65 (evar G9 T125) t19 (weakenTy T128 (HS tm H0)) jm61 (appendEnv G11 (tsubstEnv d S39 (evar empty T125))) (weakenTrace d (HS tm H0)) (weaken_subst_etvar _ (evar empty T125) H112))) (substhvl_ty_wfTy (Kinding_wf_0 G10 S39 K99 jm65) _ _ H96 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112)))))
    | (T_App T126 T127 t20 t21 jm62 jm63) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) =>
      (T_App G11 (tsubstTy (weakenTrace d H0) S39 T126) (tsubstTy (weakenTrace d H0) S39 T127) (tsubstTm (weakenTrace d H0) S39 t20) (tsubstTm (weakenTrace d H0) S39 t21) (subst_etvar_Typing G10 S39 K99 jm65 G9 t20 (tarr T126 T127) jm62 G11 d (weaken_subst_etvar _ empty H112)) (subst_etvar_Typing G10 S39 K99 jm65 G9 t21 T126 jm63 G11 d (weaken_subst_etvar _ empty H112))))
    | (T_TAbs K100 T124 t19 jm64 H102) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) =>
      (T_TAbs G11 K100 (tsubstTy (weakenTrace d (HS ty H0)) S39 T124) (tsubstTm (weakenTrace d (HS ty H0)) S39 t19) (subst_etvar_Typing G10 S39 K99 jm65 (etvar G9 K100) t19 T124 jm64 (appendEnv G11 (tsubstEnv d S39 (etvar empty K100))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K100) H112)) (substhvl_ty_wfKind _ _ H102 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112)))))
    | (T_TApp K101 T127 T128 t20 jm56 jm57) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) =>
      (Typing_cast G11 _ _ G11 (tsubstTm d S39 (tyapp t20 T128)) (tsubstTy d S39 (tsubstTy X0 T128 T127)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T127 d S39 T128)) (T_TApp G11 K101 (tsubstTy (weakenTrace d (HS ty H0)) S39 T127) (tsubstTy (weakenTrace d H0) S39 T128) (tsubstTm (weakenTrace d H0) S39 t20) (subst_etvar_Typing G10 S39 K99 jm65 G9 t20 (tall K101 T127) jm56 G11 d (weaken_subst_etvar _ empty H112)) (subst_etvar_Kinding G10 S39 K99 jm65 G9 T128 K101 jm57 G11 d (weaken_subst_etvar _ empty H112)))))
    | (T_Eq S38 T124 t19 jm58 jm59) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K99 S39 d G9 G11)) =>
      (T_Eq G11 (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T124) (tsubstTm (weakenTrace d H0) S39 t19) (subst_etvar_Typing G10 S39 K99 jm65 G9 t19 S38 jm58 G11 d (weaken_subst_etvar _ empty H112)) (subst_etvar_TyEq G10 S39 K99 jm65 G9 S38 T124 (star) jm59 G11 d (weaken_subst_etvar _ empty H112))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenKind_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.