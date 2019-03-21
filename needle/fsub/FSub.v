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
  Fixpoint weakenIndexty (X19 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X19
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X19 k))
        | _ => (weakenIndexty X19 k)
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x6 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x6 k) k0) = (weakenIndextm x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexty_append  :
    (forall (X19 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X19 k) k0) = (weakenIndexty X19 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | top 
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (T : Ty) (t : Tm)
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
  Fixpoint shiftIndex (c : (Cutoff tm)) (x6 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x6)
      | (CS c) => match x6 with
        | (I0) => I0
        | (IS x6) => (IS (shiftIndex c x6))
      end
    end.
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X19 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X19)
      | (CS c) => match X19 with
        | (I0) => I0
        | (IS X19) => (IS (tshiftIndex c X19))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S9 : Ty) {struct S9} :
  Ty :=
    match S9 with
      | (tvar X19) => (tvar (tshiftIndex c X19))
      | (top) => (top)
      | (tarr T49 T50) => (tarr (tshiftTy c T49) (tshiftTy c T50))
      | (tall T51 T52) => (tall (tshiftTy c T51) (tshiftTy (CS c) T52))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var (shiftIndex c x6))
      | (abs T49 t17) => (abs T49 (shiftTm (CS c) t17))
      | (app t18 t19) => (app (shiftTm c t18) (shiftTm c t19))
      | (tabs T50 t20) => (tabs T50 (shiftTm c t20))
      | (tapp t21 T51) => (tapp (shiftTm c t21) T51)
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T49 t17) => (abs (tshiftTy c T49) (tshiftTm c t17))
      | (app t18 t19) => (app (tshiftTm c t18) (tshiftTm c t19))
      | (tabs T50 t20) => (tabs (tshiftTy c T50) (tshiftTm (CS c) t20))
      | (tapp t21 T51) => (tapp (tshiftTm c t21) (tshiftTy c T51))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S9 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S9
      | (HS tm k) => (weakenTy S9 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S9 k))
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
        (T49 : (Trace a)).
  
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
  Fixpoint tsubstIndex (d : (Trace ty)) (S9 : Ty) (X19 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X19 with
        | (I0) => S9
        | (IS X19) => (tvar X19)
      end
      | (XS tm d) => (tsubstIndex d S9 X19)
      | (XS ty d) => match X19 with
        | (I0) => (tvar I0)
        | (IS X19) => (tshiftTy C0 (tsubstIndex d S9 X19))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S9 : Ty) (S10 : Ty) {struct S10} :
  Ty :=
    match S10 with
      | (tvar X19) => (tsubstIndex d S9 X19)
      | (top) => (top)
      | (tarr T49 T50) => (tarr (tsubstTy d S9 T49) (tsubstTy d S9 T50))
      | (tall T51 T52) => (tall (tsubstTy d S9 T51) (tsubstTy (weakenTrace d (HS ty H0)) S9 T52))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x6) => (substIndex d s x6)
      | (abs T49 t17) => (abs T49 (substTm (weakenTrace d (HS tm H0)) s t17))
      | (app t18 t19) => (app (substTm d s t18) (substTm d s t19))
      | (tabs T50 t20) => (tabs T50 (substTm (weakenTrace d (HS ty H0)) s t20))
      | (tapp t21 T51) => (tapp (substTm d s t21) T51)
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S9 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T49 t17) => (abs (tsubstTy d S9 T49) (tsubstTm (weakenTrace d (HS tm H0)) S9 t17))
      | (app t18 t19) => (app (tsubstTm d S9 t18) (tsubstTm d S9 t19))
      | (tabs T50 t20) => (tabs (tsubstTy d S9 T50) (tsubstTm (weakenTrace d (HS ty H0)) S9 t20))
      | (tapp t21 T51) => (tapp (tsubstTm d S9 t21) (tsubstTy d S9 T51))
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
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S9 : Ty) :
    (forall (k : Hvl) (X19 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S9 (tshiftIndex (weakenCutoffty C0 k) X19)) = (tvar X19))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S10 : Ty) (k : Hvl) (S9 : Ty) {struct S10} :
  ((tsubstTy (weakenTrace X0 k) S9 (tshiftTy (weakenCutoffty C0 k) S10)) = S10) :=
    match S10 return ((tsubstTy (weakenTrace X0 k) S9 (tshiftTy (weakenCutoffty C0 k) S10)) = S10) with
      | (tvar X19) => (tsubstIndex0_tshiftIndex0_reflection_ind S9 k X19)
      | (top) => eq_refl
      | (tarr T49 T50) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T49 k S9) (tsubst0_tshift0_Ty_reflection_ind T50 k S9))
      | (tall T49 T50) => (f_equal2 tall (tsubst0_tshift0_Ty_reflection_ind T49 k S9) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T50 (HS ty k) S9)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x6) => (substIndex0_shiftIndex0_reflection_ind s k x6)
      | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t17 (HS tm k) s)))
      | (app t18 t19) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t18 k s) (subst0_shift0_Tm_reflection_ind t19 k s))
      | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t17 (HS ty k) s)))
      | (tapp t17 T49) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t17 k s) eq_refl)
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S9 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S9 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S9 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x6) => eq_refl
      | (abs T49 t17) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T49 k S9) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t17 (HS tm k) S9)))
      | (app t18 t19) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t18 k S9) (tsubst0_tshift0_Tm_reflection_ind t19 k S9))
      | (tabs T49 t17) => (f_equal2 tabs (tsubst0_tshift0_Ty_reflection_ind T49 k S9) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t17 (HS ty k) S9)))
      | (tapp t17 T49) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t17 k S9) (tsubst0_tshift0_Ty_reflection_ind T49 k S9))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S10 : Ty) : (forall (S9 : Ty) ,
    ((tsubstTy X0 S9 (tshiftTy C0 S10)) = S10)) := (tsubst0_tshift0_Ty_reflection_ind S10 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S9 : Ty) ,
    ((tsubstTm X0 S9 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
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
      (forall (k : Hvl) (c : (Cutoff ty)) (X19 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c) k) (tshiftIndex (weakenCutoffty C0 k) X19)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c k) X19)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S9 : Ty) (k : Hvl) (c : (Cutoff ty)) {struct S9} :
    ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S9)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S9))) :=
      match S9 return ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S9)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S9))) with
        | (tvar X19) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c X19))
        | (top) => eq_refl
        | (tarr T49 T50) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T49 k c) (tshift_tshift0_Ty_comm_ind T50 k c))
        | (tall T49 T50) => (f_equal2 tall (tshift_tshift0_Ty_comm_ind T49 k c) (tshift_tshift0_Ty_comm_ind T50 (HS ty k) c))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x6))
        | (abs T49 t17) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (shift_shift0_Tm_comm_ind t18 k c) (shift_shift0_Tm_comm_ind t19 k c))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (shift_shift0_Tm_comm_ind t17 (HS ty k) c))
        | (tapp t17 T49) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (shift_tshift0_Tm_comm_ind t18 k c) (shift_tshift0_Tm_comm_ind t19 k c))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (shift_tshift0_Tm_comm_ind t17 (HS ty k) c))
        | (tapp t17 T49) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (tshift_shift0_Tm_comm_ind t18 k c) (tshift_shift0_Tm_comm_ind t19 k c))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (tshift_shift0_Tm_comm_ind t17 (HS ty k) c))
        | (tapp t17 T49) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T49 k c) (tshift_tshift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t18 k c) (tshift_tshift0_Tm_comm_ind t19 k c))
        | (tabs T49 t17) => (f_equal2 tabs (tshift_tshift0_Ty_comm_ind T49 k c) (tshift_tshift0_Tm_comm_ind t17 (HS ty k) c))
        | (tapp t17 T49) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t17 k c) (tshift_tshift0_Ty_comm_ind T49 k c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S9 : Ty) : (forall (c : (Cutoff ty)) ,
      ((tshiftTy (CS c) (tshiftTy C0 S9)) = (tshiftTy C0 (tshiftTy c S9)))) := (tshift_tshift0_Ty_comm_ind S9 H0).
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
    (forall (k : Hvl) (c : (Cutoff ty)) (S9 : Ty) ,
      ((weakenTy (tshiftTy c S9) k) = (tshiftTy (weakenCutoffty c k) (weakenTy S9 k)))).
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
    Lemma tshiftTy_tsubstIndex0_comm_ind (c : (Cutoff ty)) (S9 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c k) (tsubstIndex (weakenTrace X0 k) S9 X19)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c S9) (tshiftIndex (weakenCutoffty (CS c) k) X19)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S10 : Ty) (k : Hvl) (c : (Cutoff ty)) (S9 : Ty) {struct S10} :
    ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S9 S10)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S9) (tshiftTy (weakenCutoffty (CS c) k) S10))) :=
      match S10 return ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S9 S10)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S9) (tshiftTy (weakenCutoffty (CS c) k) S10))) with
        | (tvar X19) => (tshiftTy_tsubstIndex0_comm_ind c S9 k X19)
        | (top) => eq_refl
        | (tarr T49 T50) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T49 k c S9) (tshift_tsubst0_Ty_comm_ind T50 k c S9))
        | (tall T49 T50) => (f_equal2 tall (tshift_tsubst0_Ty_comm_ind T49 k c S9) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T50 (HS ty k) c S9) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x6) => (shiftTm_substIndex0_comm_ind c s k x6)
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t17 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (shift_subst0_Tm_comm_ind t18 k c s) (shift_subst0_Tm_comm_ind t19 k c s))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t17 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t17 T49) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t17 k c s) eq_refl)
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) (S9 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S9 s)) = (tsubstTm (weakenTrace X0 k) S9 (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S9 s)) = (tsubstTm (weakenTrace X0 k) S9 (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t17 (HS tm k) c S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t18 k c S9) (shift_tsubst0_Tm_comm_ind t19 k c S9))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t17 (HS ty k) c S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t17 T49) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t17 k c S9) eq_refl)
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) with
        | (var x6) => (tshiftTm_substIndex0_comm_ind c s k x6)
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t17 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tshift_subst0_Tm_comm_ind t18 k c s) (tshift_subst0_Tm_comm_ind t19 k c s))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t17 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t17 T49) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t17 k c s) eq_refl)
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) (S9 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S9 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S9) (tshiftTm (weakenCutoffty (CS c) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S9 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S9) (tshiftTm (weakenCutoffty (CS c) k) s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T49 k c S9) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t17 (HS tm k) c S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t18 k c S9) (tshift_tsubst0_Tm_comm_ind t19 k c S9))
        | (tabs T49 t17) => (f_equal2 tabs (tshift_tsubst0_Ty_comm_ind T49 k c S9) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t17 (HS ty k) c S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t17 T49) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t17 k c S9) (tshift_tsubst0_Ty_comm_ind T49 k c S9))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S10 : Ty) : (forall (c : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftTy c (tsubstTy X0 S9 S10)) = (tsubstTy X0 (tshiftTy c S9) (tshiftTy (CS c) S10)))) := (tshift_tsubst0_Ty_comm_ind S10 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c (substTm X0 s s0)) = (substTm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff tm)) (S9 : Ty) ,
      ((shiftTm c (tsubstTm X0 S9 s)) = (tsubstTm X0 S9 (shiftTm c s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c (substTm X0 s s0)) = (substTm X0 (tshiftTm c s) (tshiftTm c s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftTm c (tsubstTm X0 S9 s)) = (tsubstTm X0 (tshiftTy c S9) (tshiftTm (CS c) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
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
    Lemma tsubstIndex_shiftTy0_comm_ind (d : (Trace ty)) (S9 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k) S9 X19) = (tsubstIndex (weakenTrace d k) S9 X19))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S9 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k) S9 (tshiftIndex (weakenCutoffty C0 k) X19)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d k) S9 X19)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S10 : Ty) (k : Hvl) (d : (Trace ty)) (S9 : Ty) {struct S10} :
    ((tsubstTy (weakenTrace (XS ty d) k) S9 (tshiftTy (weakenCutoffty C0 k) S10)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S9 S10))) :=
      match S10 return ((tsubstTy (weakenTrace (XS ty d) k) S9 (tshiftTy (weakenCutoffty C0 k) S10)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S9 S10))) with
        | (tvar X19) => (tsubstIndex_tshiftTy0_comm_ind d S9 k X19)
        | (top) => eq_refl
        | (tarr T49 T50) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T49 k d S9) (tsubst_tshift0_Ty_comm_ind T50 k d S9))
        | (tall T49 T50) => (f_equal2 tall (tsubst_tshift0_Ty_comm_ind T49 k d S9) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T50 (HS ty k) d S9) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_shiftTm0_comm_ind d s k x6)
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t17 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_shift0_Tm_comm_ind t18 k d s) (subst_shift0_Tm_comm_ind t19 k d s))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t17 (HS ty k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t17 k d s) eq_refl)
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_tshiftTm0_comm_ind d s k x6)
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t17 (HS tm k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_tshift0_Tm_comm_ind t18 k d s) (subst_tshift0_Tm_comm_ind t19 k d s))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t17 (HS ty k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t17 k d s) eq_refl)
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S9 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S9 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S9 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S9 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S9 s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t17 (HS tm k) d S9) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t18 k d S9) (tsubst_shift0_Tm_comm_ind t19 k d S9))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t17 (HS ty k) d S9) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t17 k d S9) eq_refl)
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S9 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d) k) S9 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S9 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d) k) S9 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S9 s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T49 k d S9) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t17 (HS tm k) d S9) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t18 k d S9) (tsubst_tshift0_Tm_comm_ind t19 k d S9))
        | (tabs T49 t17) => (f_equal2 tabs (tsubst_tshift0_Ty_comm_ind T49 k d S9) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t17 (HS ty k) d S9) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t17 k d S9) (tsubst_tshift0_Ty_comm_ind T49 k d S9))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S10 : Ty) : (forall (d : (Trace ty)) (S9 : Ty) ,
      ((tsubstTy (XS ty d) S9 (tshiftTy C0 S10)) = (tshiftTy C0 (tsubstTy d S9 S10)))) := (tsubst_tshift0_Ty_comm_ind S10 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S9 : Ty) ,
      ((tsubstTm d S9 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d S9 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S9 : Ty) ,
      ((tsubstTm (XS ty d) S9 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d S9 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S10 : Ty) (k : Hvl) (d : (Trace ty)) (S9 : Ty) {struct S10} :
    ((tsubstTy (weakenTrace (XS tm d) k) S9 S10) = (tsubstTy (weakenTrace d k) S9 S10)) :=
      match S10 return ((tsubstTy (weakenTrace (XS tm d) k) S9 S10) = (tsubstTy (weakenTrace d k) S9 S10)) with
        | (tvar X19) => (tsubstIndex_shiftTy0_comm_ind d S9 k X19)
        | (top) => eq_refl
        | (tarr T49 T50) => (f_equal2 tarr (tsubst_tm_Ty_ind T49 k d S9) (tsubst_tm_Ty_ind T50 k d S9))
        | (tall T49 T50) => (f_equal2 tall (tsubst_tm_Ty_ind T49 k d S9) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T50 (HS ty k) d S9) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S9 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d) k) S9 s) = (tsubstTm (weakenTrace d k) S9 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d) k) S9 s) = (tsubstTm (weakenTrace d k) S9 s)) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs (tsubst_tm_Ty_ind T49 k d S9) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t17 (HS tm k) d S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tsubst_tm_Tm_ind t18 k d S9) (tsubst_tm_Tm_ind t19 k d S9))
        | (tabs T49 t17) => (f_equal2 tabs (tsubst_tm_Ty_ind T49 k d S9) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t17 (HS ty k) d S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t17 T49) => (f_equal2 tapp (tsubst_tm_Tm_ind t17 k d S9) (tsubst_tm_Ty_ind T49 k d S9))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S10 : Ty) : (forall (d : (Trace ty)) (S9 : Ty) ,
      ((tsubstTy (XS tm d) S9 S10) = (tsubstTy d S9 S10))) := (tsubst_tm_Ty_ind S10 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d : (Trace ty)) (S9 : Ty) ,
      ((tsubstTm (XS tm d) S9 s) = (tsubstTm d S9 s))) := (tsubst_tm_Tm_ind s H0).
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
    Lemma tsubstTm_substIndex0_commright_ind (d : (Trace ty)) (S9 : Ty) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((tsubstTm (weakenTrace d k) S9 (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tsubstTm d S9 s) x6))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d : (Trace ty)) (S9 : Ty) (S10 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tsubstTy (weakenTrace d k) S9 (tsubstIndex (weakenTrace X0 k) S10 X19)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S9 S10) (tsubstIndex (weakenTrace (XS ty d) k) S9 X19)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d : (Trace tm)) (s : Tm) (S9 : Ty) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace d k) s x6) = (tsubstTm (weakenTrace X0 k) S9 (substIndex (weakenTrace (XS ty d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S11 : Ty) (k : Hvl) (d : (Trace ty)) (S9 : Ty) (S10 : Ty) {struct S11} :
    ((tsubstTy (weakenTrace d k) S9 (tsubstTy (weakenTrace X0 k) S10 S11)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S9 S10) (tsubstTy (weakenTrace (XS ty d) k) S9 S11))) :=
      match S11 return ((tsubstTy (weakenTrace d k) S9 (tsubstTy (weakenTrace X0 k) S10 S11)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S9 S10) (tsubstTy (weakenTrace (XS ty d) k) S9 S11))) with
        | (tvar X19) => (tsubstTy_tsubstIndex0_commright_ind d S9 S10 k X19)
        | (top) => eq_refl
        | (tarr T49 T50) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T49 k d S9 S10) (tsubst_tsubst0_Ty_comm_ind T50 k d S9 S10))
        | (tall T49 T50) => (f_equal2 tall (tsubst_tsubst0_Ty_comm_ind T49 k d S9 S10) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T50 (HS ty k) d S9 S10) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x6) => (substTm_substIndex0_commright_ind d s s0 k x6)
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t17 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_subst0_Tm_comm_ind t18 k d s s0) (subst_subst0_Tm_comm_ind t19 k d s s0))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t17 (HS ty k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t17 k d s s0) eq_refl)
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (S9 : Ty) {struct s0} :
    ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S9 s0)) = (tsubstTm (weakenTrace X0 k) S9 (substTm (weakenTrace (XS ty d) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S9 s0)) = (tsubstTm (weakenTrace X0 k) S9 (substTm (weakenTrace (XS ty d) k) s s0))) with
        | (var x6) => (substTy_tsubstIndex0_commleft_ind d s S9 k x6)
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t17 (HS tm k) d s S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t18 k d s S9) (subst_tsubst0_Tm_comm_ind t19 k d s S9))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t17 (HS ty k) d s S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t17 k d s S9) eq_refl)
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace ty)) (S9 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d k) S9 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S9 s) (tsubstTm (weakenTrace d k) S9 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d k) S9 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S9 s) (tsubstTm (weakenTrace d k) S9 s0))) with
        | (var x6) => (tsubstTm_substIndex0_commright_ind d S9 s k x6)
        | (abs T49 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t17 (HS tm k) d S9 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t18 k d S9 s) (tsubst_subst0_Tm_comm_ind t19 k d S9 s))
        | (tabs T49 t17) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t17 (HS ty k) d S9 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t17 k d S9 s) eq_refl)
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S9 : Ty) (S10 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S9 (tsubstTm (weakenTrace X0 k) S10 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S9 S10) (tsubstTm (weakenTrace (XS ty d) k) S9 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S9 (tsubstTm (weakenTrace X0 k) S10 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S9 S10) (tsubstTm (weakenTrace (XS ty d) k) S9 s))) with
        | (var x6) => eq_refl
        | (abs T49 t17) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T49 k d S9 S10) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t17 (HS tm k) d S9 S10) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t18 k d S9 S10) (tsubst_tsubst0_Tm_comm_ind t19 k d S9 S10))
        | (tabs T49 t17) => (f_equal2 tabs (tsubst_tsubst0_Ty_comm_ind T49 k d S9 S10) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t17 (HS ty k) d S9 S10) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t17 T49) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t17 k d S9 S10) (tsubst_tsubst0_Ty_comm_ind T49 k d S9 S10))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S11 : Ty) : (forall (d : (Trace ty)) (S9 : Ty) (S10 : Ty) ,
      ((tsubstTy d S9 (tsubstTy X0 S10 S11)) = (tsubstTy X0 (tsubstTy d S9 S10) (tsubstTy (XS ty d) S9 S11)))) := (tsubst_tsubst0_Ty_comm_ind S11 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d s (substTm X0 s0 s1)) = (substTm X0 (substTm d s s0) (substTm (XS tm d) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) (S9 : Ty) ,
      ((substTm d s (tsubstTm X0 S9 s0)) = (tsubstTm X0 S9 (substTm (XS ty d) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d : (Trace ty)) (S9 : Ty) (s : Tm) ,
      ((tsubstTm d S9 (substTm X0 s s0)) = (substTm X0 (tsubstTm d S9 s) (tsubstTm d S9 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S9 : Ty) (S10 : Ty) ,
      ((tsubstTm d S9 (tsubstTm X0 S10 s)) = (tsubstTm X0 (tsubstTy d S9 S10) (tsubstTm (XS ty d) S9 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d : (Trace ty)) (S9 : Ty) (S10 : Ty) ,
        ((weakenTy (tsubstTy d S9 S10) k) = (tsubstTy (weakenTrace d k) S9 (weakenTy S10 k)))).
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
      (forall (k : Hvl) (d : (Trace ty)) (S9 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d S9 s) k) = (tsubstTm (weakenTrace d k) S9 (weakenTm s k)))).
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
    | wfTy_tvar (X19 : (Index ty))
        (wfi : (wfindex k X19)) :
        (wfTy k (tvar X19))
    | wfTy_top : (wfTy k (top))
    | wfTy_tarr {T49 : Ty}
        (wf : (wfTy k T49)) {T50 : Ty}
        (wf0 : (wfTy k T50)) :
        (wfTy k (tarr T49 T50))
    | wfTy_tall {T51 : Ty}
        (wf : (wfTy k T51)) {T52 : Ty}
        (wf0 : (wfTy (HS ty k) T52)) :
        (wfTy k (tall T51 T52)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x6 : (Index tm))
        (wfi : (wfindex k x6)) :
        (wfTm k (var x6))
    | wfTm_abs {T49 : Ty}
        (wf : (wfTy k T49)) {t17 : Tm}
        (wf0 : (wfTm (HS tm k) t17)) :
        (wfTm k (abs T49 t17))
    | wfTm_app {t18 : Tm}
        (wf : (wfTm k t18)) {t19 : Tm}
        (wf0 : (wfTm k t19)) :
        (wfTm k (app t18 t19))
    | wfTm_tabs {T50 : Ty}
        (wf : (wfTy k T50)) {t20 : Tm}
        (wf0 : (wfTm (HS ty k) t20)) :
        (wfTm k (tabs T50 t20))
    | wfTm_tapp {t21 : Tm}
        (wf : (wfTm k t21)) {T51 : Ty}
        (wf0 : (wfTy k T51)) :
        (wfTm k (tapp t21 T51)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H17 : (wfTy k (tvar X))) : (wfindex k X) := match H17 in (wfTy _ S9) return match S9 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k1 (tarr T1 T2))) : (wfTy k1 T1) := match H19 in (wfTy _ S11) return match S11 return Prop with
    | (tarr T1 T2) => (wfTy k1 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k1 (tarr T1 T2))) : (wfTy k1 T2) := match H19 in (wfTy _ S11) return match S11 return Prop with
    | (tarr T1 T2) => (wfTy k1 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H20 : (wfTy k2 (tall T1 T2))) : (wfTy k2 T1) := match H20 in (wfTy _ S12) return match S12 return Prop with
    | (tall T1 T2) => (wfTy k2 T1)
    | _ => True
  end with
    | (wfTy_tall T1 H4 T2 H5) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tall_2 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H20 : (wfTy k2 (tall T1 T2))) : (wfTy (HS ty k2) T2) := match H20 in (wfTy _ S12) return match S12 return Prop with
    | (tall T1 T2) => (wfTy (HS ty k2) T2)
    | _ => True
  end with
    | (wfTy_tall T1 H4 T2 H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k3 : Hvl) (x : (Index tm)) (H21 : (wfTm k3 (var x))) : (wfindex k3 x) := match H21 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k3 x)
    | _ => True
  end with
    | (wfTm_var x H6) => H6
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k4 : Hvl) (T : Ty) (t : Tm) (H22 : (wfTm k4 (abs T t))) : (wfTy k4 T) := match H22 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k4 T)
    | _ => True
  end with
    | (wfTm_abs T H7 t H8) => H7
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k4 : Hvl) (T : Ty) (t : Tm) (H22 : (wfTm k4 (abs T t))) : (wfTm (HS tm k4) t) := match H22 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k4) t)
    | _ => True
  end with
    | (wfTm_abs T H7 t H8) => H8
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k5 : Hvl) (t1 : Tm) (t2 : Tm) (H23 : (wfTm k5 (app t1 t2))) : (wfTm k5 t1) := match H23 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k5 t1)
    | _ => True
  end with
    | (wfTm_app t1 H9 t2 H10) => H9
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k5 : Hvl) (t1 : Tm) (t2 : Tm) (H23 : (wfTm k5 (app t1 t2))) : (wfTm k5 t2) := match H23 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k5 t2)
    | _ => True
  end with
    | (wfTm_app t1 H9 t2 H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k6 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k6 (tabs T t))) : (wfTy k6 T) := match H24 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTy k6 T)
    | _ => True
  end with
    | (wfTm_tabs T H11 t H12) => H11
    | _ => I
  end.
  Definition inversion_wfTm_tabs_2 (k6 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k6 (tabs T t))) : (wfTm (HS ty k6) t) := match H24 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTm (HS ty k6) t)
    | _ => True
  end with
    | (wfTm_tabs T H11 t H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k7 : Hvl) (t : Tm) (T : Ty) (H25 : (wfTm k7 (tapp t T))) : (wfTm k7 t) := match H25 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k7 t)
    | _ => True
  end with
    | (wfTm_tapp t H13 T H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k7 : Hvl) (t : Tm) (T : Ty) (H25 : (wfTm k7 (tapp t T))) : (wfTy k7 T) := match H25 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_tapp t H13 T H14) => H14
    | _ => I
  end.
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
    (forall (c : (Cutoff tm)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) (X19 : (Index ty)) ,
      (wfindex k8 X19) -> (wfindex k9 X19)).
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
    (forall (c : (Cutoff ty)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) (X19 : (Index ty)) ,
      (wfindex k8 X19) -> (wfindex k9 (tshiftIndex c X19))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k8 : Hvl) ,
    (forall (S13 : Ty) (wf : (wfTy k8 S13)) ,
      (forall (c : (Cutoff tm)) (k9 : Hvl) ,
        (shifthvl_tm c k8 k9) -> (wfTy k9 S13)))) := (ind_wfTy (fun (k8 : Hvl) (S13 : Ty) (wf : (wfTy k8 S13)) =>
    (forall (c : (Cutoff tm)) (k9 : Hvl) ,
      (shifthvl_tm c k8 k9) -> (wfTy k9 S13))) (fun (k8 : Hvl) (X19 : (Index ty)) (wfi : (wfindex k8 X19)) (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_tvar k9 _ (shift_wfindex_ty c k8 k9 ins X19 wfi))) (fun (k8 : Hvl) (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_top k9)) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_tarr k9 (IHT1 c k9 (weaken_shifthvl_tm H0 ins)) (IHT2 c k9 (weaken_shifthvl_tm H0 ins)))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS ty k8) T2)) IHT2 (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTy_tall k9 (IHT1 c k9 (weaken_shifthvl_tm H0 ins)) (IHT2 c (HS ty k9) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k8 : Hvl) ,
    (forall (S13 : Ty) (wf : (wfTy k8 S13)) ,
      (forall (c : (Cutoff ty)) (k9 : Hvl) ,
        (shifthvl_ty c k8 k9) -> (wfTy k9 (tshiftTy c S13))))) := (ind_wfTy (fun (k8 : Hvl) (S13 : Ty) (wf : (wfTy k8 S13)) =>
    (forall (c : (Cutoff ty)) (k9 : Hvl) ,
      (shifthvl_ty c k8 k9) -> (wfTy k9 (tshiftTy c S13)))) (fun (k8 : Hvl) (X19 : (Index ty)) (wfi : (wfindex k8 X19)) (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_tvar k9 _ (tshift_wfindex_ty c k8 k9 ins X19 wfi))) (fun (k8 : Hvl) (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_top k9)) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_tarr k9 (IHT1 c k9 (weaken_shifthvl_ty H0 ins)) (IHT2 c k9 (weaken_shifthvl_ty H0 ins)))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS ty k8) T2)) IHT2 (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTy_tall k9 (IHT1 c k9 (weaken_shifthvl_ty H0 ins)) (IHT2 (CS c) (HS ty k9) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k8 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k8 s4)) ,
      (forall (c : (Cutoff tm)) (k9 : Hvl) ,
        (shifthvl_tm c k8 k9) -> (wfTm k9 (shiftTm c s4))))) := (ind_wfTm (fun (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) =>
    (forall (c : (Cutoff tm)) (k9 : Hvl) ,
      (shifthvl_tm c k8 k9) -> (wfTm k9 (shiftTm c s4)))) (fun (k8 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k8 x6)) (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_var k9 _ (shift_wfindex_tm c k8 k9 ins x6 wfi))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS tm k8) t)) IHt (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_abs k9 (shift_wfTy k8 T wf c k9 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k9) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k8 : Hvl) (t1 : Tm) (wf : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k8 t2)) IHt2 (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_app k9 (IHt1 c k9 (weaken_shifthvl_tm H0 ins)) (IHt2 c k9 (weaken_shifthvl_tm H0 ins)))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS ty k8) t)) IHt (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_tabs k9 (shift_wfTy k8 T wf c k9 (weaken_shifthvl_tm H0 ins)) (IHt c (HS ty k9) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm k8 t)) IHt (T : Ty) (wf0 : (wfTy k8 T)) (c : (Cutoff tm)) (k9 : Hvl) (ins : (shifthvl_tm c k8 k9)) =>
    (wfTm_tapp k9 (IHt c k9 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k8 T wf0 c k9 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k8 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k8 s4)) ,
      (forall (c : (Cutoff ty)) (k9 : Hvl) ,
        (shifthvl_ty c k8 k9) -> (wfTm k9 (tshiftTm c s4))))) := (ind_wfTm (fun (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) =>
    (forall (c : (Cutoff ty)) (k9 : Hvl) ,
      (shifthvl_ty c k8 k9) -> (wfTm k9 (tshiftTm c s4)))) (fun (k8 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k8 x6)) (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_var k9 _ (tshift_wfindex_tm c k8 k9 ins x6 wfi))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS tm k8) t)) IHt (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_abs k9 (tshift_wfTy k8 T wf c k9 (weaken_shifthvl_ty H0 ins)) (IHt c (HS tm k9) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k8 : Hvl) (t1 : Tm) (wf : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k8 t2)) IHt2 (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_app k9 (IHt1 c k9 (weaken_shifthvl_ty H0 ins)) (IHt2 c k9 (weaken_shifthvl_ty H0 ins)))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS ty k8) t)) IHt (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_tabs k9 (tshift_wfTy k8 T wf c k9 (weaken_shifthvl_ty H0 ins)) (IHt (CS c) (HS ty k9) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm k8 t)) IHt (T : Ty) (wf0 : (wfTy k8 T)) (c : (Cutoff ty)) (k9 : Hvl) (ins : (shifthvl_ty c k8 k9)) =>
    (wfTm_tapp k9 (IHt c k9 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k8 T wf0 c k9 (weaken_shifthvl_ty H0 ins))))).
  Fixpoint weaken_wfTy (k8 : Hvl) {struct k8} :
  (forall (k9 : Hvl) (S13 : Ty) (wf : (wfTy k9 S13)) ,
    (wfTy (appendHvl k9 k8) (weakenTy S13 k8))) :=
    match k8 return (forall (k9 : Hvl) (S13 : Ty) (wf : (wfTy k9 S13)) ,
      (wfTy (appendHvl k9 k8) (weakenTy S13 k8))) with
      | (H0) => (fun (k9 : Hvl) (S13 : Ty) (wf : (wfTy k9 S13)) =>
        wf)
      | (HS tm k8) => (fun (k9 : Hvl) (S13 : Ty) (wf : (wfTy k9 S13)) =>
        (shift_wfTy (appendHvl k9 k8) (weakenTy S13 k8) (weaken_wfTy k8 k9 S13 wf) C0 (HS tm (appendHvl k9 k8)) (shifthvl_tm_here (appendHvl k9 k8))))
      | (HS ty k8) => (fun (k9 : Hvl) (S13 : Ty) (wf : (wfTy k9 S13)) =>
        (tshift_wfTy (appendHvl k9 k8) (weakenTy S13 k8) (weaken_wfTy k8 k9 S13 wf) C0 (HS ty (appendHvl k9 k8)) (shifthvl_ty_here (appendHvl k9 k8))))
    end.
  Fixpoint weaken_wfTm (k8 : Hvl) {struct k8} :
  (forall (k9 : Hvl) (s4 : Tm) (wf : (wfTm k9 s4)) ,
    (wfTm (appendHvl k9 k8) (weakenTm s4 k8))) :=
    match k8 return (forall (k9 : Hvl) (s4 : Tm) (wf : (wfTm k9 s4)) ,
      (wfTm (appendHvl k9 k8) (weakenTm s4 k8))) with
      | (H0) => (fun (k9 : Hvl) (s4 : Tm) (wf : (wfTm k9 s4)) =>
        wf)
      | (HS tm k8) => (fun (k9 : Hvl) (s4 : Tm) (wf : (wfTm k9 s4)) =>
        (shift_wfTm (appendHvl k9 k8) (weakenTm s4 k8) (weaken_wfTm k8 k9 s4 wf) C0 (HS tm (appendHvl k9 k8)) (shifthvl_tm_here (appendHvl k9 k8))))
      | (HS ty k8) => (fun (k9 : Hvl) (s4 : Tm) (wf : (wfTm k9 s4)) =>
        (tshift_wfTm (appendHvl k9 k8) (weakenTm s4 k8) (weaken_wfTm k8 k9 s4 wf) C0 (HS ty (appendHvl k9 k8)) (shifthvl_ty_here (appendHvl k9 k8))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k8 : Hvl) (S13 : Ty) (k9 : Hvl) (S14 : Ty) ,
    (k8 = k9) -> (S13 = S14) -> (wfTy k8 S13) -> (wfTy k9 S14)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k8 : Hvl) (s4 : Tm) (k9 : Hvl) (s5 : Tm) ,
    (k8 = k9) -> (s4 = s5) -> (wfTm k8 s4) -> (wfTm k9 s5)).
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
  Lemma substhvl_tm_wfindex_tm {k8 : Hvl} {s4 : Tm} (wft : (wfTm k8 s4)) :
    (forall {d : (Trace tm)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (forall {x6 : (Index tm)} ,
        (wfindex k9 x6) -> (wfTm k10 (substIndex d s4 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k8 : Hvl} {S13 : Ty} (wft : (wfTy k8 S13)) :
    (forall {d : (Trace ty)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (forall {X19 : (Index ty)} ,
        (wfindex k9 X19) -> (wfTy k10 (tsubstIndex d S13 X19)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k8 : Hvl} :
    (forall {d : (Trace tm)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (forall {X19 : (Index ty)} ,
        (wfindex k9 X19) -> (wfindex k10 X19))).
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
  Definition substhvl_tm_wfTy {k8 : Hvl} : (forall (k9 : Hvl) ,
    (forall (S13 : Ty) (wf0 : (wfTy k9 S13)) ,
      (forall {d : (Trace tm)} {k10 : Hvl} ,
        (substhvl_tm k8 d k9 k10) -> (wfTy k10 S13)))) := (ind_wfTy (fun (k9 : Hvl) (S13 : Ty) (wf0 : (wfTy k9 S13)) =>
    (forall {d : (Trace tm)} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (wfTy k10 S13))) (fun (k9 : Hvl) {X19 : (Index ty)} (wfi : (wfindex k9 X19)) {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_tvar k10 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k9 : Hvl) {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_top k10)) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_tarr k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS ty k9) T2)) IHT2 {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTy_tall k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d (HS ty H0)) (HS ty k10) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k8 : Hvl} {S13 : Ty} (wf : (wfTy k8 S13)) : (forall (k9 : Hvl) ,
    (forall (S14 : Ty) (wf0 : (wfTy k9 S14)) ,
      (forall {d : (Trace ty)} {k10 : Hvl} ,
        (substhvl_ty k8 d k9 k10) -> (wfTy k10 (tsubstTy d S13 S14))))) := (ind_wfTy (fun (k9 : Hvl) (S14 : Ty) (wf0 : (wfTy k9 S14)) =>
    (forall {d : (Trace ty)} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (wfTy k10 (tsubstTy d S13 S14)))) (fun (k9 : Hvl) {X19 : (Index ty)} (wfi : (wfindex k9 X19)) {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k9 : Hvl) {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTy_top k10)) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTy_tarr k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS ty k9) T2)) IHT2 {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTy_tall k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d (HS ty H0)) (HS ty k10) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k8 : Hvl} {s4 : Tm} (wf : (wfTm k8 s4)) : (forall (k9 : Hvl) ,
    (forall (s5 : Tm) (wf0 : (wfTm k9 s5)) ,
      (forall {d : (Trace tm)} {k10 : Hvl} ,
        (substhvl_tm k8 d k9 k10) -> (wfTm k10 (substTm d s4 s5))))) := (ind_wfTm (fun (k9 : Hvl) (s5 : Tm) (wf0 : (wfTm k9 s5)) =>
    (forall {d : (Trace tm)} {k10 : Hvl} ,
      (substhvl_tm k8 d k9 k10) -> (wfTm k10 (substTm d s4 s5)))) (fun (k9 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k9 x6)) {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS tm k9) t)) IHt {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTm_abs k10 (substhvl_tm_wfTy k9 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k10) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k9 : Hvl) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k9 t2)) IHt2 {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTm_app k10 (IHt1 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS ty k9) t)) IHt {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTm_tabs k10 (substhvl_tm_wfTy k9 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS ty H0)) (HS ty k10) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm k9 t)) IHt (T : Ty) (wf1 : (wfTy k9 T)) {d : (Trace tm)} {k10 : Hvl} (del : (substhvl_tm k8 d k9 k10)) =>
    (wfTm_tapp k10 (IHt (weakenTrace d H0) k10 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k9 T wf1 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k8 : Hvl} {S13 : Ty} (wf : (wfTy k8 S13)) : (forall (k9 : Hvl) ,
    (forall (s4 : Tm) (wf0 : (wfTm k9 s4)) ,
      (forall {d : (Trace ty)} {k10 : Hvl} ,
        (substhvl_ty k8 d k9 k10) -> (wfTm k10 (tsubstTm d S13 s4))))) := (ind_wfTm (fun (k9 : Hvl) (s4 : Tm) (wf0 : (wfTm k9 s4)) =>
    (forall {d : (Trace ty)} {k10 : Hvl} ,
      (substhvl_ty k8 d k9 k10) -> (wfTm k10 (tsubstTm d S13 s4)))) (fun (k9 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k9 x6)) {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_var k10 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS tm k9) t)) IHt {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_abs k10 (substhvl_ty_wfTy wf k9 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k10) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k9 : Hvl) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k9 t2)) IHt2 {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_app k10 (IHt1 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS ty k9) t)) IHt {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_tabs k10 (substhvl_ty_wfTy wf k9 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS ty H0)) (HS ty k10) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm k9 t)) IHt (T : Ty) (wf1 : (wfTy k9 T)) {d : (Trace ty)} {k10 : Hvl} (del : (substhvl_ty k8 d k9 k10)) =>
    (wfTm_tapp k10 (IHt (weakenTrace d H0) k10 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k9 T wf1 (weaken_substhvl_ty H0 del))))).
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
    | etvar (G : Env) (T : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1 T) => (etvar (appendEnv G G1) T)
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0 T) => (HS ty (domainEnv G0))
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
      | (etvar G0 T) => (etvar (shiftEnv c G0) T)
    end.
  Fixpoint tshiftEnv (c : (Cutoff ty)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c G0) (tshiftTy (weakenCutoffty c (domainEnv G0)) T))
      | (etvar G0 T) => (etvar (tshiftEnv c G0) (tshiftTy (weakenCutoffty c (domainEnv G0)) T))
    end.
  Fixpoint weakenEnv (G : Env) (k8 : Hvl) {struct k8} :
  Env :=
    match k8 with
      | (H0) => G
      | (HS tm k8) => (weakenEnv G k8)
      | (HS ty k8) => (tshiftEnv C0 (weakenEnv G k8))
    end.
  Fixpoint substEnv (d : (Trace tm)) (s4 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s4 G0) T)
      | (etvar G0 T) => (etvar (substEnv d s4 G0) T)
    end.
  Fixpoint tsubstEnv (d : (Trace ty)) (S13 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d S13 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S13 T))
      | (etvar G0 T) => (etvar (tsubstEnv d S13 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S13 T))
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
    (forall (d : (Trace ty)) (S13 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d S13 G)) = (domainEnv G))).
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
      (forall (d : (Trace ty)) (S13 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d S13 (appendEnv G G0)) = (appendEnv (tsubstEnv d S13 G) (tsubstEnv (weakenTrace d (domainEnv G)) S13 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S13 : Ty) (k8 : Hvl) (k9 : Hvl) ,
      ((weakenTy (weakenTy S13 k8) k9) = (weakenTy S13 (appendHvl k8 k9)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s4 : Tm) (k8 : Hvl) (k9 : Hvl) ,
      ((weakenTm (weakenTm s4 k8) k9) = (weakenTm s4 (appendHvl k8 k9)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T49 : Ty) :
          (wfTy (domainEnv G) T49) -> (lookup_evar (evar G T49) I0 T49)
      | lookup_evar_there_evar
          {G : Env} {x6 : (Index tm)}
          (T50 : Ty) (T51 : Ty) :
          (lookup_evar G x6 T50) -> (lookup_evar (evar G T51) (IS x6) T50)
      | lookup_evar_there_etvar
          {G : Env} {x6 : (Index tm)}
          (T50 : Ty) (T51 : Ty) :
          (lookup_evar G x6 T50) -> (lookup_evar (etvar G T51) x6 (tshiftTy C0 T50)).
    Inductive lookup_etvar : Env -> (Index ty) -> Ty -> Prop :=
      | lookup_etvar_here {G : Env}
          (T50 : Ty) :
          (wfTy (domainEnv G) T50) -> (lookup_etvar (etvar G T50) I0 (tshiftTy C0 T50))
      | lookup_etvar_there_evar
          {G : Env} {X19 : (Index ty)}
          (T51 : Ty) (T52 : Ty) :
          (lookup_etvar G X19 T51) -> (lookup_etvar (evar G T52) X19 T51)
      | lookup_etvar_there_etvar
          {G : Env} {X19 : (Index ty)}
          (T51 : Ty) (T52 : Ty) :
          (lookup_etvar G X19 T51) -> (lookup_etvar (etvar G T52) (IS X19) (tshiftTy C0 T51)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T51 : Ty) (T52 : Ty) ,
        (lookup_evar (evar G T51) I0 T52) -> (T51 = T52)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (T51 : Ty) (T52 : Ty) ,
        (lookup_etvar (etvar G T51) I0 T52) -> ((tshiftTy C0 T51) = T52)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x6 : (Index tm)} ,
        (forall (T51 : Ty) ,
          (lookup_evar G x6 T51) -> (forall (T52 : Ty) ,
            (lookup_evar G x6 T52) -> (T51 = T52)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X19 : (Index ty)} ,
        (forall (T51 : Ty) ,
          (lookup_etvar G X19 T51) -> (forall (T52 : Ty) ,
            (lookup_etvar G X19 T52) -> (T51 = T52)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x6 : (Index tm)} (T51 : Ty) ,
        (lookup_evar G x6 T51) -> (wfTy (domainEnv G) T51)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X19 : (Index ty)} (T51 : Ty) ,
        (lookup_etvar G X19 T51) -> (wfTy (domainEnv G) T51)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x6 : (Index tm)} (T51 : Ty) ,
        (lookup_evar G x6 T51) -> (lookup_evar (appendEnv G G0) (weakenIndextm x6 (domainEnv G0)) (weakenTy T51 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X19 : (Index ty)} (T51 : Ty) ,
        (lookup_etvar G X19 T51) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X19 (domainEnv G0)) (weakenTy T51 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x6 : (Index tm)} (T55 : Ty) ,
        (lookup_evar G x6 T55) -> (wfindex (domainEnv G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X19 : (Index ty)} (T55 : Ty) ,
        (lookup_etvar G X19 T55) -> (wfindex (domainEnv G) X19)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T51 : Ty} :
        (shift_evar C0 G (evar G T51))
    | shiftevar_there_evar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar c (etvar G T) (etvar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutofftm c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {T51 : Ty} :
        (shift_etvar C0 G (etvar G T51))
    | shiftetvar_there_evar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (tshiftTy c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G T) (etvar G0 (tshiftTy c T))).
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
  Inductive subst_evar (G : Env) (T51 : Ty) (s4 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T51 s4 X0 (evar G T51) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T52 : Ty) :
        (subst_evar G T51 s4 d G0 G1) -> (subst_evar G T51 s4 (XS tm d) (evar G0 T52) (evar G1 T52))
    | subst_evar_there_etvar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T52 : Ty) :
        (subst_evar G T51 s4 d G0 G1) -> (subst_evar G T51 s4 (XS ty d) (etvar G0 T52) (etvar G1 T52)).
  Lemma weaken_subst_evar {G : Env} (T51 : Ty) {s4 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T51 s4 d G1 G2) -> (subst_evar G T51 s4 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (T51 : Ty) (S13 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G T51 S13 X0 (etvar G T51) G)
    | subst_etvar_there_evar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T52 : Ty) :
        (subst_etvar G T51 S13 d G0 G1) -> (subst_etvar G T51 S13 (XS tm d) (evar G0 T52) (evar G1 (tsubstTy d S13 T52)))
    | subst_etvar_there_etvar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T52 : Ty) :
        (subst_etvar G T51 S13 d G0 G1) -> (subst_etvar G T51 S13 (XS ty d) (etvar G0 T52) (etvar G1 (tsubstTy d S13 T52))).
  Lemma weaken_subst_etvar {G : Env} (T51 : Ty) {S13 : Ty} :
    (forall (G0 : Env) {d : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G T51 S13 d G1 G2) -> (subst_etvar G T51 S13 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d S13 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s4 : Tm} (T51 : Ty) :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T51 s4 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S13 : Ty} (T52 : Ty) :
    (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G T52 S13 d G0 G1) -> (substhvl_ty (domainEnv G) d (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T51 : Ty} (wf : (wfTy (domainEnv G) T51)) ,
    (lookup_evar (appendEnv (evar G T51) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T51 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {T51 : Ty} (wf : (wfTy (domainEnv G) T51)) ,
    (lookup_etvar (appendEnv (etvar G T51) G0) (weakenIndexty I0 (domainEnv G0)) (weakenTy (tshiftTy C0 T51) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTm wfTy : infra.
 Hint Constructors wfTm wfTy : wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H32 : (wfTy _ (tvar _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (top)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (tarr _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (tall _ _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H32 : (wfTm _ (var _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (abs _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (app _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (tabs _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (tapp _ _)) |- _ => inversion H32; subst; clear H32
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
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x6 : (Index tm)} {T51 : Ty} ,
    (lookup_evar G x6 T51) -> (lookup_evar G0 (shiftIndex c x6) T51)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X19 : (Index ty)} {T51 : Ty} ,
    (lookup_etvar G X19 T51) -> (lookup_etvar G0 X19 T51)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x6 : (Index tm)} {T51 : Ty} ,
    (lookup_evar G x6 T51) -> (lookup_evar G0 x6 (tshiftTy c T51))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X19 : (Index ty)} {T51 : Ty} ,
    (lookup_etvar G X19 T51) -> (lookup_etvar G0 (tshiftIndex c X19) (tshiftTy c T51))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T53 : Ty) {s4 : Tm} :
  (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T53 s4 d G0 G1)) {X19 : (Index ty)} (T54 : Ty) ,
    (lookup_etvar G0 X19 T54) -> (lookup_etvar G1 X19 T54)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} (T53 : Ty) {S13 : Ty} (wf : (wfTy (domainEnv G) S13)) :
  (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G T53 S13 d G0 G1)) {x6 : (Index tm)} (T54 : Ty) ,
    (lookup_evar G0 x6 T54) -> (lookup_evar G1 x6 (tsubstTy d S13 T54))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S9 : Ty) {struct S9} :
nat :=
  match S9 with
    | (tvar X19) => 1
    | (top) => 1
    | (tarr T49 T50) => (plus 1 (plus (size_Ty T49) (size_Ty T50)))
    | (tall T51 T52) => (plus 1 (plus (size_Ty T51) (size_Ty T52)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x6) => 1
    | (abs T49 t17) => (plus 1 (plus (size_Ty T49) (size_Tm t17)))
    | (app t18 t19) => (plus 1 (plus (size_Tm t18) (size_Tm t19)))
    | (tabs T50 t20) => (plus 1 (plus (size_Ty T50) (size_Tm t20)))
    | (tapp t21 T51) => (plus 1 (plus (size_Tm t21) (size_Ty T51)))
  end.
Fixpoint tshift_size_Ty (S9 : Ty) (c : (Cutoff ty)) {struct S9} :
((size_Ty (tshiftTy c S9)) = (size_Ty S9)) :=
  match S9 return ((size_Ty (tshiftTy c S9)) = (size_Ty S9)) with
    | (tvar _) => eq_refl
    | (top) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tall T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 (CS c))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t c)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c) eq_refl))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t (CS c))))
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
  (forall (k : Hvl) (S9 : Ty) ,
    ((size_Ty (weakenTy S9 k)) = (size_Ty S9))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive Sub (G : Env) : Ty -> Ty -> Prop :=
  | SA_Top (S1 : Ty)
      (H19 : (wfTy (domainEnv G) S1))
      : (Sub G S1 (top))
  | SA_Refl_TVar (X : (Index ty))
      (H20 : (wfindex (domainEnv G) X))
      : (Sub G (tvar X) (tvar X))
  | SA_Trans_TVar (T : Ty)
      (U : Ty) (X : (Index ty))
      (lk : (lookup_etvar G X U))
      (jm : (Sub G U T))
      (H23 : (wfindex (domainEnv G) X))
      : (Sub G (tvar X) T)
  | SA_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm0 : (Sub G T1 S1))
      (jm1 : (Sub G S2 T2)) :
      (Sub G (tarr S1 S2) (tarr T1 T2))
  | SA_All (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm2 : (Sub G T1 S1))
      (jm3 : (Sub (etvar G T1) S2 T2))
      :
      (Sub G (tall S1 S2) (tall T1 T2)).
Inductive Typing (G : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (y : (Index tm))
      (lk : (lookup_evar G y T))
      (H19 : (wfTy (domainEnv G) T))
      (H20 : (wfindex (domainEnv G) y))
      : (Typing G (var y) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm4 : (Typing (evar G T1) t (weakenTy T2 (HS tm H0))))
      (H21 : (wfTy (domainEnv G) T1))
      (H22 : (wfTy (domainEnv G) T2))
      :
      (Typing G (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm5 : (Typing G t1 (tarr T11 T12)))
      (jm6 : (Typing G t2 T11)) :
      (Typing G (app t1 t2) T12)
  | T_Tabs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm7 : (Typing (etvar G T1) t T2))
      (H28 : (wfTy (domainEnv G) T1))
      :
      (Typing G (tabs T1 t) (tall T1 T2))
  | T_Tapp (T11 : Ty) (T12 : Ty)
      (T2 : Ty) (t1 : Tm)
      (jm8 : (Typing G t1 (tall T11 T12)))
      (jm9 : (Sub G T2 T11)) :
      (Typing G (tapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Sub (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm10 : (Typing G t T1))
      (jm11 : (Sub G T1 T2)) :
      (Typing G t T2).
Lemma Sub_cast  :
  (forall (G : Env) (T55 : Ty) (T56 : Ty) (G0 : Env) (T57 : Ty) (T58 : Ty) ,
    (G = G0) -> (T55 = T57) -> (T56 = T58) -> (Sub G T55 T56) -> (Sub G0 T57 T58)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G : Env) (t17 : Tm) (T55 : Ty) (G0 : Env) (t18 : Tm) (T56 : Ty) ,
    (G = G0) -> (t17 = t18) -> (T55 = T56) -> (Typing G t17 T55) -> (Typing G0 t18 T56)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_Sub (G3 : Env) (T65 : Ty) (T66 : Ty) (jm19 : (Sub G3 T65 T66)) :
(forall (c : (Cutoff tm)) (G4 : Env) (H55 : (shift_evar c G3 G4)) ,
  (Sub G4 T65 T66)) :=
  match jm19 in (Sub _ T65 T66) return (forall (c : (Cutoff tm)) (G4 : Env) (H55 : (shift_evar c G3 G4)) ,
    (Sub G4 T65 T66)) with
    | (SA_Top S13 H40) => (fun (c : (Cutoff tm)) (G4 : Env) (H55 : (shift_evar c G3 G4)) =>
      (SA_Top G4 S13 (shift_wfTy _ _ H40 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H55)))))
    | (SA_Refl_TVar X21 H41) => (fun (c : (Cutoff tm)) (G4 : Env) (H55 : (shift_evar c G3 G4)) =>
      (SA_Refl_TVar G4 X21 (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H55)) _ H41)))
    | (SA_Trans_TVar T62 U1 X21 lk0 jm14 H44) => (fun (c : (Cutoff tm)) (G4 : Env) (H55 : (shift_evar c G3 G4)) =>
      (SA_Trans_TVar G4 T62 U1 X21 (shift_evar_lookup_etvar H55 lk0) (shift_evar_Sub G3 U1 T62 jm14 c G4 (weaken_shift_evar empty H55)) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H55)) _ H44)))
    | (SA_Arrow S13 S14 T63 T64 jm15 jm16) => (fun (c : (Cutoff tm)) (G4 : Env) (H55 : (shift_evar c G3 G4)) =>
      (SA_Arrow G4 S13 S14 T63 T64 (shift_evar_Sub G3 T63 S13 jm15 c G4 (weaken_shift_evar empty H55)) (shift_evar_Sub G3 S14 T64 jm16 c G4 (weaken_shift_evar empty H55))))
    | (SA_All S13 S14 T63 T64 jm17 jm18) => (fun (c : (Cutoff tm)) (G4 : Env) (H55 : (shift_evar c G3 G4)) =>
      (SA_All G4 S13 S14 T63 T64 (shift_evar_Sub G3 T63 S13 jm17 c G4 (weaken_shift_evar empty H55)) (shift_evar_Sub (etvar G3 T63) S14 T64 jm18 c (etvar G4 T63) (weaken_shift_evar (etvar empty T63) H55))))
  end.
Fixpoint shift_etvar_Sub (G3 : Env) (T65 : Ty) (T66 : Ty) (jm19 : (Sub G3 T65 T66)) :
(forall (c : (Cutoff ty)) (G4 : Env) (H55 : (shift_etvar c G3 G4)) ,
  (Sub G4 (tshiftTy c T65) (tshiftTy c T66))) :=
  match jm19 in (Sub _ T65 T66) return (forall (c : (Cutoff ty)) (G4 : Env) (H55 : (shift_etvar c G3 G4)) ,
    (Sub G4 (tshiftTy c T65) (tshiftTy c T66))) with
    | (SA_Top S13 H40) => (fun (c : (Cutoff ty)) (G4 : Env) (H55 : (shift_etvar c G3 G4)) =>
      (SA_Top G4 (tshiftTy c S13) (tshift_wfTy _ _ H40 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H55)))))
    | (SA_Refl_TVar X21 H41) => (fun (c : (Cutoff ty)) (G4 : Env) (H55 : (shift_etvar c G3 G4)) =>
      (SA_Refl_TVar G4 (tshiftIndex c X21) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H55)) _ H41)))
    | (SA_Trans_TVar T62 U1 X21 lk0 jm14 H44) => (fun (c : (Cutoff ty)) (G4 : Env) (H55 : (shift_etvar c G3 G4)) =>
      (SA_Trans_TVar G4 (tshiftTy c T62) (tshiftTy c U1) (tshiftIndex c X21) (shift_etvar_lookup_etvar H55 lk0) (shift_etvar_Sub G3 U1 T62 jm14 c G4 (weaken_shift_etvar empty H55)) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H55)) _ H44)))
    | (SA_Arrow S13 S14 T63 T64 jm15 jm16) => (fun (c : (Cutoff ty)) (G4 : Env) (H55 : (shift_etvar c G3 G4)) =>
      (SA_Arrow G4 (tshiftTy c S13) (tshiftTy c S14) (tshiftTy c T63) (tshiftTy c T64) (shift_etvar_Sub G3 T63 S13 jm15 c G4 (weaken_shift_etvar empty H55)) (shift_etvar_Sub G3 S14 T64 jm16 c G4 (weaken_shift_etvar empty H55))))
    | (SA_All S13 S14 T63 T64 jm17 jm18) => (fun (c : (Cutoff ty)) (G4 : Env) (H55 : (shift_etvar c G3 G4)) =>
      (SA_All G4 (tshiftTy c S13) (tshiftTy (CS c) S14) (tshiftTy c T63) (tshiftTy (CS c) T64) (shift_etvar_Sub G3 T63 S13 jm17 c G4 (weaken_shift_etvar empty H55)) (shift_etvar_Sub (etvar G3 T63) S14 T64 jm18 (CS c) (etvar G4 (tshiftTy c T63)) (weaken_shift_etvar (etvar empty T63) H55))))
  end.
Fixpoint shift_evar_Typing (G3 : Env) (t21 : Tm) (T67 : Ty) (jm22 : (Typing G3 t21 T67)) :
(forall (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) ,
  (Typing G4 (shiftTm c t21) T67)) :=
  match jm22 in (Typing _ t21 T67) return (forall (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) ,
    (Typing G4 (shiftTm c t21) T67)) with
    | (T_Var T62 y1 lk0 H40 H41) => (fun (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) =>
      (T_Var G4 T62 (shiftIndex c y1) (shift_evar_lookup_evar H61 lk0) (shift_wfTy _ _ H40 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61)) _ H41)))
    | (T_Abs T63 T66 t18 jm16 H42 H43) => (fun (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) =>
      (T_Abs G4 T63 T66 (shiftTm (CS c) t18) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G3 T63) t18 (weakenTy T66 (HS tm H0)) jm16 (CS c) (evar G4 T63) (weaken_shift_evar (evar empty T63) H61))) (shift_wfTy _ _ H42 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61))) (shift_wfTy _ _ H43 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61)))))
    | (T_App T64 T65 t19 t20 jm17 jm18) => (fun (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) =>
      (T_App G4 T64 T65 (shiftTm c t19) (shiftTm c t20) (shift_evar_Typing G3 t19 (tarr T64 T65) jm17 c G4 (weaken_shift_evar empty H61)) (shift_evar_Typing G3 t20 T64 jm18 c G4 (weaken_shift_evar empty H61))))
    | (T_Tabs T63 T66 t18 jm19 H49) => (fun (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) =>
      (T_Tabs G4 T63 T66 (shiftTm c t18) (shift_evar_Typing (etvar G3 T63) t18 T66 jm19 c (etvar G4 T63) (weaken_shift_evar (etvar empty T63) H61)) (shift_wfTy _ _ H49 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H61)))))
    | (T_Tapp T64 T65 T66 t19 jm20 jm21) => (fun (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) =>
      (T_Tapp G4 T64 T65 T66 (shiftTm c t19) (shift_evar_Typing G3 t19 (tall T64 T65) jm20 c G4 (weaken_shift_evar empty H61)) (shift_evar_Sub G3 T66 T64 jm21 c G4 (weaken_shift_evar empty H61))))
    | (T_Sub T63 T66 t18 jm14 jm15) => (fun (c : (Cutoff tm)) (G4 : Env) (H61 : (shift_evar c G3 G4)) =>
      (T_Sub G4 T63 T66 (shiftTm c t18) (shift_evar_Typing G3 t18 T63 jm14 c G4 (weaken_shift_evar empty H61)) (shift_evar_Sub G3 T63 T66 jm15 c G4 (weaken_shift_evar empty H61))))
  end.
Fixpoint shift_etvar_Typing (G3 : Env) (t21 : Tm) (T67 : Ty) (jm22 : (Typing G3 t21 T67)) :
(forall (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) ,
  (Typing G4 (tshiftTm c t21) (tshiftTy c T67))) :=
  match jm22 in (Typing _ t21 T67) return (forall (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) ,
    (Typing G4 (tshiftTm c t21) (tshiftTy c T67))) with
    | (T_Var T62 y1 lk0 H40 H41) => (fun (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) =>
      (T_Var G4 (tshiftTy c T62) y1 (shift_etvar_lookup_evar H61 lk0) (tshift_wfTy _ _ H40 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H61))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H61)) _ H41)))
    | (T_Abs T63 T66 t18 jm16 H42 H43) => (fun (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) =>
      (T_Abs G4 (tshiftTy c T63) (tshiftTy c T66) (tshiftTm c t18) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c T66)) (shift_etvar_Typing (evar G3 T63) t18 (weakenTy T66 (HS tm H0)) jm16 c (evar G4 (tshiftTy c T63)) (weaken_shift_etvar (evar empty T63) H61))) (tshift_wfTy _ _ H42 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H61))) (tshift_wfTy _ _ H43 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H61)))))
    | (T_App T64 T65 t19 t20 jm17 jm18) => (fun (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) =>
      (T_App G4 (tshiftTy c T64) (tshiftTy c T65) (tshiftTm c t19) (tshiftTm c t20) (shift_etvar_Typing G3 t19 (tarr T64 T65) jm17 c G4 (weaken_shift_etvar empty H61)) (shift_etvar_Typing G3 t20 T64 jm18 c G4 (weaken_shift_etvar empty H61))))
    | (T_Tabs T63 T66 t18 jm19 H49) => (fun (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) =>
      (T_Tabs G4 (tshiftTy c T63) (tshiftTy (CS c) T66) (tshiftTm (CS c) t18) (shift_etvar_Typing (etvar G3 T63) t18 T66 jm19 (CS c) (etvar G4 (tshiftTy c T63)) (weaken_shift_etvar (etvar empty T63) H61)) (tshift_wfTy _ _ H49 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H61)))))
    | (T_Tapp T64 T65 T66 t19 jm20 jm21) => (fun (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) =>
      (Typing_cast G4 _ _ G4 (tshiftTm c (tapp t19 T66)) (tshiftTy c (tsubstTy X0 T66 T65)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T65 c T66)) (T_Tapp G4 (tshiftTy c T64) (tshiftTy (CS c) T65) (tshiftTy c T66) (tshiftTm c t19) (shift_etvar_Typing G3 t19 (tall T64 T65) jm20 c G4 (weaken_shift_etvar empty H61)) (shift_etvar_Sub G3 T66 T64 jm21 c G4 (weaken_shift_etvar empty H61)))))
    | (T_Sub T63 T66 t18 jm14 jm15) => (fun (c : (Cutoff ty)) (G4 : Env) (H61 : (shift_etvar c G3 G4)) =>
      (T_Sub G4 (tshiftTy c T63) (tshiftTy c T66) (tshiftTm c t18) (shift_etvar_Typing G3 t18 T63 jm14 c G4 (weaken_shift_etvar empty H61)) (shift_etvar_Sub G3 T63 T66 jm15 c G4 (weaken_shift_etvar empty H61))))
  end.
 Hint Resolve shift_evar_Sub shift_etvar_Sub shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_Sub shift_etvar_Sub shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_Sub (G : Env) :
(forall (G0 : Env) (T55 : Ty) (T56 : Ty) (jm12 : (Sub G0 T55 T56)) ,
  (Sub (appendEnv G0 G) (weakenTy T55 (domainEnv G)) (weakenTy T56 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (T55 : Ty) (T56 : Ty) (jm12 : (Sub G0 T55 T56)) ,
    (Sub (appendEnv G0 G) (weakenTy T55 (domainEnv G)) (weakenTy T56 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (T55 : Ty) (T56 : Ty) (jm12 : (Sub G0 T55 T56)) =>
      jm12)
    | (evar G T57) => (fun (G0 : Env) (T55 : Ty) (T56 : Ty) (jm12 : (Sub G0 T55 T56)) =>
      (shift_evar_Sub (appendEnv G0 G) (weakenTy T55 (domainEnv G)) (weakenTy T56 (domainEnv G)) (weaken_Sub G G0 T55 T56 jm12) C0 (evar (appendEnv G0 G) T57) shift_evar_here))
    | (etvar G T58) => (fun (G0 : Env) (T55 : Ty) (T56 : Ty) (jm12 : (Sub G0 T55 T56)) =>
      (shift_etvar_Sub (appendEnv G0 G) (weakenTy T55 (domainEnv G)) (weakenTy T56 (domainEnv G)) (weaken_Sub G G0 T55 T56 jm12) C0 (etvar (appendEnv G0 G) T58) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G1 : Env) :
(forall (G2 : Env) (t17 : Tm) (T59 : Ty) (jm13 : (Typing G2 t17 T59)) ,
  (Typing (appendEnv G2 G1) (weakenTm t17 (domainEnv G1)) (weakenTy T59 (domainEnv G1)))) :=
  match G1 return (forall (G2 : Env) (t17 : Tm) (T59 : Ty) (jm13 : (Typing G2 t17 T59)) ,
    (Typing (appendEnv G2 G1) (weakenTm t17 (domainEnv G1)) (weakenTy T59 (domainEnv G1)))) with
    | (empty) => (fun (G2 : Env) (t17 : Tm) (T59 : Ty) (jm13 : (Typing G2 t17 T59)) =>
      jm13)
    | (evar G1 T60) => (fun (G2 : Env) (t17 : Tm) (T59 : Ty) (jm13 : (Typing G2 t17 T59)) =>
      (shift_evar_Typing (appendEnv G2 G1) (weakenTm t17 (domainEnv G1)) (weakenTy T59 (domainEnv G1)) (weaken_Typing G1 G2 t17 T59 jm13) C0 (evar (appendEnv G2 G1) T60) shift_evar_here))
    | (etvar G1 T61) => (fun (G2 : Env) (t17 : Tm) (T59 : Ty) (jm13 : (Typing G2 t17 T59)) =>
      (shift_etvar_Typing (appendEnv G2 G1) (weakenTm t17 (domainEnv G1)) (weakenTy T59 (domainEnv G1)) (weaken_Typing G1 G2 t17 T59 jm13) C0 (etvar (appendEnv G2 G1) T61) shift_etvar_here))
  end.
Fixpoint Sub_wf_0 (G : Env) (T62 : Ty) (T63 : Ty) (jm14 : (Sub G T62 T63)) {struct jm14} :
(wfTy (domainEnv G) T62) :=
  match jm14 in (Sub _ T62 T63) return (wfTy (domainEnv G) T62) with
    | (SA_Top S1 H19) => H19
    | (SA_Refl_TVar X H20) => (wfTy_tvar (domainEnv G) _ H20)
    | (SA_Trans_TVar T U X lk jm H23) => (wfTy_tvar (domainEnv G) _ H23)
    | (SA_Arrow S1 S2 T1 T2 jm0 jm1) => (wfTy_tarr (domainEnv G) (Sub_wf_1 G T1 S1 jm0) (Sub_wf_0 G S2 T2 jm1))
    | (SA_All S1 S2 T1 T2 jm2 jm3) => (wfTy_tall (domainEnv G) (Sub_wf_1 G T1 S1 jm2) (Sub_wf_0 (etvar G T1) S2 T2 jm3))
  end
with Sub_wf_1 (G : Env) (T62 : Ty) (T63 : Ty) (jm15 : (Sub G T62 T63)) {struct jm15} :
(wfTy (domainEnv G) T63) :=
  match jm15 in (Sub _ T62 T63) return (wfTy (domainEnv G) T63) with
    | (SA_Top S1 H19) => (wfTy_top (domainEnv G))
    | (SA_Refl_TVar X H20) => (wfTy_tvar (domainEnv G) _ H20)
    | (SA_Trans_TVar T U X lk jm H23) => (Sub_wf_1 G U T jm)
    | (SA_Arrow S1 S2 T1 T2 jm0 jm1) => (wfTy_tarr (domainEnv G) (Sub_wf_0 G T1 S1 jm0) (Sub_wf_1 G S2 T2 jm1))
    | (SA_All S1 S2 T1 T2 jm2 jm3) => (wfTy_tall (domainEnv G) (Sub_wf_0 G T1 S1 jm2) (Sub_wf_1 (etvar G T1) S2 T2 jm3))
  end.
Fixpoint Typing_wf_0 (G : Env) (t18 : Tm) (T64 : Ty) (jm16 : (Typing G t18 T64)) {struct jm16} :
(wfTm (domainEnv G) t18) :=
  match jm16 in (Typing _ t18 T64) return (wfTm (domainEnv G) t18) with
    | (T_Var T y lk0 H19 H20) => (wfTm_var (domainEnv G) _ H20)
    | (T_Abs T1 T2 t jm4 H21 H22) => (wfTm_abs (domainEnv G) H21 (Typing_wf_0 (evar G T1) t (weakenTy T2 (HS tm H0)) jm4))
    | (T_App T11 T12 t1 t2 jm5 jm6) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tarr T11 T12) jm5) (Typing_wf_0 G t2 T11 jm6))
    | (T_Tabs T1 T2 t jm7 H28) => (wfTm_tabs (domainEnv G) H28 (Typing_wf_0 (etvar G T1) t T2 jm7))
    | (T_Tapp T11 T12 T2 t1 jm8 jm9) => (wfTm_tapp (domainEnv G) (Typing_wf_0 G t1 (tall T11 T12) jm8) (Sub_wf_0 G T2 T11 jm9))
    | (T_Sub T1 T2 t jm10 jm11) => (Typing_wf_0 G t T1 jm10)
  end
with Typing_wf_1 (G : Env) (t18 : Tm) (T64 : Ty) (jm17 : (Typing G t18 T64)) {struct jm17} :
(wfTy (domainEnv G) T64) :=
  match jm17 in (Typing _ t18 T64) return (wfTy (domainEnv G) T64) with
    | (T_Var T y lk1 H19 H20) => H19
    | (T_Abs T1 T2 t jm4 H21 H22) => (wfTy_tarr (domainEnv G) H21 H22)
    | (T_App T11 T12 t1 t2 jm5 jm6) => (inversion_wfTy_tarr_1 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tarr T11 T12) jm5))
    | (T_Tabs T1 T2 t jm7 H28) => (wfTy_tall (domainEnv G) H28 (Typing_wf_1 (etvar G T1) t T2 jm7))
    | (T_Tapp T11 T12 T2 t1 jm8 jm9) => (substhvl_ty_wfTy (Sub_wf_0 G T2 T11 jm9) (HS ty (domainEnv G)) T12 (inversion_wfTy_tall_2 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tall T11 T12) jm8)) (substhvl_ty_here (domainEnv G)))
    | (T_Sub T1 T2 t jm10 jm11) => (Sub_wf_1 G T1 T2 jm11)
  end.
 Hint Extern 8 => match goal with
  | H44 : (Sub _ _ _) |- _ => pose proof ((Sub_wf_0 _ _ _ H44)); pose proof ((Sub_wf_1 _ _ _ H44)); clear H44
end : wf.
 Hint Extern 8 => match goal with
  | H45 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H45)); pose proof ((Typing_wf_1 _ _ _ H45)); clear H45
end : wf.
Class Obligation_Env_var_ty : Prop := { Env_var_ty (G3 : Env) (X21 : (Index ty)) (T : Ty) : (lookup_etvar G3 X21 T) -> (Sub G3 (tvar X21) T) }.
Context {obligation_Env_var_ty : Obligation_Env_var_ty} .
Lemma subst_evar_lookup_evar (G4 : Env) (s4 : Tm) (T65 : Ty) (jm18 : (Typing G4 s4 T65)) :
  (forall (d : (Trace tm)) (G5 : Env) (G7 : Env) (sub : (subst_evar G4 T65 s4 d G5 G7)) (x8 : (Index tm)) (T66 : Ty) ,
    (lookup_evar G5 x8 T66) -> (Typing G7 (substIndex d s4 x8) T66)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Lemma subst_etvar_lookup_etvar (G4 : Env) (S13 : Ty) (T65 : Ty) (jm18 : (Sub G4 S13 T65)) :
  (forall (d : (Trace ty)) (G5 : Env) (G7 : Env) (sub : (subst_etvar G4 T65 S13 d G5 G7)) (X22 : (Index ty)) (T66 : Ty) ,
    (lookup_etvar G5 X22 T66) -> (Sub G7 (tsubstIndex d S13 X22) (tsubstTy d S13 T66))).
Proof.
  needleGenericSubstEnvLookupHom (Env_var_ty).
Qed.
Class Obligation_Env_reg_Sub : Prop := { Env_reg_SA_Refl_TVar (G : Env) (S13 : Ty) (H46 : (wfTy (domainEnv G) S13)) : (Sub G (weakenTy S13 H0) (weakenTy S13 H0)) ; Env_reg_SA_Trans_TVar (G : Env) (T : Ty) (U : Ty) (S14 : Ty) (jm18 : (Sub G S14 U)) (jm : (Sub G U T)) (H47 : (wfTy (domainEnv G) S14)) : (Sub G (weakenTy S14 H0) T) }.
Context {obligation_Env_reg_Sub : Obligation_Env_reg_Sub} .
Fixpoint subst_evar_Sub (G5 : Env) (s4 : Tm) (T65 : Ty) (jm24 : (Typing G5 s4 T65)) (G4 : Env) (T1 : Ty) (T2 : Ty) (jm25 : (Sub G4 T1 T2)) :
(forall (G6 : Env) (d : (Trace tm)) (H62 : (subst_evar G5 T65 s4 d G4 G6)) ,
  (Sub G6 T1 T2)) :=
  match jm25 in (Sub _ T1 T2) return (forall (G6 : Env) (d : (Trace tm)) (H62 : (subst_evar G5 T65 s4 d G4 G6)) ,
    (Sub G6 T1 T2)) with
    | (SA_Top S15 H49) => (fun (G6 : Env) (d : (Trace tm)) (H62 : (subst_evar G5 T65 s4 d G4 G6)) =>
      (SA_Top G6 S15 (substhvl_tm_wfTy _ _ H49 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62)))))
    | (SA_Refl_TVar X22 H50) => (fun (G6 : Env) (d : (Trace tm)) (H62 : (subst_evar G5 T65 s4 d G4 G6)) =>
      (SA_Refl_TVar G6 X22 (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62)) H50)))
    | (SA_Trans_TVar T66 U1 X22 lk2 jm19 H53) => (fun (G6 : Env) (d : (Trace tm)) (H62 : (subst_evar G5 T65 s4 d G4 G6)) =>
      (SA_Trans_TVar G6 T66 U1 X22 (subst_evar_lookup_etvar T65 H62 U1 lk2) (subst_evar_Sub G5 s4 T65 jm24 G4 U1 T66 jm19 G6 d (weaken_subst_evar _ empty H62)) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H62)) H53)))
    | (SA_Arrow S15 S16 T67 T68 jm20 jm21) => (fun (G6 : Env) (d : (Trace tm)) (H62 : (subst_evar G5 T65 s4 d G4 G6)) =>
      (SA_Arrow G6 S15 S16 T67 T68 (subst_evar_Sub G5 s4 T65 jm24 G4 T67 S15 jm20 G6 d (weaken_subst_evar _ empty H62)) (subst_evar_Sub G5 s4 T65 jm24 G4 S16 T68 jm21 G6 d (weaken_subst_evar _ empty H62))))
    | (SA_All S15 S16 T67 T68 jm22 jm23) => (fun (G6 : Env) (d : (Trace tm)) (H62 : (subst_evar G5 T65 s4 d G4 G6)) =>
      (SA_All G6 S15 S16 T67 T68 (subst_evar_Sub G5 s4 T65 jm24 G4 T67 S15 jm22 G6 d (weaken_subst_evar _ empty H62)) (subst_evar_Sub G5 s4 T65 jm24 (etvar G4 T67) S16 T68 jm23 (appendEnv G6 (etvar empty T67)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty T67) H62))))
  end.
Fixpoint subst_etvar_Sub (G5 : Env) (S17 : Ty) (T66 : Ty) (jm24 : (Sub G5 S17 T66)) (G4 : Env) (T1 : Ty) (T2 : Ty) (jm25 : (Sub G4 T1 T2)) :
(forall (G6 : Env) (d : (Trace ty)) (H63 : (subst_etvar G5 T66 S17 d G4 G6)) ,
  (Sub G6 (tsubstTy d S17 T1) (tsubstTy d S17 T2))) :=
  match jm25 in (Sub _ T1 T2) return (forall (G6 : Env) (d : (Trace ty)) (H63 : (subst_etvar G5 T66 S17 d G4 G6)) ,
    (Sub G6 (tsubstTy d S17 T1) (tsubstTy d S17 T2))) with
    | (SA_Top S15 H50) => (fun (G6 : Env) (d : (Trace ty)) (H63 : (subst_etvar G5 T66 S17 d G4 G6)) =>
      (SA_Top G6 (tsubstTy (weakenTrace d H0) S17 S15) (substhvl_ty_wfTy (Sub_wf_0 G5 S17 T66 jm24) _ _ H50 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H63)))))
    | (SA_Refl_TVar X22 H51) => (fun (G6 : Env) (d : (Trace ty)) (H63 : (subst_etvar G5 T66 S17 d G4 G6)) =>
      (Env_reg_SA_Refl_TVar G6 _ (substhvl_ty_wfindex_ty (Sub_wf_0 G5 S17 T66 jm24) (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H63)) H51)))
    | (SA_Trans_TVar T67 U1 X22 lk2 jm19 H54) => (fun (G6 : Env) (d : (Trace ty)) (H63 : (subst_etvar G5 T66 S17 d G4 G6)) =>
      (Env_reg_SA_Trans_TVar G6 (tsubstTy (weakenTrace d H0) S17 T67) (tsubstTy (weakenTrace d H0) S17 U1) _ (subst_etvar_lookup_etvar G5 S17 T66 jm24 d _ _ H63 X22 U1 lk2) (subst_etvar_Sub G5 S17 T66 jm24 G4 U1 T67 jm19 G6 d (weaken_subst_etvar _ empty H63)) (substhvl_ty_wfindex_ty (Sub_wf_0 G5 S17 T66 jm24) (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H63)) H54)))
    | (SA_Arrow S15 S16 T68 T69 jm20 jm21) => (fun (G6 : Env) (d : (Trace ty)) (H63 : (subst_etvar G5 T66 S17 d G4 G6)) =>
      (SA_Arrow G6 (tsubstTy (weakenTrace d H0) S17 S15) (tsubstTy (weakenTrace d H0) S17 S16) (tsubstTy (weakenTrace d H0) S17 T68) (tsubstTy (weakenTrace d H0) S17 T69) (subst_etvar_Sub G5 S17 T66 jm24 G4 T68 S15 jm20 G6 d (weaken_subst_etvar _ empty H63)) (subst_etvar_Sub G5 S17 T66 jm24 G4 S16 T69 jm21 G6 d (weaken_subst_etvar _ empty H63))))
    | (SA_All S15 S16 T68 T69 jm22 jm23) => (fun (G6 : Env) (d : (Trace ty)) (H63 : (subst_etvar G5 T66 S17 d G4 G6)) =>
      (SA_All G6 (tsubstTy (weakenTrace d H0) S17 S15) (tsubstTy (weakenTrace d (HS ty H0)) S17 S16) (tsubstTy (weakenTrace d H0) S17 T68) (tsubstTy (weakenTrace d (HS ty H0)) S17 T69) (subst_etvar_Sub G5 S17 T66 jm24 G4 T68 S15 jm22 G6 d (weaken_subst_etvar _ empty H63)) (subst_etvar_Sub G5 S17 T66 jm24 (etvar G4 T68) S16 T69 jm23 (appendEnv G6 (tsubstEnv d S17 (etvar empty T68))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty T68) H63))))
  end.
Fixpoint subst_evar_Typing (G5 : Env) (s4 : Tm) (T67 : Ty) (jm27 : (Typing G5 s4 T67)) (G4 : Env) (t : Tm) (T : Ty) (jm28 : (Typing G4 t T)) :
(forall (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) ,
  (Typing G6 (substTm d s4 t) T)) :=
  match jm28 in (Typing _ t T) return (forall (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) ,
    (Typing G6 (substTm d s4 t) T)) with
    | (T_Var T68 y1 lk2 H51 H52) => (fun (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) =>
      (subst_evar_lookup_evar G5 s4 T67 jm27 d G4 G6 H70 y1 T68 lk2))
    | (T_Abs T69 T72 t19 jm21 H53 H54) => (fun (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) =>
      (T_Abs G6 T69 T72 (substTm (weakenTrace d (HS tm H0)) s4 t19) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G5 s4 T67 jm27 (evar G4 T69) t19 (weakenTy T72 (HS tm H0)) jm21 (appendEnv G6 (evar empty T69)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T69) H70))) (substhvl_tm_wfTy _ _ H53 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H70))) (substhvl_tm_wfTy _ _ H54 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H70)))))
    | (T_App T70 T71 t20 t21 jm22 jm23) => (fun (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) =>
      (T_App G6 T70 T71 (substTm (weakenTrace d H0) s4 t20) (substTm (weakenTrace d H0) s4 t21) (subst_evar_Typing G5 s4 T67 jm27 G4 t20 (tarr T70 T71) jm22 G6 d (weaken_subst_evar _ empty H70)) (subst_evar_Typing G5 s4 T67 jm27 G4 t21 T70 jm23 G6 d (weaken_subst_evar _ empty H70))))
    | (T_Tabs T69 T72 t19 jm24 H60) => (fun (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) =>
      (T_Tabs G6 T69 T72 (substTm (weakenTrace d (HS ty H0)) s4 t19) (subst_evar_Typing G5 s4 T67 jm27 (etvar G4 T69) t19 T72 jm24 (appendEnv G6 (etvar empty T69)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty T69) H70)) (substhvl_tm_wfTy _ _ H60 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H70)))))
    | (T_Tapp T70 T71 T72 t20 jm25 jm26) => (fun (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) =>
      (T_Tapp G6 T70 T71 T72 (substTm (weakenTrace d H0) s4 t20) (subst_evar_Typing G5 s4 T67 jm27 G4 t20 (tall T70 T71) jm25 G6 d (weaken_subst_evar _ empty H70)) (subst_evar_Sub G5 s4 T67 jm27 G4 T72 T70 jm26 G6 d (weaken_subst_evar _ empty H70))))
    | (T_Sub T69 T72 t19 jm19 jm20) => (fun (G6 : Env) (d : (Trace tm)) (H70 : (subst_evar G5 T67 s4 d G4 G6)) =>
      (T_Sub G6 T69 T72 (substTm (weakenTrace d H0) s4 t19) (subst_evar_Typing G5 s4 T67 jm27 G4 t19 T69 jm19 G6 d (weaken_subst_evar _ empty H70)) (subst_evar_Sub G5 s4 T67 jm27 G4 T69 T72 jm20 G6 d (weaken_subst_evar _ empty H70))))
  end.
Fixpoint subst_etvar_Typing (G5 : Env) (S15 : Ty) (T68 : Ty) (jm27 : (Sub G5 S15 T68)) (G4 : Env) (t : Tm) (T : Ty) (jm28 : (Typing G4 t T)) :
(forall (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) ,
  (Typing G6 (tsubstTm d S15 t) (tsubstTy d S15 T))) :=
  match jm28 in (Typing _ t T) return (forall (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) ,
    (Typing G6 (tsubstTm d S15 t) (tsubstTy d S15 T))) with
    | (T_Var T69 y1 lk2 H52 H53) => (fun (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) =>
      (T_Var G6 (tsubstTy (weakenTrace d H0) S15 T69) y1 (subst_etvar_lookup_evar T68 (Sub_wf_0 G5 S15 T68 jm27) H71 T69 lk2) (substhvl_ty_wfTy (Sub_wf_0 G5 S15 T68 jm27) _ _ H52 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H71))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H71)) H53)))
    | (T_Abs T70 T73 t19 jm21 H54 H55) => (fun (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) =>
      (T_Abs G6 (tsubstTy (weakenTrace d H0) S15 T70) (tsubstTy (weakenTrace d H0) S15 T73) (tsubstTm (weakenTrace d (HS tm H0)) S15 t19) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d S15 T73)) (subst_etvar_Typing G5 S15 T68 jm27 (evar G4 T70) t19 (weakenTy T73 (HS tm H0)) jm21 (appendEnv G6 (tsubstEnv d S15 (evar empty T70))) (weakenTrace d (HS tm H0)) (weaken_subst_etvar _ (evar empty T70) H71))) (substhvl_ty_wfTy (Sub_wf_0 G5 S15 T68 jm27) _ _ H54 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H71))) (substhvl_ty_wfTy (Sub_wf_0 G5 S15 T68 jm27) _ _ H55 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H71)))))
    | (T_App T71 T72 t20 t21 jm22 jm23) => (fun (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) =>
      (T_App G6 (tsubstTy (weakenTrace d H0) S15 T71) (tsubstTy (weakenTrace d H0) S15 T72) (tsubstTm (weakenTrace d H0) S15 t20) (tsubstTm (weakenTrace d H0) S15 t21) (subst_etvar_Typing G5 S15 T68 jm27 G4 t20 (tarr T71 T72) jm22 G6 d (weaken_subst_etvar _ empty H71)) (subst_etvar_Typing G5 S15 T68 jm27 G4 t21 T71 jm23 G6 d (weaken_subst_etvar _ empty H71))))
    | (T_Tabs T70 T73 t19 jm24 H61) => (fun (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) =>
      (T_Tabs G6 (tsubstTy (weakenTrace d H0) S15 T70) (tsubstTy (weakenTrace d (HS ty H0)) S15 T73) (tsubstTm (weakenTrace d (HS ty H0)) S15 t19) (subst_etvar_Typing G5 S15 T68 jm27 (etvar G4 T70) t19 T73 jm24 (appendEnv G6 (tsubstEnv d S15 (etvar empty T70))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty T70) H71)) (substhvl_ty_wfTy (Sub_wf_0 G5 S15 T68 jm27) _ _ H61 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H71)))))
    | (T_Tapp T71 T72 T73 t20 jm25 jm26) => (fun (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) =>
      (Typing_cast G6 _ _ G6 (tsubstTm d S15 (tapp t20 T73)) (tsubstTy d S15 (tsubstTy X0 T73 T72)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T72 d S15 T73)) (T_Tapp G6 (tsubstTy (weakenTrace d H0) S15 T71) (tsubstTy (weakenTrace d (HS ty H0)) S15 T72) (tsubstTy (weakenTrace d H0) S15 T73) (tsubstTm (weakenTrace d H0) S15 t20) (subst_etvar_Typing G5 S15 T68 jm27 G4 t20 (tall T71 T72) jm25 G6 d (weaken_subst_etvar _ empty H71)) (subst_etvar_Sub G5 S15 T68 jm27 G4 T73 T71 jm26 G6 d (weaken_subst_etvar _ empty H71)))))
    | (T_Sub T70 T73 t19 jm19 jm20) => (fun (G6 : Env) (d : (Trace ty)) (H71 : (subst_etvar G5 T68 S15 d G4 G6)) =>
      (T_Sub G6 (tsubstTy (weakenTrace d H0) S15 T70) (tsubstTy (weakenTrace d H0) S15 T73) (tsubstTm (weakenTrace d H0) S15 t19) (subst_etvar_Typing G5 S15 T68 jm27 G4 t19 T70 jm19 G6 d (weaken_subst_etvar _ empty H71)) (subst_etvar_Sub G5 S15 T68 jm27 G4 T70 T73 jm20 G6 d (weaken_subst_etvar _ empty H71))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.