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
  
  Fixpoint weakenIndextm (x13 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x13
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x13 k))
        | _ => (weakenIndextm x13 k)
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
    (forall (x13 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x13 k) k0) = (weakenIndextm x13 (appendHvl k k0)))).
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
    | tall (T : Ty)
    | tprod (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | pprod (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (t : Tm)
    | tapp (t : Tm) (T : Ty)
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
  Fixpoint shiftIndex (c : (Cutoff tm)) (x13 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x13)
      | (CS c) => match x13 with
        | (I0) => I0
        | (IS x13) => (IS (shiftIndex c x13))
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
      | (tarr T43 T44) => (tarr (tshiftTy c T43) (tshiftTy c T44))
      | (tall T45) => (tall (tshiftTy (CS c) T45))
      | (tprod T46 T47) => (tprod (tshiftTy c T46) (tshiftTy c T47))
    end.
  Fixpoint tshiftPat (c : (Cutoff ty)) (p18 : Pat) {struct p18} :
  Pat :=
    match p18 with
      | (pvar T43) => (pvar (tshiftTy c T43))
      | (pprod p19 p20) => (pprod (tshiftPat c p19) (tshiftPat (weakenCutoffty c (appendHvl H0 (bindPat p19))) p20))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x13) => (var (shiftIndex c x13))
      | (abs T43 t27) => (abs T43 (shiftTm (CS c) t27))
      | (app t28 t29) => (app (shiftTm c t28) (shiftTm c t29))
      | (tabs t30) => (tabs (shiftTm c t30))
      | (tapp t31 T44) => (tapp (shiftTm c t31) T44)
      | (prod t32 t33) => (prod (shiftTm c t32) (shiftTm c t33))
      | (lett p18 t34 t35) => (lett p18 (shiftTm c t34) (shiftTm (weakenCutofftm c (appendHvl H0 (bindPat p18))) t35))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x13) => (var x13)
      | (abs T43 t27) => (abs (tshiftTy c T43) (tshiftTm c t27))
      | (app t28 t29) => (app (tshiftTm c t28) (tshiftTm c t29))
      | (tabs t30) => (tabs (tshiftTm (CS c) t30))
      | (tapp t31 T44) => (tapp (tshiftTm c t31) (tshiftTy c T44))
      | (prod t32 t33) => (prod (tshiftTm c t32) (tshiftTm c t33))
      | (lett p18 t34 t35) => (lett (tshiftPat c p18) (tshiftTm c t34) (tshiftTm (weakenCutoffty c (appendHvl H0 (bindPat p18))) t35))
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
  Fixpoint weakenPat (p18 : Pat) (k : Hvl) {struct k} :
  Pat :=
    match k with
      | (H0) => p18
      | (HS tm k) => (weakenPat p18 k)
      | (HS ty k) => (tshiftPat C0 (weakenPat p18 k))
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
        (T43 : (Trace a)).
  
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
      | (XS ty d) => (tshiftTm C0 (substIndex d s x13))
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
      | (tarr T43 T44) => (tarr (tsubstTy d S0 T43) (tsubstTy d S0 T44))
      | (tall T45) => (tall (tsubstTy (weakenTrace d (HS ty H0)) S0 T45))
      | (tprod T46 T47) => (tprod (tsubstTy d S0 T46) (tsubstTy d S0 T47))
    end.
  Fixpoint tsubstPat (d : (Trace ty)) (S0 : Ty) (p18 : Pat) {struct p18} :
  Pat :=
    match p18 with
      | (pvar T43) => (pvar (tsubstTy d S0 T43))
      | (pprod p19 p20) => (pprod (tsubstPat d S0 p19) (tsubstPat (weakenTrace d (appendHvl H0 (bindPat p19))) S0 p20))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x13) => (substIndex d s x13)
      | (abs T43 t27) => (abs T43 (substTm (weakenTrace d (HS tm H0)) s t27))
      | (app t28 t29) => (app (substTm d s t28) (substTm d s t29))
      | (tabs t30) => (tabs (substTm (weakenTrace d (HS ty H0)) s t30))
      | (tapp t31 T44) => (tapp (substTm d s t31) T44)
      | (prod t32 t33) => (prod (substTm d s t32) (substTm d s t33))
      | (lett p18 t34 t35) => (lett p18 (substTm d s t34) (substTm (weakenTrace d (appendHvl H0 (bindPat p18))) s t35))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x13) => (var x13)
      | (abs T43 t27) => (abs (tsubstTy d S0 T43) (tsubstTm (weakenTrace d (HS tm H0)) S0 t27))
      | (app t28 t29) => (app (tsubstTm d S0 t28) (tsubstTm d S0 t29))
      | (tabs t30) => (tabs (tsubstTm (weakenTrace d (HS ty H0)) S0 t30))
      | (tapp t31 T44) => (tapp (tsubstTm d S0 t31) (tsubstTy d S0 T44))
      | (prod t32 t33) => (prod (tsubstTm d S0 t32) (tsubstTm d S0 t33))
      | (lett p18 t34 t35) => (lett (tsubstPat d S0 p18) (tsubstTm d S0 t34) (tsubstTm (weakenTrace d (appendHvl H0 (bindPat p18))) S0 t35))
    end.
End Subst.

Global Hint Resolve (f_equal (tshiftPat C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_tshift_bindPat  :
  (forall (p18 : Pat) ,
    (forall (c : (Cutoff ty)) ,
      ((bindPat (tshiftPat c p18)) = (bindPat p18)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tshift_bindPat : interaction.
 Hint Rewrite stability_tshift_bindPat : stability_shift.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p19 : Pat) ,
    ((bindPat (weakenPat p19 k)) = (bindPat p19))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPat : stability_weaken.
Lemma stability_tsubst_bindPat  :
  (forall (p19 : Pat) ,
    (forall (d : (Trace ty)) (S0 : Ty) ,
      ((bindPat (tsubstPat d S0 p19)) = (bindPat p19)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tsubst_bindPat : interaction.
 Hint Rewrite stability_tsubst_bindPat : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x13 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x13)) = (var x13))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S1 : Ty) :
    (forall (k : Hvl) (X12 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S1 (tshiftIndex (weakenCutoffty C0 k) X12)) = (tvar X12))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S2 : Ty) (k : Hvl) (S1 : Ty) {struct S2} :
  ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = S2) :=
    match S2 return ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = S2) with
      | (tvar X12) => (tsubstIndex0_tshiftIndex0_reflection_ind S1 k X12)
      | (tarr T44 T45) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T44 k S1) (tsubst0_tshift0_Ty_reflection_ind T45 k S1))
      | (tall T43) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T43 (HS ty k) S1)))
      | (tprod T44 T45) => (f_equal2 tprod (tsubst0_tshift0_Ty_reflection_ind T44 k S1) (tsubst0_tshift0_Ty_reflection_ind T45 k S1))
    end.
  Fixpoint tsubst0_tshift0_Pat_reflection_ind (p20 : Pat) (k : Hvl) (S1 : Ty) {struct p20} :
  ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = p20) :=
    match p20 return ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = p20) with
      | (pvar T43) => (f_equal pvar (tsubst0_tshift0_Ty_reflection_ind T43 k S1))
      | (pprod p21 p22) => (f_equal2 pprod (tsubst0_tshift0_Pat_reflection_ind p21 k S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (tsubst0_tshift0_Pat_reflection_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) S1)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x13) => (substIndex0_shiftIndex0_reflection_ind s k x13)
      | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t27 (HS tm k) s)))
      | (app t28 t29) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t28 k s) (subst0_shift0_Tm_reflection_ind t29 k s))
      | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t27 (HS ty k) s)))
      | (tapp t27 T43) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t27 k s) eq_refl)
      | (prod t28 t29) => (f_equal2 prod (subst0_shift0_Tm_reflection_ind t28 k s) (subst0_shift0_Tm_reflection_ind t29 k s))
      | (lett p20 t28 t29) => (f_equal3 lett eq_refl (subst0_shift0_Tm_reflection_ind t28 k s) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (subst0_shift0_Tm_reflection_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) s)))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S1 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x13) => eq_refl
      | (abs T43 t27) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T43 k S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t27 (HS tm k) S1)))
      | (app t28 t29) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t28 k S1) (tsubst0_tshift0_Tm_reflection_ind t29 k S1))
      | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t27 (HS ty k) S1)))
      | (tapp t27 T43) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t27 k S1) (tsubst0_tshift0_Ty_reflection_ind T43 k S1))
      | (prod t28 t29) => (f_equal2 prod (tsubst0_tshift0_Tm_reflection_ind t28 k S1) (tsubst0_tshift0_Tm_reflection_ind t29 k S1))
      | (lett p20 t28 t29) => (f_equal3 lett (tsubst0_tshift0_Pat_reflection_ind p20 k S1) (tsubst0_tshift0_Tm_reflection_ind t28 k S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (tsubst0_tshift0_Tm_reflection_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) S1)))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S2 : Ty) : (forall (S1 : Ty) ,
    ((tsubstTy X0 S1 (tshiftTy C0 S2)) = S2)) := (tsubst0_tshift0_Ty_reflection_ind S2 H0).
  Definition tsubstPat0_tshiftPat0_reflection (p20 : Pat) : (forall (S1 : Ty) ,
    ((tsubstPat X0 S1 (tshiftPat C0 p20)) = p20)) := (tsubst0_tshift0_Pat_reflection_ind p20 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S1 : Ty) ,
    ((tsubstTm X0 S1 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff tm)) (x13 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c0) k) (shiftIndex (weakenCutofftm C0 k) x13)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c0 k) x13)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff ty)) (X12 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c0) k) (tshiftIndex (weakenCutoffty C0 k) X12)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c0 k) X12)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c0 : (Cutoff ty)) {struct S1} :
    ((tshiftTy (weakenCutoffty (CS c0) k) (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c0 k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffty (CS c0) k) (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c0 k) S1))) with
        | (tvar X12) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c0 X12))
        | (tarr T44 T45) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T44 k c0) (tshift_tshift0_Ty_comm_ind T45 k c0))
        | (tall T43) => (f_equal tall (tshift_tshift0_Ty_comm_ind T43 (HS ty k) c0))
        | (tprod T44 T45) => (f_equal2 tprod (tshift_tshift0_Ty_comm_ind T44 k c0) (tshift_tshift0_Ty_comm_ind T45 k c0))
      end.
    Fixpoint tshift_tshift0_Pat_comm_ind (p20 : Pat) (k : Hvl) (c0 : (Cutoff ty)) {struct p20} :
    ((tshiftPat (weakenCutoffty (CS c0) k) (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c0 k) p20))) :=
      match p20 return ((tshiftPat (weakenCutoffty (CS c0) k) (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c0 k) p20))) with
        | (pvar T43) => (f_equal pvar (tshift_tshift0_Ty_comm_ind T43 k c0))
        | (pprod p21 p22) => (f_equal2 pprod (tshift_tshift0_Pat_comm_ind p21 k c0) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p21)))) (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (eq_trans (tshift_tshift0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) c0) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftPat (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p21)))) eq_refl)))))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c0) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c0) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x13) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c0 x13))
        | (abs T43 t27) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t27 (HS tm k) c0))
        | (app t28 t29) => (f_equal2 app (shift_shift0_Tm_comm_ind t28 k c0) (shift_shift0_Tm_comm_ind t29 k c0))
        | (tabs t27) => (f_equal tabs (shift_shift0_Tm_comm_ind t27 (HS ty k) c0))
        | (tapp t27 T43) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t27 k c0) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (shift_shift0_Tm_comm_ind t28 k c0) (shift_shift0_Tm_comm_ind t29 k c0))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (shift_shift0_Tm_comm_ind t28 k c0) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c0) k (appendHvl H0 (bindPat p20))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c0 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c0 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t27 (HS tm k) c0))
        | (app t28 t29) => (f_equal2 app (shift_tshift0_Tm_comm_ind t28 k c0) (shift_tshift0_Tm_comm_ind t29 k c0))
        | (tabs t27) => (f_equal tabs (shift_tshift0_Tm_comm_ind t27 (HS ty k) c0))
        | (tapp t27 T43) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t27 k c0) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (shift_tshift0_Tm_comm_ind t28 k c0) (shift_tshift0_Tm_comm_ind t29 k c0))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (shift_tshift0_Tm_comm_ind t28 k c0) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c0 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c0 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c0 k) s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t27 (HS tm k) c0))
        | (app t28 t29) => (f_equal2 app (tshift_shift0_Tm_comm_ind t28 k c0) (tshift_shift0_Tm_comm_ind t29 k c0))
        | (tabs t27) => (f_equal tabs (tshift_shift0_Tm_comm_ind t27 (HS ty k) c0))
        | (tapp t27 T43) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t27 k c0) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (tshift_shift0_Tm_comm_ind t28 k c0) (tshift_shift0_Tm_comm_ind t29 k c0))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (tshift_shift0_Tm_comm_ind t28 k c0) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c0) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c0) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c0 k) s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T43 k c0) (tshift_tshift0_Tm_comm_ind t27 (HS tm k) c0))
        | (app t28 t29) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t28 k c0) (tshift_tshift0_Tm_comm_ind t29 k c0))
        | (tabs t27) => (f_equal tabs (tshift_tshift0_Tm_comm_ind t27 (HS ty k) c0))
        | (tapp t27 T43) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t27 k c0) (tshift_tshift0_Ty_comm_ind T43 k c0))
        | (prod t28 t29) => (f_equal2 prod (tshift_tshift0_Tm_comm_ind t28 k c0) (tshift_tshift0_Tm_comm_ind t29 k c0))
        | (lett p20 t28 t29) => (f_equal3 lett (tshift_tshift0_Pat_comm_ind p20 k c0) (tshift_tshift0_Tm_comm_ind t28 k c0) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p20)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S1 : Ty) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftTy (CS c0) (tshiftTy C0 S1)) = (tshiftTy C0 (tshiftTy c0 S1)))) := (tshift_tshift0_Ty_comm_ind S1 H0).
    Definition tshift_tshift0_Pat_comm (p20 : Pat) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftPat (CS c0) (tshiftPat C0 p20)) = (tshiftPat C0 (tshiftPat c0 p20)))) := (tshift_tshift0_Pat_comm_ind p20 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff tm)) ,
      ((shiftTm (CS c0) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c0 s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff tm)) ,
      ((shiftTm c0 (tshiftTm C0 s)) = (tshiftTm C0 (shiftTm c0 s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftTm c0 (shiftTm C0 s)) = (shiftTm C0 (tshiftTm c0 s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftTm (CS c0) (tshiftTm C0 s)) = (tshiftTm C0 (tshiftTm c0 s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((weakenTy (tshiftTy c0 S1) k) = (tshiftTy (weakenCutoffty c0 k) (weakenTy S1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPat_tshiftPat  :
    (forall (k : Hvl) (c0 : (Cutoff ty)) (p20 : Pat) ,
      ((weakenPat (tshiftPat c0 p20) k) = (tshiftPat (weakenCutoffty c0 k) (weakenPat p20 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c0 : (Cutoff tm)) (s : Tm) ,
      ((weakenTm (shiftTm c0 s) k) = (shiftTm (weakenCutofftm c0 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c0 : (Cutoff ty)) (s : Tm) ,
      ((weakenTm (tshiftTm c0 s) k) = (tshiftTm (weakenCutoffty c0 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c0 : (Cutoff tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c0 k) (substIndex (weakenTrace X0 k) s x13)) = (substIndex (weakenTrace X0 k) (shiftTm c0 s) (shiftIndex (weakenCutofftm (CS c0) k) x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c0 : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c0 k) (substIndex (weakenTrace X0 k) s x13)) = (substIndex (weakenTrace X0 k) (tshiftTm c0 s) x13))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c0 : (Cutoff ty)) (S1 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c0 k) (tsubstIndex (weakenTrace X0 k) S1 X12)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftIndex (weakenCutoffty (CS c0) k) X12)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) {struct S2} :
    ((tshiftTy (weakenCutoffty c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffty (CS c0) k) S2))) :=
      match S2 return ((tshiftTy (weakenCutoffty c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffty (CS c0) k) S2))) with
        | (tvar X12) => (tshiftTy_tsubstIndex0_comm_ind c0 S1 k X12)
        | (tarr T44 T45) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T44 k c0 S1) (tshift_tsubst0_Ty_comm_ind T45 k c0 S1))
        | (tall T43) => (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T43 (HS ty k) c0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tprod T44 T45) => (f_equal2 tprod (tshift_tsubst0_Ty_comm_ind T44 k c0 S1) (tshift_tsubst0_Ty_comm_ind T45 k c0 S1))
      end.
    Fixpoint tshift_tsubst0_Pat_comm_ind (p20 : Pat) (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) {struct p20} :
    ((tshiftPat (weakenCutoffty c0 k) (tsubstPat (weakenTrace X0 k) S1 p20)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffty (CS c0) k) p20))) :=
      match p20 return ((tshiftPat (weakenCutoffty c0 k) (tsubstPat (weakenTrace X0 k) S1 p20)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffty (CS c0) k) p20))) with
        | (pvar T43) => (f_equal pvar (tshift_tsubst0_Ty_comm_ind T43 k c0 S1))
        | (pprod p21 p22) => (f_equal2 pprod (tshift_tsubst0_Pat_comm_ind p21 k c0 S1) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p21)))) (f_equal3 tsubstPat (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) c0 S1) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftPat (eq_sym (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p21)))) eq_refl)))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutofftm (CS c0) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutofftm (CS c0) k) s0))) with
        | (var x13) => (shiftTm_substIndex0_comm_ind c0 s k x13)
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t27 (HS tm k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t28 t29) => (f_equal2 app (shift_subst0_Tm_comm_ind t28 k c0 s) (shift_subst0_Tm_comm_ind t29 k c0 s))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t27 (HS ty k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t27 T43) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t27 k c0 s) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (shift_subst0_Tm_comm_ind t28 k c0 s) (shift_subst0_Tm_comm_ind t29 k c0 s))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (shift_subst0_Tm_comm_ind t28 k c0 s) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c0) k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) (S1 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t27 (HS tm k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t28 t29) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t28 k c0 S1) (shift_tsubst0_Tm_comm_ind t29 k c0 S1))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t27 (HS ty k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t27 T43) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t27 k c0 S1) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (shift_tsubst0_Tm_comm_ind t28 k c0 S1) (shift_tsubst0_Tm_comm_ind t29 k c0 S1))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (shift_tsubst0_Tm_comm_ind t28 k c0 S1) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffty c0 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffty c0 k) s0))) with
        | (var x13) => (tshiftTm_substIndex0_comm_ind c0 s k x13)
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t27 (HS tm k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t28 t29) => (f_equal2 app (tshift_subst0_Tm_comm_ind t28 k c0 s) (tshift_subst0_Tm_comm_ind t29 k c0 s))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t27 (HS ty k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t27 T43) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t27 k c0 s) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (tshift_subst0_Tm_comm_ind t28 k c0 s) (tshift_subst0_Tm_comm_ind t29 k c0 s))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (tshift_subst0_Tm_comm_ind t28 k c0 s) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffty (CS c0) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffty (CS c0) k) s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T43 k c0 S1) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t27 (HS tm k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t28 t29) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t28 k c0 S1) (tshift_tsubst0_Tm_comm_ind t29 k c0 S1))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t27 (HS ty k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t27 T43) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t27 k c0 S1) (tshift_tsubst0_Ty_comm_ind T43 k c0 S1))
        | (prod t28 t29) => (f_equal2 prod (tshift_tsubst0_Tm_comm_ind t28 k c0 S1) (tshift_tsubst0_Tm_comm_ind t29 k c0 S1))
        | (lett p20 t28 t29) => (f_equal3 lett (tshift_tsubst0_Pat_comm_ind p20 k c0 S1) (tshift_tsubst0_Tm_comm_ind t28 k c0 S1) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) c0 S1) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S2 : Ty) : (forall (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftTy c0 (tsubstTy X0 S1 S2)) = (tsubstTy X0 (tshiftTy c0 S1) (tshiftTy (CS c0) S2)))) := (tshift_tsubst0_Ty_comm_ind S2 H0).
    Definition tshiftPat_tsubstPat0_comm (p20 : Pat) : (forall (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftPat c0 (tsubstPat X0 S1 p20)) = (tsubstPat X0 (tshiftTy c0 S1) (tshiftPat (CS c0) p20)))) := (tshift_tsubst0_Pat_comm_ind p20 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c0 (substTm X0 s s0)) = (substTm X0 (shiftTm c0 s) (shiftTm (CS c0) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff tm)) (S1 : Ty) ,
      ((shiftTm c0 (tsubstTm X0 S1 s)) = (tsubstTm X0 S1 (shiftTm c0 s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c0 (substTm X0 s s0)) = (substTm X0 (tshiftTm c0 s) (tshiftTm c0 s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftTm c0 (tsubstTm X0 S1 s)) = (tsubstTm X0 (tshiftTy c0 S1) (tshiftTm (CS c0) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d0 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d0) k) s (shiftIndex (weakenCutofftm C0 k) x13)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d0 k) s x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d0 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d0) k) s x13) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d0 k) s x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d0 : (Trace ty)) (S1 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d0) k) S1 X12) = (tsubstIndex (weakenTrace d0 k) S1 X12))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d0 : (Trace ty)) (S1 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d0) k) S1 (tshiftIndex (weakenCutoffty C0 k) X12)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d0 k) S1 X12)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS ty d0) k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) :=
      match S2 return ((tsubstTy (weakenTrace (XS ty d0) k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) with
        | (tvar X12) => (tsubstIndex_tshiftTy0_comm_ind d0 S1 k X12)
        | (tarr T44 T45) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T44 k d0 S1) (tsubst_tshift0_Ty_comm_ind T45 k d0 S1))
        | (tall T43) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T43 (HS ty k) d0 S1) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tprod T44 T45) => (f_equal2 tprod (tsubst_tshift0_Ty_comm_ind T44 k d0 S1) (tsubst_tshift0_Ty_comm_ind T45 k d0 S1))
      end.
    Fixpoint tsubst_tshift0_Pat_comm_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace (XS ty d0) k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d0 k) S1 p20))) :=
      match p20 return ((tsubstPat (weakenTrace (XS ty d0) k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d0 k) S1 p20))) with
        | (pvar T43) => (f_equal pvar (tsubst_tshift0_Ty_comm_ind T43 k d0 S1))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tshift0_Pat_comm_ind p21 k d0 S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (eq_trans (tsubst_tshift0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S1) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d0) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d0) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x13) => (substIndex_shiftTm0_comm_ind d0 s k x13)
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t27 (HS tm k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (subst_shift0_Tm_comm_ind t28 k d0 s) (subst_shift0_Tm_comm_ind t29 k d0 s))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t27 (HS ty k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t27 k d0 s) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (subst_shift0_Tm_comm_ind t28 k d0 s) (subst_shift0_Tm_comm_ind t29 k d0 s))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (subst_shift0_Tm_comm_ind t28 k d0 s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d0) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d0) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x13) => (substIndex_tshiftTm0_comm_ind d0 s k x13)
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t27 (HS tm k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (subst_tshift0_Tm_comm_ind t28 k d0 s) (subst_tshift0_Tm_comm_ind t29 k d0 s))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t27 (HS ty k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t27 k d0 s) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (subst_tshift0_Tm_comm_ind t28 k d0 s) (subst_tshift0_Tm_comm_ind t29 k d0 s))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (subst_tshift0_Tm_comm_ind t28 k d0 s) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append tm (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (subst_tshift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t27 (HS tm k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t28 k d0 S1) (tsubst_shift0_Tm_comm_ind t29 k d0 S1))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t27 (HS ty k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t27 k d0 S1) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (tsubst_shift0_Tm_comm_ind t28 k d0 S1) (tsubst_shift0_Tm_comm_ind t29 k d0 S1))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (tsubst_shift0_Tm_comm_ind t28 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tsubst_shift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d0) k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d0) k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T43 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t27 (HS tm k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t28 k d0 S1) (tsubst_tshift0_Tm_comm_ind t29 k d0 S1))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t27 (HS ty k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t27 k d0 S1) (tsubst_tshift0_Ty_comm_ind T43 k d0 S1))
        | (prod t28 t29) => (f_equal2 prod (tsubst_tshift0_Tm_comm_ind t28 k d0 S1) (tsubst_tshift0_Tm_comm_ind t29 k d0 S1))
        | (lett p20 t28 t29) => (f_equal3 lett (tsubst_tshift0_Pat_comm_ind p20 k d0 S1) (tsubst_tshift0_Tm_comm_ind t28 k d0 S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tsubst_tshift0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S2 : Ty) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTy (XS ty d0) S1 (tshiftTy C0 S2)) = (tshiftTy C0 (tsubstTy d0 S1 S2)))) := (tsubst_tshift0_Ty_comm_ind S2 H0).
    Definition tsubstPat_tshiftPat0_comm (p20 : Pat) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstPat (XS ty d0) S1 (tshiftPat C0 p20)) = (tshiftPat C0 (tsubstPat d0 S1 p20)))) := (tsubst_tshift0_Pat_comm_ind p20 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d0) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d0 s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d0) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d0 s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm d0 S1 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d0 S1 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm (XS ty d0) S1 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d0 S1 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S2 : Ty) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS tm d0) k) S1 S2) = (tsubstTy (weakenTrace d0 k) S1 S2)) :=
      match S2 return ((tsubstTy (weakenTrace (XS tm d0) k) S1 S2) = (tsubstTy (weakenTrace d0 k) S1 S2)) with
        | (tvar X12) => (tsubstIndex_shiftTy0_comm_ind d0 S1 k X12)
        | (tarr T44 T45) => (f_equal2 tarr (tsubst_tm_Ty_ind T44 k d0 S1) (tsubst_tm_Ty_ind T45 k d0 S1))
        | (tall T43) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T43 (HS ty k) d0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl))))
        | (tprod T44 T45) => (f_equal2 tprod (tsubst_tm_Ty_ind T44 k d0 S1) (tsubst_tm_Ty_ind T45 k d0 S1))
      end.
    Fixpoint tsubst_tm_Pat_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace (XS tm d0) k) S1 p20) = (tsubstPat (weakenTrace d0 k) S1 p20)) :=
      match p20 return ((tsubstPat (weakenTrace (XS tm d0) k) S1 p20) = (tsubstPat (weakenTrace d0 k) S1 p20)) with
        | (pvar T43) => (f_equal pvar (tsubst_tm_Ty_ind T43 k d0 S1))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tm_Pat_ind p21 k d0 S1) (eq_trans (f_equal3 tsubstPat (weakenTrace_append ty (XS tm d0) k (appendHvl H0 (bindPat p21))) eq_refl eq_refl) (eq_trans (tsubst_tm_Pat_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S1) (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs (tsubst_tm_Ty_ind T43 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t27 (HS tm k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t28 t29) => (f_equal2 app (tsubst_tm_Tm_ind t28 k d0 S1) (tsubst_tm_Tm_ind t29 k d0 S1))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t27 (HS ty k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t27 T43) => (f_equal2 tapp (tsubst_tm_Tm_ind t27 k d0 S1) (tsubst_tm_Ty_ind T43 k d0 S1))
        | (prod t28 t29) => (f_equal2 prod (tsubst_tm_Tm_ind t28 k d0 S1) (tsubst_tm_Tm_ind t29 k d0 S1))
        | (lett p20 t28 t29) => (f_equal3 lett (tsubst_tm_Pat_ind p20 k d0 S1) (tsubst_tm_Tm_ind t28 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (appendHvl H0 (bindPat p20))) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl))))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S2 : Ty) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTy (XS tm d0) S1 S2) = (tsubstTy d0 S1 S2))) := (tsubst_tm_Ty_ind S2 H0).
    Definition tsubstPat_tm (p20 : Pat) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstPat (XS tm d0) S1 p20) = (tsubstPat d0 S1 p20))) := (tsubst_tm_Pat_ind p20 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm (XS tm d0) S1 s) = (tsubstTm d0 S1 s))) := (tsubst_tm_Tm_ind s H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstPat_tm tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstPat_tm tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d0 : (Trace tm)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substTm (weakenTrace d0 k) s (substIndex (weakenTrace X0 k) s0 x13)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substIndex (weakenTrace (XS tm d0) k) s x13)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d0 : (Trace ty)) (S1 : Ty) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((tsubstTm (weakenTrace d0 k) S1 (substIndex (weakenTrace X0 k) s x13)) = (substIndex (weakenTrace X0 k) (tsubstTm d0 S1 s) x13))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstTy (weakenTrace d0 k) S1 (tsubstIndex (weakenTrace X0 k) S2 X12)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstIndex (weakenTrace (XS ty d0) k) S1 X12)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d0 : (Trace tm)) (s : Tm) (S1 : Ty) :
      (forall (k : Hvl) (x13 : (Index tm)) ,
        ((substIndex (weakenTrace d0 k) s x13) = (tsubstTm (weakenTrace X0 k) S1 (substIndex (weakenTrace (XS ty d0) k) s x13)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S3 : Ty) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct S3} :
    ((tsubstTy (weakenTrace d0 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTy (weakenTrace (XS ty d0) k) S1 S3))) :=
      match S3 return ((tsubstTy (weakenTrace d0 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTy (weakenTrace (XS ty d0) k) S1 S3))) with
        | (tvar X12) => (tsubstTy_tsubstIndex0_commright_ind d0 S1 S2 k X12)
        | (tarr T44 T45) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T44 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T45 k d0 S1 S2))
        | (tall T43) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T43 (HS ty k) d0 S1 S2) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tprod T44 T45) => (f_equal2 tprod (tsubst_tsubst0_Ty_comm_ind T44 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T45 k d0 S1 S2))
      end.
    Fixpoint tsubst_tsubst0_Pat_comm_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p20)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS ty d0) k) S1 p20))) :=
      match p20 return ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p20)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS ty d0) k) S1 p20))) with
        | (pvar T43) => (f_equal pvar (tsubst_tsubst0_Ty_comm_ind T43 k d0 S1 S2))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tsubst0_Pat_comm_ind p21 k d0 S1 S2) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal3 tsubstPat (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S1 S2) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS tm d0) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS tm d0) k) s s1))) with
        | (var x13) => (substTm_substIndex0_commright_ind d0 s s0 k x13)
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t27 (HS tm k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (subst_subst0_Tm_comm_ind t28 k d0 s s0) (subst_subst0_Tm_comm_ind t29 k d0 s s0))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t27 (HS ty k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t27 k d0 s s0) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (subst_subst0_Tm_comm_ind t28 k d0 s s0) (subst_subst0_Tm_comm_ind t29 k d0 s s0))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (subst_subst0_Tm_comm_ind t28 k d0 s s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) (S1 : Ty) {struct s0} :
    ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS ty d0) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS ty d0) k) s s0))) with
        | (var x13) => (substTy_tsubstIndex0_commleft_ind d0 s S1 k x13)
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t27 (HS tm k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t28 k d0 s S1) (subst_tsubst0_Tm_comm_ind t29 k d0 s S1))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t27 (HS ty k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t27 k d0 s S1) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (subst_tsubst0_Tm_comm_ind t28 k d0 s S1) (subst_tsubst0_Tm_comm_ind t29 k d0 s S1))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (subst_tsubst0_Tm_comm_ind t28 k d0 s S1) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) with
        | (var x13) => (tsubstTm_substIndex0_commright_ind d0 S1 s k x13)
        | (abs T43 t27) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t27 (HS tm k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t28 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t29 k d0 S1 s))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t27 (HS ty k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t27 k d0 S1 s) eq_refl)
        | (prod t28 t29) => (f_equal2 prod (tsubst_subst0_Tm_comm_ind t28 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t29 k d0 S1 s))
        | (lett p20 t28 t29) => (f_equal3 lett eq_refl (tsubst_subst0_Tm_comm_ind t28 k d0 S1 s) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS ty d0) k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS ty d0) k) S1 s))) with
        | (var x13) => eq_refl
        | (abs T43 t27) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T43 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t27 (HS tm k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t28 t29) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t28 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t29 k d0 S1 S2))
        | (tabs t27) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t27 (HS ty k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t27 T43) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t27 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T43 k d0 S1 S2))
        | (prod t28 t29) => (f_equal2 prod (tsubst_tsubst0_Tm_comm_ind t28 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t29 k d0 S1 S2))
        | (lett p20 t28 t29) => (f_equal3 lett (tsubst_tsubst0_Pat_comm_ind p20 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t28 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t29 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1 S2) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S3 : Ty) : (forall (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTy d0 S1 (tsubstTy X0 S2 S3)) = (tsubstTy X0 (tsubstTy d0 S1 S2) (tsubstTy (XS ty d0) S1 S3)))) := (tsubst_tsubst0_Ty_comm_ind S3 H0).
    Definition tsubstPat_tsubstPat0_comm (p20 : Pat) : (forall (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstPat d0 S1 (tsubstPat X0 S2 p20)) = (tsubstPat X0 (tsubstTy d0 S1 S2) (tsubstPat (XS ty d0) S1 p20)))) := (tsubst_tsubst0_Pat_comm_ind p20 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d0 s (substTm X0 s0 s1)) = (substTm X0 (substTm d0 s s0) (substTm (XS tm d0) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) (S1 : Ty) ,
      ((substTm d0 s (tsubstTm X0 S1 s0)) = (tsubstTm X0 S1 (substTm (XS ty d0) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) (s : Tm) ,
      ((tsubstTm d0 S1 (substTm X0 s s0)) = (substTm X0 (tsubstTm d0 S1 s) (tsubstTm d0 S1 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTm d0 S1 (tsubstTm X0 S2 s)) = (tsubstTm X0 (tsubstTy d0 S1 S2) (tsubstTm (XS ty d0) S1 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
        ((weakenTy (tsubstTy d0 S1 S2) k) = (tsubstTy (weakenTrace d0 k) S1 (weakenTy S2 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (p20 : Pat) ,
        ((weakenPat (tsubstPat d0 S1 p20) k) = (tsubstPat (weakenTrace d0 k) S1 (weakenPat p20 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d0 : (Trace tm)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d0 s s0) k) = (substTm (weakenTrace d0 k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d0 S1 s) k) = (tsubstTm (weakenTrace d0 k) S1 (weakenTm s k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite tsubstPat_tsubstPat0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite tsubstPat_tsubstPat0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenPat_tshiftPat weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenPat_tsubstPat weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
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
    | wfTy_tarr {T43 : Ty}
        (wf : (wfTy k T43)) {T44 : Ty}
        (wf0 : (wfTy k T44)) :
        (wfTy k (tarr T43 T44))
    | wfTy_tall {T45 : Ty}
        (wf : (wfTy (HS ty k) T45)) :
        (wfTy k (tall T45))
    | wfTy_tprod {T46 : Ty}
        (wf : (wfTy k T46)) {T47 : Ty}
        (wf0 : (wfTy k T47)) :
        (wfTy k (tprod T46 T47)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T43 : Ty}
        (wf : (wfTy k T43)) :
        (wfPat k (pvar T43))
    | wfPat_pprod {p20 : Pat}
        (wf : (wfPat k p20)) {p21 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bindPat p20))) p21))
        : (wfPat k (pprod p20 p21)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x13 : (Index tm))
        (wfi : (wfindex k x13)) :
        (wfTm k (var x13))
    | wfTm_abs {T43 : Ty}
        (wf : (wfTy k T43)) {t27 : Tm}
        (wf0 : (wfTm (HS tm k) t27)) :
        (wfTm k (abs T43 t27))
    | wfTm_app {t28 : Tm}
        (wf : (wfTm k t28)) {t29 : Tm}
        (wf0 : (wfTm k t29)) :
        (wfTm k (app t28 t29))
    | wfTm_tabs {t30 : Tm}
        (wf : (wfTm (HS ty k) t30)) :
        (wfTm k (tabs t30))
    | wfTm_tapp {t31 : Tm}
        (wf : (wfTm k t31)) {T44 : Ty}
        (wf0 : (wfTy k T44)) :
        (wfTm k (tapp t31 T44))
    | wfTm_prod {t32 : Tm}
        (wf : (wfTm k t32)) {t33 : Tm}
        (wf0 : (wfTm k t33)) :
        (wfTm k (prod t32 t33))
    | wfTm_lett {p20 : Pat}
        (wf : (wfPat k p20)) {t34 : Tm}
        (wf0 : (wfTm k t34)) {t35 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bindPat p20))) t35))
        : (wfTm k (lett p20 t34 t35)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H24 : (wfTy k (tvar X))) : (wfindex k X) := match H24 in (wfTy _ S1) return match S1 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H25 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T1) := match H25 in (wfTy _ S2) return match S2 return Prop with
    | (tarr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H25 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T2) := match H25 in (wfTy _ S2) return match S2 return Prop with
    | (tarr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k1 : Hvl) (T : Ty) (H26 : (wfTy k1 (tall T))) : (wfTy (HS ty k1) T) := match H26 in (wfTy _ S3) return match S3 return Prop with
    | (tall T) => (wfTy (HS ty k1) T)
    | _ => True
  end with
    | (wfTy_tall T H4) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tprod_0 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k2 (tprod T1 T2))) : (wfTy k2 T1) := match H27 in (wfTy _ S4) return match S4 return Prop with
    | (tprod T1 T2) => (wfTy k2 T1)
    | _ => True
  end with
    | (wfTy_tprod T1 H5 T2 H6) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tprod_1 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k2 (tprod T1 T2))) : (wfTy k2 T2) := match H27 in (wfTy _ S4) return match S4 return Prop with
    | (tprod T1 T2) => (wfTy k2 T2)
    | _ => True
  end with
    | (wfTy_tprod T1 H5 T2 H6) => H6
    | _ => I
  end.
  Definition inversion_wfPat_pvar_1 (k3 : Hvl) (T : Ty) (H28 : (wfPat k3 (pvar T))) : (wfTy k3 T) := match H28 in (wfPat _ p20) return match p20 return Prop with
    | (pvar T) => (wfTy k3 T)
    | _ => True
  end with
    | (wfPat_pvar T H7) => H7
    | _ => I
  end.
  Definition inversion_wfPat_pprod_0 (k4 : Hvl) (p1 : Pat) (p2 : Pat) (H29 : (wfPat k4 (pprod p1 p2))) : (wfPat k4 p1) := match H29 in (wfPat _ p21) return match p21 return Prop with
    | (pprod p1 p2) => (wfPat k4 p1)
    | _ => True
  end with
    | (wfPat_pprod p1 H8 p2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfPat_pprod_1 (k4 : Hvl) (p1 : Pat) (p2 : Pat) (H29 : (wfPat k4 (pprod p1 p2))) : (wfPat (appendHvl k4 (appendHvl H0 (bindPat p1))) p2) := match H29 in (wfPat _ p21) return match p21 return Prop with
    | (pprod p1 p2) => (wfPat (appendHvl k4 (appendHvl H0 (bindPat p1))) p2)
    | _ => True
  end with
    | (wfPat_pprod p1 H8 p2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k5 : Hvl) (x : (Index tm)) (H30 : (wfTm k5 (var x))) : (wfindex k5 x) := match H30 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k5 x)
    | _ => True
  end with
    | (wfTm_var x H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k6 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTm k6 (abs T t))) : (wfTy k6 T) := match H31 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k6 T)
    | _ => True
  end with
    | (wfTm_abs T H11 t H12) => H11
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k6 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTm k6 (abs T t))) : (wfTm (HS tm k6) t) := match H31 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k6) t)
    | _ => True
  end with
    | (wfTm_abs T H11 t H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k7 : Hvl) (t1 : Tm) (t2 : Tm) (H32 : (wfTm k7 (app t1 t2))) : (wfTm k7 t1) := match H32 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k7 t1)
    | _ => True
  end with
    | (wfTm_app t1 H13 t2 H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k7 : Hvl) (t1 : Tm) (t2 : Tm) (H32 : (wfTm k7 (app t1 t2))) : (wfTm k7 t2) := match H32 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k7 t2)
    | _ => True
  end with
    | (wfTm_app t1 H13 t2 H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k8 : Hvl) (t : Tm) (H33 : (wfTm k8 (tabs t))) : (wfTm (HS ty k8) t) := match H33 in (wfTm _ s2) return match s2 return Prop with
    | (tabs t) => (wfTm (HS ty k8) t)
    | _ => True
  end with
    | (wfTm_tabs t H15) => H15
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k9 : Hvl) (t : Tm) (T : Ty) (H34 : (wfTm k9 (tapp t T))) : (wfTm k9 t) := match H34 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k9 t)
    | _ => True
  end with
    | (wfTm_tapp t H16 T H17) => H16
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k9 : Hvl) (t : Tm) (T : Ty) (H34 : (wfTm k9 (tapp t T))) : (wfTy k9 T) := match H34 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k9 T)
    | _ => True
  end with
    | (wfTm_tapp t H16 T H17) => H17
    | _ => I
  end.
  Definition inversion_wfTm_prod_0 (k10 : Hvl) (t1 : Tm) (t2 : Tm) (H35 : (wfTm k10 (prod t1 t2))) : (wfTm k10 t1) := match H35 in (wfTm _ s4) return match s4 return Prop with
    | (prod t1 t2) => (wfTm k10 t1)
    | _ => True
  end with
    | (wfTm_prod t1 H18 t2 H19) => H18
    | _ => I
  end.
  Definition inversion_wfTm_prod_1 (k10 : Hvl) (t1 : Tm) (t2 : Tm) (H35 : (wfTm k10 (prod t1 t2))) : (wfTm k10 t2) := match H35 in (wfTm _ s4) return match s4 return Prop with
    | (prod t1 t2) => (wfTm k10 t2)
    | _ => True
  end with
    | (wfTm_prod t1 H18 t2 H19) => H19
    | _ => I
  end.
  Definition inversion_wfTm_lett_0 (k11 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k11 (lett p t1 t2))) : (wfPat k11 p) := match H36 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfPat k11 p)
    | _ => True
  end with
    | (wfTm_lett p H20 t1 H21 t2 H22) => H20
    | _ => I
  end.
  Definition inversion_wfTm_lett_1 (k11 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k11 (lett p t1 t2))) : (wfTm k11 t1) := match H36 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfTm k11 t1)
    | _ => True
  end with
    | (wfTm_lett p H20 t1 H21 t2 H22) => H21
    | _ => I
  end.
  Definition inversion_wfTm_lett_2 (k11 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k11 (lett p t1 t2))) : (wfTm (appendHvl k11 (appendHvl H0 (bindPat p))) t2) := match H36 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfTm (appendHvl k11 (appendHvl H0 (bindPat p))) t2)
    | _ => True
  end with
    | (wfTm_lett p H20 t1 H21 t2 H22) => H22
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c0 : (Cutoff tm)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k12 : Hvl)
        :
        (shifthvl_tm C0 k12 (HS tm k12))
    | shifthvl_tm_there_tm
        (c0 : (Cutoff tm)) (k12 : Hvl)
        (k13 : Hvl) :
        (shifthvl_tm c0 k12 k13) -> (shifthvl_tm (CS c0) (HS tm k12) (HS tm k13))
    | shifthvl_tm_there_ty
        (c0 : (Cutoff tm)) (k12 : Hvl)
        (k13 : Hvl) :
        (shifthvl_tm c0 k12 k13) -> (shifthvl_tm c0 (HS ty k12) (HS ty k13)).
  Inductive shifthvl_ty : (forall (c0 : (Cutoff ty)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k12 : Hvl)
        :
        (shifthvl_ty C0 k12 (HS ty k12))
    | shifthvl_ty_there_tm
        (c0 : (Cutoff ty)) (k12 : Hvl)
        (k13 : Hvl) :
        (shifthvl_ty c0 k12 k13) -> (shifthvl_ty c0 (HS tm k12) (HS tm k13))
    | shifthvl_ty_there_ty
        (c0 : (Cutoff ty)) (k12 : Hvl)
        (k13 : Hvl) :
        (shifthvl_ty c0 k12 k13) -> (shifthvl_ty (CS c0) (HS ty k12) (HS ty k13)).
  Lemma weaken_shifthvl_tm  :
    (forall (k12 : Hvl) {c0 : (Cutoff tm)} {k13 : Hvl} {k14 : Hvl} ,
      (shifthvl_tm c0 k13 k14) -> (shifthvl_tm (weakenCutofftm c0 k12) (appendHvl k13 k12) (appendHvl k14 k12))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k12 : Hvl) {c0 : (Cutoff ty)} {k13 : Hvl} {k14 : Hvl} ,
      (shifthvl_ty c0 k13 k14) -> (shifthvl_ty (weakenCutoffty c0 k12) (appendHvl k13 k12) (appendHvl k14 k12))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c0 : (Cutoff tm)) (k12 : Hvl) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) (x13 : (Index tm)) ,
      (wfindex k12 x13) -> (wfindex k13 (shiftIndex c0 x13))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c0 : (Cutoff tm)) (k12 : Hvl) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) (X12 : (Index ty)) ,
      (wfindex k12 X12) -> (wfindex k13 X12)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c0 : (Cutoff ty)) (k12 : Hvl) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) (x13 : (Index tm)) ,
      (wfindex k12 x13) -> (wfindex k13 x13)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c0 : (Cutoff ty)) (k12 : Hvl) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) (X12 : (Index ty)) ,
      (wfindex k12 X12) -> (wfindex k13 (tshiftIndex c0 X12))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k12 : Hvl) ,
    (forall (S5 : Ty) (wf : (wfTy k12 S5)) ,
      (forall (c0 : (Cutoff tm)) (k13 : Hvl) ,
        (shifthvl_tm c0 k12 k13) -> (wfTy k13 S5)))) := (ind_wfTy (fun (k12 : Hvl) (S5 : Ty) (wf : (wfTy k12 S5)) =>
    (forall (c0 : (Cutoff tm)) (k13 : Hvl) ,
      (shifthvl_tm c0 k12 k13) -> (wfTy k13 S5))) (fun (k12 : Hvl) (X12 : (Index ty)) (wfi : (wfindex k12 X12)) (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTy_tvar k13 _ (shift_wfindex_ty c0 k12 k13 ins X12 wfi))) (fun (k12 : Hvl) (T1 : Ty) (wf : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k12 T2)) IHT2 (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTy_tarr k13 (IHT1 c0 k13 (weaken_shifthvl_tm H0 ins)) (IHT2 c0 k13 (weaken_shifthvl_tm H0 ins)))) (fun (k12 : Hvl) (T : Ty) (wf : (wfTy (HS ty k12) T)) IHT (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTy_tall k13 (IHT c0 (HS ty k13) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k12 : Hvl) (T1 : Ty) (wf : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k12 T2)) IHT2 (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTy_tprod k13 (IHT1 c0 k13 (weaken_shifthvl_tm H0 ins)) (IHT2 c0 k13 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTy : (forall (k12 : Hvl) ,
    (forall (S5 : Ty) (wf : (wfTy k12 S5)) ,
      (forall (c0 : (Cutoff ty)) (k13 : Hvl) ,
        (shifthvl_ty c0 k12 k13) -> (wfTy k13 (tshiftTy c0 S5))))) := (ind_wfTy (fun (k12 : Hvl) (S5 : Ty) (wf : (wfTy k12 S5)) =>
    (forall (c0 : (Cutoff ty)) (k13 : Hvl) ,
      (shifthvl_ty c0 k12 k13) -> (wfTy k13 (tshiftTy c0 S5)))) (fun (k12 : Hvl) (X12 : (Index ty)) (wfi : (wfindex k12 X12)) (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTy_tvar k13 _ (tshift_wfindex_ty c0 k12 k13 ins X12 wfi))) (fun (k12 : Hvl) (T1 : Ty) (wf : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k12 T2)) IHT2 (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTy_tarr k13 (IHT1 c0 k13 (weaken_shifthvl_ty H0 ins)) (IHT2 c0 k13 (weaken_shifthvl_ty H0 ins)))) (fun (k12 : Hvl) (T : Ty) (wf : (wfTy (HS ty k12) T)) IHT (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTy_tall k13 (IHT (CS c0) (HS ty k13) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k12 : Hvl) (T1 : Ty) (wf : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k12 T2)) IHT2 (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTy_tprod k13 (IHT1 c0 k13 (weaken_shifthvl_ty H0 ins)) (IHT2 c0 k13 (weaken_shifthvl_ty H0 ins))))).
  Definition shift_wfPat : (forall (k12 : Hvl) ,
    (forall (p22 : Pat) (wf : (wfPat k12 p22)) ,
      (forall (c0 : (Cutoff tm)) (k13 : Hvl) ,
        (shifthvl_tm c0 k12 k13) -> (wfPat k13 p22)))) := (ind_wfPat (fun (k12 : Hvl) (p22 : Pat) (wf : (wfPat k12 p22)) =>
    (forall (c0 : (Cutoff tm)) (k13 : Hvl) ,
      (shifthvl_tm c0 k12 k13) -> (wfPat k13 p22))) (fun (k12 : Hvl) (T : Ty) (wf : (wfTy k12 T)) (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfPat_pvar k13 (shift_wfTy k12 T wf c0 k13 (weaken_shifthvl_tm H0 ins)))) (fun (k12 : Hvl) (p1 : Pat) (wf : (wfPat k12 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k12 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfPat_pprod k13 (IHp1 c0 k13 (weaken_shifthvl_tm H0 ins)) (IHp2 (weakenCutofftm c0 (appendHvl H0 (bindPat p1))) (appendHvl k13 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p1)) ins))))).
  Definition tshift_wfPat : (forall (k12 : Hvl) ,
    (forall (p22 : Pat) (wf : (wfPat k12 p22)) ,
      (forall (c0 : (Cutoff ty)) (k13 : Hvl) ,
        (shifthvl_ty c0 k12 k13) -> (wfPat k13 (tshiftPat c0 p22))))) := (ind_wfPat (fun (k12 : Hvl) (p22 : Pat) (wf : (wfPat k12 p22)) =>
    (forall (c0 : (Cutoff ty)) (k13 : Hvl) ,
      (shifthvl_ty c0 k12 k13) -> (wfPat k13 (tshiftPat c0 p22)))) (fun (k12 : Hvl) (T : Ty) (wf : (wfTy k12 T)) (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfPat_pvar k13 (tshift_wfTy k12 T wf c0 k13 (weaken_shifthvl_ty H0 ins)))) (fun (k12 : Hvl) (p1 : Pat) (wf : (wfPat k12 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k12 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfPat_pprod k13 (IHp1 c0 k13 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k13) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHp2 (weakenCutoffty c0 (appendHvl H0 (bindPat p1))) (appendHvl k13 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p1)) ins)))))).
  Definition shift_wfTm : (forall (k12 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k12 s6)) ,
      (forall (c0 : (Cutoff tm)) (k13 : Hvl) ,
        (shifthvl_tm c0 k12 k13) -> (wfTm k13 (shiftTm c0 s6))))) := (ind_wfTm (fun (k12 : Hvl) (s6 : Tm) (wf : (wfTm k12 s6)) =>
    (forall (c0 : (Cutoff tm)) (k13 : Hvl) ,
      (shifthvl_tm c0 k12 k13) -> (wfTm k13 (shiftTm c0 s6)))) (fun (k12 : Hvl) (x13 : (Index tm)) (wfi : (wfindex k12 x13)) (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTm_var k13 _ (shift_wfindex_tm c0 k12 k13 ins x13 wfi))) (fun (k12 : Hvl) (T : Ty) (wf : (wfTy k12 T)) (t : Tm) (wf0 : (wfTm (HS tm k12) t)) IHt (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTm_abs k13 (shift_wfTy k12 T wf c0 k13 (weaken_shifthvl_tm H0 ins)) (IHt (CS c0) (HS tm k13) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k12 : Hvl) (t1 : Tm) (wf : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k12 t2)) IHt2 (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTm_app k13 (IHt1 c0 k13 (weaken_shifthvl_tm H0 ins)) (IHt2 c0 k13 (weaken_shifthvl_tm H0 ins)))) (fun (k12 : Hvl) (t : Tm) (wf : (wfTm (HS ty k12) t)) IHt (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTm_tabs k13 (IHt c0 (HS ty k13) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k12 : Hvl) (t : Tm) (wf : (wfTm k12 t)) IHt (T : Ty) (wf0 : (wfTy k12 T)) (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTm_tapp k13 (IHt c0 k13 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k12 T wf0 c0 k13 (weaken_shifthvl_tm H0 ins)))) (fun (k12 : Hvl) (t1 : Tm) (wf : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k12 t2)) IHt2 (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTm_prod k13 (IHt1 c0 k13 (weaken_shifthvl_tm H0 ins)) (IHt2 c0 k13 (weaken_shifthvl_tm H0 ins)))) (fun (k12 : Hvl) (p : Pat) (wf : (wfPat k12 p)) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k12 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff tm)) (k13 : Hvl) (ins : (shifthvl_tm c0 k12 k13)) =>
    (wfTm_lett k13 (shift_wfPat k12 p wf c0 k13 (weaken_shifthvl_tm H0 ins)) (IHt1 c0 k13 (weaken_shifthvl_tm H0 ins)) (IHt2 (weakenCutofftm c0 (appendHvl H0 (bindPat p))) (appendHvl k13 (appendHvl H0 (bindPat p))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p)) ins))))).
  Definition tshift_wfTm : (forall (k12 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k12 s6)) ,
      (forall (c0 : (Cutoff ty)) (k13 : Hvl) ,
        (shifthvl_ty c0 k12 k13) -> (wfTm k13 (tshiftTm c0 s6))))) := (ind_wfTm (fun (k12 : Hvl) (s6 : Tm) (wf : (wfTm k12 s6)) =>
    (forall (c0 : (Cutoff ty)) (k13 : Hvl) ,
      (shifthvl_ty c0 k12 k13) -> (wfTm k13 (tshiftTm c0 s6)))) (fun (k12 : Hvl) (x13 : (Index tm)) (wfi : (wfindex k12 x13)) (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTm_var k13 _ (tshift_wfindex_tm c0 k12 k13 ins x13 wfi))) (fun (k12 : Hvl) (T : Ty) (wf : (wfTy k12 T)) (t : Tm) (wf0 : (wfTm (HS tm k12) t)) IHt (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTm_abs k13 (tshift_wfTy k12 T wf c0 k13 (weaken_shifthvl_ty H0 ins)) (IHt c0 (HS tm k13) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k12 : Hvl) (t1 : Tm) (wf : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k12 t2)) IHt2 (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTm_app k13 (IHt1 c0 k13 (weaken_shifthvl_ty H0 ins)) (IHt2 c0 k13 (weaken_shifthvl_ty H0 ins)))) (fun (k12 : Hvl) (t : Tm) (wf : (wfTm (HS ty k12) t)) IHt (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTm_tabs k13 (IHt (CS c0) (HS ty k13) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k12 : Hvl) (t : Tm) (wf : (wfTm k12 t)) IHt (T : Ty) (wf0 : (wfTy k12 T)) (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTm_tapp k13 (IHt c0 k13 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k12 T wf0 c0 k13 (weaken_shifthvl_ty H0 ins)))) (fun (k12 : Hvl) (t1 : Tm) (wf : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k12 t2)) IHt2 (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTm_prod k13 (IHt1 c0 k13 (weaken_shifthvl_ty H0 ins)) (IHt2 c0 k13 (weaken_shifthvl_ty H0 ins)))) (fun (k12 : Hvl) (p : Pat) (wf : (wfPat k12 p)) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k12 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff ty)) (k13 : Hvl) (ins : (shifthvl_ty c0 k12 k13)) =>
    (wfTm_lett k13 (tshift_wfPat k12 p wf c0 k13 (weaken_shifthvl_ty H0 ins)) (IHt1 c0 k13 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k13) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHt2 (weakenCutoffty c0 (appendHvl H0 (bindPat p))) (appendHvl k13 (appendHvl H0 (bindPat p))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p)) ins)))))).
  Fixpoint weaken_wfTy (k12 : Hvl) {struct k12} :
  (forall (k13 : Hvl) (S5 : Ty) (wf : (wfTy k13 S5)) ,
    (wfTy (appendHvl k13 k12) (weakenTy S5 k12))) :=
    match k12 return (forall (k13 : Hvl) (S5 : Ty) (wf : (wfTy k13 S5)) ,
      (wfTy (appendHvl k13 k12) (weakenTy S5 k12))) with
      | (H0) => (fun (k13 : Hvl) (S5 : Ty) (wf : (wfTy k13 S5)) =>
        wf)
      | (HS tm k12) => (fun (k13 : Hvl) (S5 : Ty) (wf : (wfTy k13 S5)) =>
        (shift_wfTy (appendHvl k13 k12) (weakenTy S5 k12) (weaken_wfTy k12 k13 S5 wf) C0 (HS tm (appendHvl k13 k12)) (shifthvl_tm_here (appendHvl k13 k12))))
      | (HS ty k12) => (fun (k13 : Hvl) (S5 : Ty) (wf : (wfTy k13 S5)) =>
        (tshift_wfTy (appendHvl k13 k12) (weakenTy S5 k12) (weaken_wfTy k12 k13 S5 wf) C0 (HS ty (appendHvl k13 k12)) (shifthvl_ty_here (appendHvl k13 k12))))
    end.
  Fixpoint weaken_wfPat (k12 : Hvl) {struct k12} :
  (forall (k13 : Hvl) (p22 : Pat) (wf : (wfPat k13 p22)) ,
    (wfPat (appendHvl k13 k12) (weakenPat p22 k12))) :=
    match k12 return (forall (k13 : Hvl) (p22 : Pat) (wf : (wfPat k13 p22)) ,
      (wfPat (appendHvl k13 k12) (weakenPat p22 k12))) with
      | (H0) => (fun (k13 : Hvl) (p22 : Pat) (wf : (wfPat k13 p22)) =>
        wf)
      | (HS tm k12) => (fun (k13 : Hvl) (p22 : Pat) (wf : (wfPat k13 p22)) =>
        (shift_wfPat (appendHvl k13 k12) (weakenPat p22 k12) (weaken_wfPat k12 k13 p22 wf) C0 (HS tm (appendHvl k13 k12)) (shifthvl_tm_here (appendHvl k13 k12))))
      | (HS ty k12) => (fun (k13 : Hvl) (p22 : Pat) (wf : (wfPat k13 p22)) =>
        (tshift_wfPat (appendHvl k13 k12) (weakenPat p22 k12) (weaken_wfPat k12 k13 p22 wf) C0 (HS ty (appendHvl k13 k12)) (shifthvl_ty_here (appendHvl k13 k12))))
    end.
  Fixpoint weaken_wfTm (k12 : Hvl) {struct k12} :
  (forall (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) ,
    (wfTm (appendHvl k13 k12) (weakenTm s6 k12))) :=
    match k12 return (forall (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) ,
      (wfTm (appendHvl k13 k12) (weakenTm s6 k12))) with
      | (H0) => (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
        wf)
      | (HS tm k12) => (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
        (shift_wfTm (appendHvl k13 k12) (weakenTm s6 k12) (weaken_wfTm k12 k13 s6 wf) C0 (HS tm (appendHvl k13 k12)) (shifthvl_tm_here (appendHvl k13 k12))))
      | (HS ty k12) => (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
        (tshift_wfTm (appendHvl k13 k12) (weakenTm s6 k12) (weaken_wfTm k12 k13 s6 wf) C0 (HS ty (appendHvl k13 k12)) (shifthvl_ty_here (appendHvl k13 k12))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k16 : Hvl) (S6 : Ty) (k17 : Hvl) (S7 : Ty) ,
    (k16 = k17) -> (S6 = S7) -> (wfTy k16 S6) -> (wfTy k17 S7)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k16 : Hvl) (p23 : Pat) (k17 : Hvl) (p24 : Pat) ,
    (k16 = k17) -> (p23 = p24) -> (wfPat k16 p23) -> (wfPat k17 p24)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k16 : Hvl) (s6 : Tm) (k17 : Hvl) (s7 : Tm) ,
    (k16 = k17) -> (s6 = s7) -> (wfTm k16 s6) -> (wfTm k17 s7)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k12 : Hvl) : (forall (d0 : (Trace tm)) (k13 : Hvl) (k14 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k12 X0 (HS tm k12) k12)
    | substhvl_tm_there_tm
        {d0 : (Trace tm)} {k13 : Hvl}
        {k14 : Hvl} :
        (substhvl_tm k12 d0 k13 k14) -> (substhvl_tm k12 (XS tm d0) (HS tm k13) (HS tm k14))
    | substhvl_tm_there_ty
        {d0 : (Trace tm)} {k13 : Hvl}
        {k14 : Hvl} :
        (substhvl_tm k12 d0 k13 k14) -> (substhvl_tm k12 (XS ty d0) (HS ty k13) (HS ty k14)).
  Inductive substhvl_ty (k12 : Hvl) : (forall (d0 : (Trace ty)) (k13 : Hvl) (k14 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k12 X0 (HS ty k12) k12)
    | substhvl_ty_there_tm
        {d0 : (Trace ty)} {k13 : Hvl}
        {k14 : Hvl} :
        (substhvl_ty k12 d0 k13 k14) -> (substhvl_ty k12 (XS tm d0) (HS tm k13) (HS tm k14))
    | substhvl_ty_there_ty
        {d0 : (Trace ty)} {k13 : Hvl}
        {k14 : Hvl} :
        (substhvl_ty k12 d0 k13 k14) -> (substhvl_ty k12 (XS ty d0) (HS ty k13) (HS ty k14)).
  Lemma weaken_substhvl_tm  :
    (forall {k13 : Hvl} (k12 : Hvl) {d0 : (Trace tm)} {k14 : Hvl} {k15 : Hvl} ,
      (substhvl_tm k13 d0 k14 k15) -> (substhvl_tm k13 (weakenTrace d0 k12) (appendHvl k14 k12) (appendHvl k15 k12))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k13 : Hvl} (k12 : Hvl) {d0 : (Trace ty)} {k14 : Hvl} {k15 : Hvl} ,
      (substhvl_ty k13 d0 k14 k15) -> (substhvl_ty k13 (weakenTrace d0 k12) (appendHvl k14 k12) (appendHvl k15 k12))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k16 : Hvl} {s6 : Tm} (wft : (wfTm k16 s6)) :
    (forall {d0 : (Trace tm)} {k17 : Hvl} {k18 : Hvl} ,
      (substhvl_tm k16 d0 k17 k18) -> (forall {x13 : (Index tm)} ,
        (wfindex k17 x13) -> (wfTm k18 (substIndex d0 s6 x13)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k16 : Hvl} {S6 : Ty} (wft : (wfTy k16 S6)) :
    (forall {d0 : (Trace ty)} {k17 : Hvl} {k18 : Hvl} ,
      (substhvl_ty k16 d0 k17 k18) -> (forall {X12 : (Index ty)} ,
        (wfindex k17 X12) -> (wfTy k18 (tsubstIndex d0 S6 X12)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k16 : Hvl} :
    (forall {d0 : (Trace tm)} {k17 : Hvl} {k18 : Hvl} ,
      (substhvl_tm k16 d0 k17 k18) -> (forall {X12 : (Index ty)} ,
        (wfindex k17 X12) -> (wfindex k18 X12))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k16 : Hvl} :
    (forall {d0 : (Trace ty)} {k17 : Hvl} {k18 : Hvl} ,
      (substhvl_ty k16 d0 k17 k18) -> (forall {x13 : (Index tm)} ,
        (wfindex k17 x13) -> (wfindex k18 x13))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k16 : Hvl} : (forall (k17 : Hvl) ,
    (forall (S6 : Ty) (wf0 : (wfTy k17 S6)) ,
      (forall {d0 : (Trace tm)} {k18 : Hvl} ,
        (substhvl_tm k16 d0 k17 k18) -> (wfTy k18 S6)))) := (ind_wfTy (fun (k17 : Hvl) (S6 : Ty) (wf0 : (wfTy k17 S6)) =>
    (forall {d0 : (Trace tm)} {k18 : Hvl} ,
      (substhvl_tm k16 d0 k17 k18) -> (wfTy k18 S6))) (fun (k17 : Hvl) {X12 : (Index ty)} (wfi : (wfindex k17 X12)) {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTy_tvar k18 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k17 : Hvl) (T1 : Ty) (wf0 : (wfTy k17 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k17 T2)) IHT2 {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTy_tarr k18 (IHT1 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)))) (fun (k17 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k17) T)) IHT {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTy_tall k18 (IHT (weakenTrace d0 (HS ty H0)) (HS ty k18) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k17 : Hvl) (T1 : Ty) (wf0 : (wfTy k17 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k17 T2)) IHT2 {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTy_tprod k18 (IHT1 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTy {k16 : Hvl} {S6 : Ty} (wf : (wfTy k16 S6)) : (forall (k17 : Hvl) ,
    (forall (S7 : Ty) (wf0 : (wfTy k17 S7)) ,
      (forall {d0 : (Trace ty)} {k18 : Hvl} ,
        (substhvl_ty k16 d0 k17 k18) -> (wfTy k18 (tsubstTy d0 S6 S7))))) := (ind_wfTy (fun (k17 : Hvl) (S7 : Ty) (wf0 : (wfTy k17 S7)) =>
    (forall {d0 : (Trace ty)} {k18 : Hvl} ,
      (substhvl_ty k16 d0 k17 k18) -> (wfTy k18 (tsubstTy d0 S6 S7)))) (fun (k17 : Hvl) {X12 : (Index ty)} (wfi : (wfindex k17 X12)) {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k17 : Hvl) (T1 : Ty) (wf0 : (wfTy k17 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k17 T2)) IHT2 {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTy_tarr k18 (IHT1 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)))) (fun (k17 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k17) T)) IHT {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTy_tall k18 (IHT (weakenTrace d0 (HS ty H0)) (HS ty k18) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k17 : Hvl) (T1 : Ty) (wf0 : (wfTy k17 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k17 T2)) IHT2 {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTy_tprod k18 (IHT1 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del))))).
  Definition substhvl_tm_wfPat {k16 : Hvl} : (forall (k17 : Hvl) ,
    (forall (p23 : Pat) (wf0 : (wfPat k17 p23)) ,
      (forall {d0 : (Trace tm)} {k18 : Hvl} ,
        (substhvl_tm k16 d0 k17 k18) -> (wfPat k18 p23)))) := (ind_wfPat (fun (k17 : Hvl) (p23 : Pat) (wf0 : (wfPat k17 p23)) =>
    (forall {d0 : (Trace tm)} {k18 : Hvl} ,
      (substhvl_tm k16 d0 k17 k18) -> (wfPat k18 p23))) (fun (k17 : Hvl) (T : Ty) (wf0 : (wfTy k17 T)) {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfPat_pvar k18 (substhvl_tm_wfTy k17 T wf0 (weaken_substhvl_tm H0 del)))) (fun (k17 : Hvl) (p1 : Pat) (wf0 : (wfPat k17 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k17 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfPat_pprod k18 (IHp1 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)) (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k18 (appendHvl H0 (bindPat p1))) (weaken_substhvl_tm (appendHvl H0 (bindPat p1)) del))))).
  Definition substhvl_ty_wfPat {k16 : Hvl} {S6 : Ty} (wf : (wfTy k16 S6)) : (forall (k17 : Hvl) ,
    (forall (p23 : Pat) (wf0 : (wfPat k17 p23)) ,
      (forall {d0 : (Trace ty)} {k18 : Hvl} ,
        (substhvl_ty k16 d0 k17 k18) -> (wfPat k18 (tsubstPat d0 S6 p23))))) := (ind_wfPat (fun (k17 : Hvl) (p23 : Pat) (wf0 : (wfPat k17 p23)) =>
    (forall {d0 : (Trace ty)} {k18 : Hvl} ,
      (substhvl_ty k16 d0 k17 k18) -> (wfPat k18 (tsubstPat d0 S6 p23)))) (fun (k17 : Hvl) (T : Ty) (wf0 : (wfTy k17 T)) {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfPat_pvar k18 (substhvl_ty_wfTy wf k17 T wf0 (weaken_substhvl_ty H0 del)))) (fun (k17 : Hvl) (p1 : Pat) (wf0 : (wfPat k17 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k17 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfPat_pprod k18 (IHp1 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k18) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k18 (appendHvl H0 (bindPat p1))) (weaken_substhvl_ty (appendHvl H0 (bindPat p1)) del)))))).
  Definition substhvl_tm_wfTm {k16 : Hvl} {s6 : Tm} (wf : (wfTm k16 s6)) : (forall (k17 : Hvl) ,
    (forall (s7 : Tm) (wf0 : (wfTm k17 s7)) ,
      (forall {d0 : (Trace tm)} {k18 : Hvl} ,
        (substhvl_tm k16 d0 k17 k18) -> (wfTm k18 (substTm d0 s6 s7))))) := (ind_wfTm (fun (k17 : Hvl) (s7 : Tm) (wf0 : (wfTm k17 s7)) =>
    (forall {d0 : (Trace tm)} {k18 : Hvl} ,
      (substhvl_tm k16 d0 k17 k18) -> (wfTm k18 (substTm d0 s6 s7)))) (fun (k17 : Hvl) {x13 : (Index tm)} (wfi : (wfindex k17 x13)) {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k17 : Hvl) (T : Ty) (wf0 : (wfTy k17 T)) (t : Tm) (wf1 : (wfTm (HS tm k17) t)) IHt {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTm_abs k18 (substhvl_tm_wfTy k17 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d0 (HS tm H0)) (HS tm k18) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k17 : Hvl) (t1 : Tm) (wf0 : (wfTm k17 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k17 t2)) IHt2 {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTm_app k18 (IHt1 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)))) (fun (k17 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k17) t)) IHt {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTm_tabs k18 (IHt (weakenTrace d0 (HS ty H0)) (HS ty k18) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k17 : Hvl) (t : Tm) (wf0 : (wfTm k17 t)) IHt (T : Ty) (wf1 : (wfTy k17 T)) {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTm_tapp k18 (IHt (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k17 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k17 : Hvl) (t1 : Tm) (wf0 : (wfTm k17 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k17 t2)) IHt2 {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTm_prod k18 (IHt1 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)))) (fun (k17 : Hvl) (p : Pat) (wf0 : (wfPat k17 p)) (t1 : Tm) (wf1 : (wfTm k17 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k17 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace tm)} {k18 : Hvl} (del : (substhvl_tm k16 d0 k17 k18)) =>
    (wfTm_lett k18 (substhvl_tm_wfPat k17 p wf0 (weaken_substhvl_tm H0 del)) (IHt1 (weakenTrace d0 H0) k18 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k18 (appendHvl H0 (bindPat p))) (weaken_substhvl_tm (appendHvl H0 (bindPat p)) del))))).
  Definition substhvl_ty_wfTm {k16 : Hvl} {S6 : Ty} (wf : (wfTy k16 S6)) : (forall (k17 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k17 s6)) ,
      (forall {d0 : (Trace ty)} {k18 : Hvl} ,
        (substhvl_ty k16 d0 k17 k18) -> (wfTm k18 (tsubstTm d0 S6 s6))))) := (ind_wfTm (fun (k17 : Hvl) (s6 : Tm) (wf0 : (wfTm k17 s6)) =>
    (forall {d0 : (Trace ty)} {k18 : Hvl} ,
      (substhvl_ty k16 d0 k17 k18) -> (wfTm k18 (tsubstTm d0 S6 s6)))) (fun (k17 : Hvl) {x13 : (Index tm)} (wfi : (wfindex k17 x13)) {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTm_var k18 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k17 : Hvl) (T : Ty) (wf0 : (wfTy k17 T)) (t : Tm) (wf1 : (wfTm (HS tm k17) t)) IHt {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTm_abs k18 (substhvl_ty_wfTy wf k17 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d0 (HS tm H0)) (HS tm k18) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k17 : Hvl) (t1 : Tm) (wf0 : (wfTm k17 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k17 t2)) IHt2 {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTm_app k18 (IHt1 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)))) (fun (k17 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k17) t)) IHt {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTm_tabs k18 (IHt (weakenTrace d0 (HS ty H0)) (HS ty k18) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k17 : Hvl) (t : Tm) (wf0 : (wfTm k17 t)) IHt (T : Ty) (wf1 : (wfTy k17 T)) {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTm_tapp k18 (IHt (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k17 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k17 : Hvl) (t1 : Tm) (wf0 : (wfTm k17 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k17 t2)) IHt2 {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTm_prod k18 (IHt1 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)))) (fun (k17 : Hvl) (p : Pat) (wf0 : (wfPat k17 p)) (t1 : Tm) (wf1 : (wfTm k17 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k17 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace ty)} {k18 : Hvl} (del : (substhvl_ty k16 d0 k17 k18)) =>
    (wfTm_lett k18 (substhvl_ty_wfPat wf k17 p wf0 (weaken_substhvl_ty H0 del)) (IHt1 (weakenTrace d0 H0) k18 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k18) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k18 (appendHvl H0 (bindPat p))) (weaken_substhvl_ty (appendHvl H0 (bindPat p)) del)))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Fixpoint subhvl_tm (k16 : Hvl) {struct k16} :
Prop :=
  match k16 with
    | (H0) => True
    | (HS a k16) => match a with
      | (tm) => (subhvl_tm k16)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k16 : Hvl) (k17 : Hvl) ,
    (subhvl_tm k16) -> (subhvl_tm k17) -> (subhvl_tm (appendHvl k16 k17))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k13 : Hvl) (k12 : Hvl) (p22 : Pat) ,
    (subhvl_tm k13) -> (wfPat (appendHvl k12 k13) (weakenPat p22 k13)) -> (wfPat k12 p22)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k15 : Hvl) (k14 : Hvl) (S5 : Ty) ,
    (subhvl_tm k15) -> (wfTy (appendHvl k14 k15) (weakenTy S5 k15)) -> (wfTy k14 S5)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H40 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_tm) in H40
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H41 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H41
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G2 : Env) (T : Ty)
    | etvar (G2 : Env).
  Fixpoint appendEnv (G2 : Env) (G3 : Env) :
  Env :=
    match G3 with
      | (empty) => G2
      | (evar G4 T) => (evar (appendEnv G2 G4) T)
      | (etvar G4) => (etvar (appendEnv G2 G4))
    end.
  Fixpoint domainEnv (G2 : Env) :
  Hvl :=
    match G2 with
      | (empty) => H0
      | (evar G3 T) => (HS tm (domainEnv G3))
      | (etvar G3) => (HS ty (domainEnv G3))
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
  Fixpoint shiftEnv (c0 : (Cutoff tm)) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (shiftEnv c0 G3) T)
      | (etvar G3) => (etvar (shiftEnv c0 G3))
    end.
  Fixpoint tshiftEnv (c0 : (Cutoff ty)) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (tshiftEnv c0 G3) (tshiftTy (weakenCutoffty c0 (domainEnv G3)) T))
      | (etvar G3) => (etvar (tshiftEnv c0 G3))
    end.
  Fixpoint weakenEnv (G2 : Env) (k16 : Hvl) {struct k16} :
  Env :=
    match k16 with
      | (H0) => G2
      | (HS tm k16) => (weakenEnv G2 k16)
      | (HS ty k16) => (tshiftEnv C0 (weakenEnv G2 k16))
    end.
  Fixpoint substEnv (d0 : (Trace tm)) (s6 : Tm) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (substEnv d0 s6 G3) T)
      | (etvar G3) => (etvar (substEnv d0 s6 G3))
    end.
  Fixpoint tsubstEnv (d0 : (Trace ty)) (S6 : Ty) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (tsubstEnv d0 S6 G3) (tsubstTy (weakenTrace d0 (domainEnv G3)) S6 T))
      | (etvar G3) => (etvar (tsubstEnv d0 S6 G3))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c0 : (Cutoff tm)) (G2 : Env) ,
      ((domainEnv (shiftEnv c0 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c0 : (Cutoff ty)) (G2 : Env) ,
      ((domainEnv (tshiftEnv c0 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d0 : (Trace tm)) (s6 : Tm) (G2 : Env) ,
      ((domainEnv (substEnv d0 s6 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d0 : (Trace ty)) (S6 : Ty) (G2 : Env) ,
      ((domainEnv (tsubstEnv d0 S6 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c0 : (Cutoff tm)) (G2 : Env) (G3 : Env) ,
        ((shiftEnv c0 (appendEnv G2 G3)) = (appendEnv (shiftEnv c0 G2) (shiftEnv (weakenCutofftm c0 (domainEnv G2)) G3)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c0 : (Cutoff ty)) (G2 : Env) (G3 : Env) ,
        ((tshiftEnv c0 (appendEnv G2 G3)) = (appendEnv (tshiftEnv c0 G2) (tshiftEnv (weakenCutoffty c0 (domainEnv G2)) G3)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d0 : (Trace tm)) (s6 : Tm) (G2 : Env) (G3 : Env) ,
        ((substEnv d0 s6 (appendEnv G2 G3)) = (appendEnv (substEnv d0 s6 G2) (substEnv (weakenTrace d0 (domainEnv G2)) s6 G3)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d0 : (Trace ty)) (S6 : Ty) (G2 : Env) (G3 : Env) ,
        ((tsubstEnv d0 S6 (appendEnv G2 G3)) = (appendEnv (tsubstEnv d0 S6 G2) (tsubstEnv (weakenTrace d0 (domainEnv G2)) S6 G3)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S6 : Ty) (k16 : Hvl) (k17 : Hvl) ,
      ((weakenTy (weakenTy S6 k16) k17) = (weakenTy S6 (appendHvl k16 k17)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p23 : Pat) (k16 : Hvl) (k17 : Hvl) ,
      ((weakenPat (weakenPat p23 k16) k17) = (weakenPat p23 (appendHvl k16 k17)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s6 : Tm) (k16 : Hvl) (k17 : Hvl) ,
      ((weakenTm (weakenTm s6 k16) k17) = (weakenTm s6 (appendHvl k16 k17)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G2 : Env}
          (T43 : Ty) :
          (wfTy (domainEnv G2) T43) -> (lookup_evar (evar G2 T43) I0 T43)
      | lookup_evar_there_evar
          {G2 : Env} {x13 : (Index tm)}
          (T44 : Ty) (T45 : Ty) :
          (lookup_evar G2 x13 T44) -> (lookup_evar (evar G2 T45) (IS x13) T44)
      | lookup_evar_there_etvar
          {G2 : Env} {x13 : (Index tm)}
          (T44 : Ty) :
          (lookup_evar G2 x13 T44) -> (lookup_evar (etvar G2) x13 (tshiftTy C0 T44)).
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G2 : Env}
          : (lookup_etvar (etvar G2) I0)
      | lookup_etvar_there_evar
          {G2 : Env} {X12 : (Index ty)}
          (T44 : Ty) :
          (lookup_etvar G2 X12) -> (lookup_etvar (evar G2 T44) X12)
      | lookup_etvar_there_etvar
          {G2 : Env} {X12 : (Index ty)} :
          (lookup_etvar G2 X12) -> (lookup_etvar (etvar G2) (IS X12)).
    Lemma lookup_evar_inversion_here  :
      (forall (G2 : Env) (T44 : Ty) (T45 : Ty) ,
        (lookup_evar (evar G2 T44) I0 T45) -> (T44 = T45)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G2 : Env} {x13 : (Index tm)} ,
        (forall (T44 : Ty) ,
          (lookup_evar G2 x13 T44) -> (forall (T45 : Ty) ,
            (lookup_evar G2 x13 T45) -> (T44 = T45)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G2 : Env} {x13 : (Index tm)} (T44 : Ty) ,
        (lookup_evar G2 x13 T44) -> (wfTy (domainEnv G2) T44)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G2 : Env} (G3 : Env) {x13 : (Index tm)} (T44 : Ty) ,
        (lookup_evar G2 x13 T44) -> (lookup_evar (appendEnv G2 G3) (weakenIndextm x13 (domainEnv G3)) (weakenTy T44 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G2 : Env} (G3 : Env) {X12 : (Index ty)} ,
        (lookup_etvar G2 X12) -> (lookup_etvar (appendEnv G2 G3) (weakenIndexty X12 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G2 : Env} {x13 : (Index tm)} (T46 : Ty) ,
        (lookup_evar G2 x13 T46) -> (wfindex (domainEnv G2) x13)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G2 : Env} {X12 : (Index ty)} ,
        (lookup_etvar G2 X12) -> (wfindex (domainEnv G2) X12)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G2 : Env}
        {T44 : Ty} :
        (shift_evar C0 G2 (evar G2 T44))
    | shiftevar_there_evar
        {c0 : (Cutoff tm)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_evar c0 G2 G3) -> (shift_evar (CS c0) (evar G2 T) (evar G3 T))
    | shiftevar_there_etvar
        {c0 : (Cutoff tm)} {G2 : Env}
        {G3 : Env} :
        (shift_evar c0 G2 G3) -> (shift_evar c0 (etvar G2) (etvar G3)).
  Lemma weaken_shift_evar  :
    (forall (G2 : Env) {c0 : (Cutoff tm)} {G3 : Env} {G4 : Env} ,
      (shift_evar c0 G3 G4) -> (shift_evar (weakenCutofftm c0 (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 G2))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G2 : Env}
        : (shift_etvar C0 G2 (etvar G2))
    | shiftetvar_there_evar
        {c0 : (Cutoff ty)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_etvar c0 G2 G3) -> (shift_etvar c0 (evar G2 T) (evar G3 (tshiftTy c0 T)))
    | shiftetvar_there_etvar
        {c0 : (Cutoff ty)} {G2 : Env}
        {G3 : Env} :
        (shift_etvar c0 G2 G3) -> (shift_etvar (CS c0) (etvar G2) (etvar G3)).
  Lemma weaken_shift_etvar  :
    (forall (G2 : Env) {c0 : (Cutoff ty)} {G3 : Env} {G4 : Env} ,
      (shift_etvar c0 G3 G4) -> (shift_etvar (weakenCutoffty c0 (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 (tshiftEnv c0 G2)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} ,
      (shift_evar c0 G2 G3) -> (shifthvl_tm c0 (domainEnv G2) (domainEnv G3))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} ,
      (shift_etvar c0 G2 G3) -> (shifthvl_ty c0 (domainEnv G2) (domainEnv G3))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G2 : Env) (T44 : Ty) (s6 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G2 T44 s6 X0 (evar G2 T44) G2)
    | subst_evar_there_evar
        {d0 : (Trace tm)} {G3 : Env}
        {G4 : Env} (T45 : Ty) :
        (subst_evar G2 T44 s6 d0 G3 G4) -> (subst_evar G2 T44 s6 (XS tm d0) (evar G3 T45) (evar G4 T45))
    | subst_evar_there_etvar
        {d0 : (Trace tm)} {G3 : Env}
        {G4 : Env} :
        (subst_evar G2 T44 s6 d0 G3 G4) -> (subst_evar G2 T44 s6 (XS ty d0) (etvar G3) (etvar G4)).
  Lemma weaken_subst_evar {G2 : Env} (T44 : Ty) {s6 : Tm} :
    (forall (G3 : Env) {d0 : (Trace tm)} {G4 : Env} {G5 : Env} ,
      (subst_evar G2 T44 s6 d0 G4 G5) -> (subst_evar G2 T44 s6 (weakenTrace d0 (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 G3))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G2 : Env) (S6 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G2 S6 X0 (etvar G2) G2)
    | subst_etvar_there_evar
        {d0 : (Trace ty)} {G3 : Env}
        {G4 : Env} (T44 : Ty) :
        (subst_etvar G2 S6 d0 G3 G4) -> (subst_etvar G2 S6 (XS tm d0) (evar G3 T44) (evar G4 (tsubstTy d0 S6 T44)))
    | subst_etvar_there_etvar
        {d0 : (Trace ty)} {G3 : Env}
        {G4 : Env} :
        (subst_etvar G2 S6 d0 G3 G4) -> (subst_etvar G2 S6 (XS ty d0) (etvar G3) (etvar G4)).
  Lemma weaken_subst_etvar {G2 : Env} {S6 : Ty} :
    (forall (G3 : Env) {d0 : (Trace ty)} {G4 : Env} {G5 : Env} ,
      (subst_etvar G2 S6 d0 G4 G5) -> (subst_etvar G2 S6 (weakenTrace d0 (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 (tsubstEnv d0 S6 G3)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G2 : Env} {s6 : Tm} (T44 : Ty) :
    (forall {d0 : (Trace tm)} {G3 : Env} {G4 : Env} ,
      (subst_evar G2 T44 s6 d0 G3 G4) -> (substhvl_tm (domainEnv G2) d0 (domainEnv G3) (domainEnv G4))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G2 : Env} {S6 : Ty} :
    (forall {d0 : (Trace ty)} {G3 : Env} {G4 : Env} ,
      (subst_etvar G2 S6 d0 G3 G4) -> (substhvl_ty (domainEnv G2) d0 (domainEnv G3) (domainEnv G4))).
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
  (forall {G2 : Env} (G3 : Env) {T44 : Ty} (wf : (wfTy (domainEnv G2) T44)) ,
    (lookup_evar (appendEnv (evar G2 T44) G3) (weakenIndextm I0 (domainEnv G3)) (weakenTy T44 (domainEnv G3)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G2 : Env} (G3 : Env) ,
    (lookup_etvar (appendEnv (etvar G2) G3) (weakenIndexty I0 (domainEnv G3)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H40 : (wfTy _ (tvar _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTy _ (tarr _ _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTy _ (tall _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTy _ (tprod _ _)) |- _ => inversion H40; subst; clear H40
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H40 : (wfPat _ (pvar _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfPat _ (pprod _ _)) |- _ => inversion H40; subst; clear H40
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H40 : (wfTm _ (var _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTm _ (abs _ _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTm _ (app _ _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTm _ (tabs _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTm _ (tapp _ _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTm _ (prod _ _)) |- _ => inversion H40; subst; clear H40
  | H40 : (wfTm _ (lett _ _ _)) |- _ => inversion H40; subst; clear H40
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
  (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} (ins : (shift_evar c0 G2 G3)) {x13 : (Index tm)} {T44 : Ty} ,
    (lookup_evar G2 x13 T44) -> (lookup_evar G3 (shiftIndex c0 x13) T44)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} (ins : (shift_evar c0 G2 G3)) {X12 : (Index ty)} ,
    (lookup_etvar G2 X12) -> (lookup_etvar G3 X12)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} (ins : (shift_etvar c0 G2 G3)) {x13 : (Index tm)} {T44 : Ty} ,
    (lookup_evar G2 x13 T44) -> (lookup_evar G3 x13 (tshiftTy c0 T44))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} (ins : (shift_etvar c0 G2 G3)) {X12 : (Index ty)} ,
    (lookup_etvar G2 X12) -> (lookup_etvar G3 (tshiftIndex c0 X12))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G2 : Env} (T45 : Ty) {s6 : Tm} :
  (forall {d0 : (Trace tm)} {G3 : Env} {G4 : Env} (sub : (subst_evar G2 T45 s6 d0 G3 G4)) {X12 : (Index ty)} ,
    (lookup_etvar G3 X12) -> (lookup_etvar G4 X12)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G2 : Env} {S6 : Ty} (wf : (wfTy (domainEnv G2) S6)) :
  (forall {d0 : (Trace ty)} {G3 : Env} {G4 : Env} (sub : (subst_etvar G2 S6 d0 G3 G4)) {x13 : (Index tm)} (T45 : Ty) ,
    (lookup_evar G3 x13 T45) -> (lookup_evar G4 x13 (tsubstTy d0 S6 T45))).
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
    | (tarr T43 T44) => (plus 1 (plus (size_Ty T43) (size_Ty T44)))
    | (tall T45) => (plus 1 (size_Ty T45))
    | (tprod T46 T47) => (plus 1 (plus (size_Ty T46) (size_Ty T47)))
  end.
Fixpoint size_Pat (p18 : Pat) {struct p18} :
nat :=
  match p18 with
    | (pvar T43) => (plus 1 (size_Ty T43))
    | (pprod p19 p20) => (plus 1 (plus (size_Pat p19) (size_Pat p20)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x13) => 1
    | (abs T43 t27) => (plus 1 (plus (size_Ty T43) (size_Tm t27)))
    | (app t28 t29) => (plus 1 (plus (size_Tm t28) (size_Tm t29)))
    | (tabs t30) => (plus 1 (size_Tm t30))
    | (tapp t31 T44) => (plus 1 (plus (size_Tm t31) (size_Ty T44)))
    | (prod t32 t33) => (plus 1 (plus (size_Tm t32) (size_Tm t33)))
    | (lett p18 t34 t35) => (plus 1 (plus (size_Pat p18) (plus (size_Tm t34) (size_Tm t35))))
  end.
Fixpoint tshift_size_Ty (S1 : Ty) (c0 : (Cutoff ty)) {struct S1} :
((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) with
    | (tvar _) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
    | (tall T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c0)))
    | (tprod T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
  end.
Fixpoint tshift_size_Pat (p20 : Pat) (c0 : (Cutoff ty)) {struct p20} :
((size_Pat (tshiftPat c0 p20)) = (size_Pat p20)) :=
  match p20 return ((size_Pat (tshiftPat c0 p20)) = (size_Pat p20)) with
    | (pvar T) => (f_equal2 plus eq_refl (tshift_size_Ty T c0))
    | (pprod p1 p2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p1 c0) (tshift_size_Pat p2 (weakenCutoffty c0 (appendHvl H0 (bindPat p1))))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c0 : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c0 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c0))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (tabs t) => (f_equal2 plus eq_refl (shift_size_Tm t c0))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c0) eq_refl))
    | (prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (lett p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 (weakenCutofftm c0 (appendHvl H0 (bindPat p)))))))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c0 : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c0 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c0) (tshift_size_Tm t c0)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (tabs t) => (f_equal2 plus eq_refl (tshift_size_Tm t (CS c0)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c0) (tshift_size_Ty T c0)))
    | (prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (lett p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p c0) (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 (weakenCutoffty c0 (appendHvl H0 (bindPat p)))))))
  end.
 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Pat  :
  (forall (k : Hvl) (p20 : Pat) ,
    ((size_Pat (weakenPat p20 k)) = (size_Pat p20))).
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
  (forall (k : Hvl) (S1 : Ty) ,
    ((size_Ty (weakenTy S1 k)) = (size_Ty S1))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive PTyping (G2 : Env) : Pat -> Ty -> Env -> Prop :=
  | P_Var (T : Ty)
      (H26 : (wfTy (domainEnv G2) T))
      :
      (PTyping G2 (pvar T) T (evar empty T))
  | P_Prod (T1 : Ty) (T2 : Ty)
      (p1 : Pat) (p2 : Pat) (G : Env)
      (G0 : Env)
      (wtp1 : (PTyping G2 p1 T1 G))
      (wtp2 : (PTyping (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0))
      (H28 : (wfTy (domainEnv G2) T2))
      :
      (PTyping G2 (pprod p1 p2) (tprod T1 T2) (appendEnv (appendEnv empty G) G0)).
Inductive Typing (G2 : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index tm))
      (lk : (lookup_evar G2 x T))
      (H26 : (wfTy (domainEnv G2) T))
      (H27 : (wfindex (domainEnv G2) x))
      : (Typing G2 (var x) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G2 T1) t (weakenTy T2 (HS tm H0))))
      (H28 : (wfTy (domainEnv G2) T1))
      (H29 : (wfTy (domainEnv G2) T2))
      :
      (Typing G2 (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm0 : (Typing G2 t1 (tarr T11 T12)))
      (jm1 : (Typing G2 t2 T11)) :
      (Typing G2 (app t1 t2) T12)
  | T_Tabs (T : Ty) (t : Tm)
      (jm2 : (Typing (etvar G2) t T))
      : (Typing G2 (tabs t) (tall T))
  | T_Tapp (T12 : Ty) (T2 : Ty)
      (t1 : Tm)
      (jm3 : (Typing G2 t1 (tall T12)))
      (H38 : (wfTy (domainEnv G2) T2))
      :
      (Typing G2 (tapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Prod (T1 : Ty) (T2 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm4 : (Typing G2 t1 T1))
      (jm5 : (Typing G2 t2 T2)) :
      (Typing G2 (prod t1 t2) (tprod T1 T2))
  | T_Let (T1 : Ty) (T2 : Ty)
      (p : Pat) (t1 : Tm) (t2 : Tm)
      (G1 : Env)
      (jm6 : (Typing G2 t1 T1))
      (wtp : (PTyping G2 p T1 G1))
      (jm7 : (Typing (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p)))))
      (H45 : (wfTy (domainEnv G2) T2))
      : (Typing G2 (lett p t1 t2) T2).
Fixpoint domain_PTyping_bindPat (G4 : Env) (p25 : Pat) (T49 : Ty) (G5 : Env) (wtp8 : (PTyping G4 p25 T49 G5)) :
((domainEnv G5) = (bindPat p25)) :=
  match wtp8 in (PTyping _ p25 T49 G5) return ((domainEnv G5) = (bindPat p25)) with
    | (P_Var T46 H42) => (eq_refl (HS tm H0))
    | (P_Prod T47 T48 p23 p24 G2 G3 wtp6 wtp7 H44) => (eq_trans (domainEnv_appendEnv (appendEnv empty G2) G3) (f_equal2 appendHvl (eq_trans (domainEnv_appendEnv empty G2) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G4 p23 T47 G2 wtp6))) (domain_PTyping_bindPat (appendEnv G4 (appendEnv empty G2)) p24 (weakenTy T48 (appendHvl H0 (bindPat p23))) G3 wtp7)))
  end.
Lemma PTyping_cast  :
  (forall (G2 : Env) (p23 : Pat) (T46 : Ty) (G4 : Env) (G3 : Env) (p24 : Pat) (T47 : Ty) (G5 : Env) ,
    (G2 = G3) -> (p23 = p24) -> (T46 = T47) -> (G4 = G5) -> (PTyping G2 p23 T46 G4) -> (PTyping G3 p24 T47 G5)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G2 : Env) (t27 : Tm) (T46 : Ty) (G3 : Env) (t28 : Tm) (T47 : Ty) ,
    (G2 = G3) -> (t27 = t28) -> (T46 = T47) -> (Typing G2 t27 T46) -> (Typing G3 t28 T47)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_PTyping (G9 : Env) (p26 : Pat) (T53 : Ty) (G10 : Env) (wtp9 : (PTyping G9 p26 T53 G10)) :
(forall (c0 : (Cutoff tm)) (G11 : Env) (H55 : (shift_evar c0 G9 G11)) ,
  (PTyping G11 p26 T53 G10)) :=
  match wtp9 in (PTyping _ p26 T53 G10) return (forall (c0 : (Cutoff tm)) (G11 : Env) (H55 : (shift_evar c0 G9 G11)) ,
    (PTyping G11 p26 T53 G10)) with
    | (P_Var T50 H48) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H55 : (shift_evar c0 G9 G11)) =>
      (P_Var G11 T50 (shift_wfTy _ _ H48 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H55)))))
    | (P_Prod T51 T52 p24 p25 G7 G8 wtp7 wtp8 H50) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H55 : (shift_evar c0 G9 G11)) =>
      (PTyping_cast G11 _ _ _ G11 (pprod p24 p25) (tprod T51 T52) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G11 T51 T52 p24 p25 G7 G8 (shift_evar_PTyping G9 p24 T51 G7 wtp7 c0 G11 (weaken_shift_evar empty H55)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (shift_evar_PTyping (appendEnv G9 (appendEnv empty G7)) p25 (weakenTy T52 (appendHvl H0 (bindPat p24))) G8 wtp8 (weakenCutofftm c0 (domainEnv (appendEnv empty G7))) (appendEnv G11 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H55))) (shift_wfTy _ _ H50 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H55))))))
  end.
Fixpoint shift_etvar_PTyping (G9 : Env) (p26 : Pat) (T53 : Ty) (G10 : Env) (wtp9 : (PTyping G9 p26 T53 G10)) :
(forall (c0 : (Cutoff ty)) (G11 : Env) (H55 : (shift_etvar c0 G9 G11)) ,
  (PTyping G11 (tshiftPat c0 p26) (tshiftTy c0 T53) (tshiftEnv c0 G10))) :=
  match wtp9 in (PTyping _ p26 T53 G10) return (forall (c0 : (Cutoff ty)) (G11 : Env) (H55 : (shift_etvar c0 G9 G11)) ,
    (PTyping G11 (tshiftPat c0 p26) (tshiftTy c0 T53) (tshiftEnv c0 G10))) with
    | (P_Var T50 H48) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H55 : (shift_etvar c0 G9 G11)) =>
      (P_Var G11 (tshiftTy c0 T50) (tshift_wfTy _ _ H48 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H55)))))
    | (P_Prod T51 T52 p24 p25 G7 G8 wtp7 wtp8 H50) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H55 : (shift_etvar c0 G9 G11)) =>
      (PTyping_cast G11 _ _ _ G11 (tshiftPat c0 (pprod p24 p25)) (tshiftTy c0 (tprod T51 T52)) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym (tshiftEnv_appendEnv c0 empty G7)) eq_refl) (eq_sym (tshiftEnv_appendEnv c0 (appendEnv empty G7) G8))) (P_Prod G11 (tshiftTy c0 T51) (tshiftTy c0 T52) (tshiftPat c0 p24) (tshiftPat (weakenCutoffty c0 (appendHvl H0 (bindPat p24))) p25) (tshiftEnv c0 G7) (tshiftEnv (weakenCutoffty c0 (domainEnv (appendEnv empty G7))) G8) (shift_etvar_PTyping G9 p24 T51 G7 wtp7 c0 G11 (weaken_shift_etvar empty H55)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tshiftEnv_appendEnv c0 empty G7)) (f_equal2 tshiftPat (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G9 p24 T51 G7 wtp7)))) eq_refl) (eq_trans (f_equal2 tshiftTy (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G9 p24 T51 G7 wtp7)))) eq_refl) (eq_trans (eq_sym (weakenTy_tshiftTy (appendHvl H0 (bindPat p24)) c0 T52)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))))) eq_refl (shift_etvar_PTyping (appendEnv G9 (appendEnv empty G7)) p25 (weakenTy T52 (appendHvl H0 (bindPat p24))) G8 wtp8 (weakenCutoffty c0 (domainEnv (appendEnv empty G7))) (appendEnv G11 (tshiftEnv c0 (appendEnv empty G7))) (weaken_shift_etvar (appendEnv empty G7) H55))) (tshift_wfTy _ _ H50 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H55))))))
  end.
Fixpoint shift_evar_Typing (G8 : Env) (t31 : Tm) (T55 : Ty) (jm18 : (Typing G8 t31 T55)) :
(forall (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) ,
  (Typing G9 (shiftTm c0 t31) T55)) :=
  match jm18 in (Typing _ t31 T55) return (forall (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) ,
    (Typing G9 (shiftTm c0 t31) T55)) with
    | (T_Var T50 x15 lk0 H48 H49) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) =>
      (T_Var G9 T50 (shiftIndex c0 x15) (shift_evar_lookup_evar H73 lk0) (shift_wfTy _ _ H48 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H73))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H73)) _ H49)))
    | (T_Abs T51 T54 t28 jm9 H50 H51) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) =>
      (T_Abs G9 T51 T54 (shiftTm (CS c0) t28) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G8 T51) t28 (weakenTy T54 (HS tm H0)) jm9 (CS c0) (evar G9 T51) (weaken_shift_evar (evar empty T51) H73))) (shift_wfTy _ _ H50 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H73))) (shift_wfTy _ _ H51 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H73)))))
    | (T_App T52 T53 t29 t30 jm10 jm11) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) =>
      (T_App G9 T52 T53 (shiftTm c0 t29) (shiftTm c0 t30) (shift_evar_Typing G8 t29 (tarr T52 T53) jm10 c0 G9 (weaken_shift_evar empty H73)) (shift_evar_Typing G8 t30 T52 jm11 c0 G9 (weaken_shift_evar empty H73))))
    | (T_Tabs T50 t28 jm12) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) =>
      (T_Tabs G9 T50 (shiftTm c0 t28) (shift_evar_Typing (etvar G8) t28 T50 jm12 c0 (etvar G9) (weaken_shift_evar (etvar empty) H73))))
    | (T_Tapp T53 T54 t29 jm13 H60) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) =>
      (T_Tapp G9 T53 T54 (shiftTm c0 t29) (shift_evar_Typing G8 t29 (tall T53) jm13 c0 G9 (weaken_shift_evar empty H73)) (shift_wfTy _ _ H60 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H73)))))
    | (T_Prod T51 T54 t29 t30 jm14 jm15) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) =>
      (T_Prod G9 T51 T54 (shiftTm c0 t29) (shiftTm c0 t30) (shift_evar_Typing G8 t29 T51 jm14 c0 G9 (weaken_shift_evar empty H73)) (shift_evar_Typing G8 t30 T54 jm15 c0 G9 (weaken_shift_evar empty H73))))
    | (T_Let T51 T54 p24 t29 t30 G7 jm16 wtp7 jm17 H67) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H73 : (shift_evar c0 G8 G9)) =>
      (T_Let G9 T51 T54 p24 (shiftTm c0 t29) (shiftTm (weakenCutofftm c0 (appendHvl H0 (bindPat p24))) t30) G7 (shift_evar_Typing G8 t29 T51 jm16 c0 G9 (weaken_shift_evar empty H73)) (shift_evar_PTyping G8 p24 T51 G7 wtp7 c0 G9 (weaken_shift_evar empty H73)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal2 shiftTm (f_equal2 weakenCutofftm eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G8 p24 T51 G7 wtp7)))) eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (shift_evar_Typing (appendEnv G8 (appendEnv empty G7)) t30 (weakenTy T54 (appendHvl H0 (bindPat p24))) jm17 (weakenCutofftm c0 (domainEnv (appendEnv empty G7))) (appendEnv G9 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H73))) (shift_wfTy _ _ H67 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H73)))))
  end.
Fixpoint shift_etvar_Typing (G8 : Env) (t31 : Tm) (T55 : Ty) (jm18 : (Typing G8 t31 T55)) :
(forall (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) ,
  (Typing G9 (tshiftTm c0 t31) (tshiftTy c0 T55))) :=
  match jm18 in (Typing _ t31 T55) return (forall (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) ,
    (Typing G9 (tshiftTm c0 t31) (tshiftTy c0 T55))) with
    | (T_Var T50 x15 lk0 H48 H49) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) =>
      (T_Var G9 (tshiftTy c0 T50) x15 (shift_etvar_lookup_evar H73 lk0) (tshift_wfTy _ _ H48 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H73))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H73)) _ H49)))
    | (T_Abs T51 T54 t28 jm9 H50 H51) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) =>
      (T_Abs G9 (tshiftTy c0 T51) (tshiftTy c0 T54) (tshiftTm c0 t28) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c0 T54)) (shift_etvar_Typing (evar G8 T51) t28 (weakenTy T54 (HS tm H0)) jm9 c0 (evar G9 (tshiftTy c0 T51)) (weaken_shift_etvar (evar empty T51) H73))) (tshift_wfTy _ _ H50 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H73))) (tshift_wfTy _ _ H51 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H73)))))
    | (T_App T52 T53 t29 t30 jm10 jm11) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) =>
      (T_App G9 (tshiftTy c0 T52) (tshiftTy c0 T53) (tshiftTm c0 t29) (tshiftTm c0 t30) (shift_etvar_Typing G8 t29 (tarr T52 T53) jm10 c0 G9 (weaken_shift_etvar empty H73)) (shift_etvar_Typing G8 t30 T52 jm11 c0 G9 (weaken_shift_etvar empty H73))))
    | (T_Tabs T50 t28 jm12) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) =>
      (T_Tabs G9 (tshiftTy (CS c0) T50) (tshiftTm (CS c0) t28) (shift_etvar_Typing (etvar G8) t28 T50 jm12 (CS c0) (etvar G9) (weaken_shift_etvar (etvar empty) H73))))
    | (T_Tapp T53 T54 t29 jm13 H60) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) =>
      (Typing_cast G9 _ _ G9 (tshiftTm c0 (tapp t29 T54)) (tshiftTy c0 (tsubstTy X0 T54 T53)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T53 c0 T54)) (T_Tapp G9 (tshiftTy (CS c0) T53) (tshiftTy c0 T54) (tshiftTm c0 t29) (shift_etvar_Typing G8 t29 (tall T53) jm13 c0 G9 (weaken_shift_etvar empty H73)) (tshift_wfTy _ _ H60 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H73))))))
    | (T_Prod T51 T54 t29 t30 jm14 jm15) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) =>
      (T_Prod G9 (tshiftTy c0 T51) (tshiftTy c0 T54) (tshiftTm c0 t29) (tshiftTm c0 t30) (shift_etvar_Typing G8 t29 T51 jm14 c0 G9 (weaken_shift_etvar empty H73)) (shift_etvar_Typing G8 t30 T54 jm15 c0 G9 (weaken_shift_etvar empty H73))))
    | (T_Let T51 T54 p24 t29 t30 G7 jm16 wtp7 jm17 H67) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H73 : (shift_etvar c0 G8 G9)) =>
      (T_Let G9 (tshiftTy c0 T51) (tshiftTy c0 T54) (tshiftPat c0 p24) (tshiftTm c0 t29) (tshiftTm (weakenCutoffty c0 (appendHvl H0 (bindPat p24))) t30) (tshiftEnv c0 G7) (shift_etvar_Typing G8 t29 T51 jm16 c0 G9 (weaken_shift_etvar empty H73)) (shift_etvar_PTyping G8 p24 T51 G7 wtp7 c0 G9 (weaken_shift_etvar empty H73)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tshiftEnv_appendEnv c0 empty G7)) (f_equal2 tshiftTm (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G8 p24 T51 G7 wtp7)))) eq_refl) (eq_trans (f_equal2 tshiftTy (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G8 p24 T51 G7 wtp7)))) eq_refl) (eq_trans (eq_sym (weakenTy_tshiftTy (appendHvl H0 (bindPat p24)) c0 T54)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))))) (shift_etvar_Typing (appendEnv G8 (appendEnv empty G7)) t30 (weakenTy T54 (appendHvl H0 (bindPat p24))) jm17 (weakenCutoffty c0 (domainEnv (appendEnv empty G7))) (appendEnv G9 (tshiftEnv c0 (appendEnv empty G7))) (weaken_shift_etvar (appendEnv empty G7) H73))) (tshift_wfTy _ _ H67 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H73)))))
  end.
 Hint Resolve shift_evar_PTyping shift_etvar_PTyping shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_PTyping shift_etvar_PTyping shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_PTyping (G2 : Env) :
(forall (G3 : Env) (p23 : Pat) (T46 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T46 G4)) ,
  (PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T46 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) :=
  match G2 return (forall (G3 : Env) (p23 : Pat) (T46 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T46 G4)) ,
    (PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T46 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) with
    | (empty) => (fun (G3 : Env) (p23 : Pat) (T46 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T46 G4)) =>
      wtp6)
    | (evar G2 T47) => (fun (G3 : Env) (p23 : Pat) (T46 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T46 G4)) =>
      (shift_evar_PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T46 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)) (weaken_PTyping G2 G3 p23 T46 G4 wtp6) C0 (evar (appendEnv G3 G2) T47) shift_evar_here))
    | (etvar G2) => (fun (G3 : Env) (p23 : Pat) (T46 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T46 G4)) =>
      (shift_etvar_PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T46 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)) (weaken_PTyping G2 G3 p23 T46 G4 wtp6) C0 (etvar (appendEnv G3 G2)) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G5 : Env) :
(forall (G6 : Env) (t27 : Tm) (T48 : Ty) (jm8 : (Typing G6 t27 T48)) ,
  (Typing (appendEnv G6 G5) (weakenTm t27 (domainEnv G5)) (weakenTy T48 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (t27 : Tm) (T48 : Ty) (jm8 : (Typing G6 t27 T48)) ,
    (Typing (appendEnv G6 G5) (weakenTm t27 (domainEnv G5)) (weakenTy T48 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (t27 : Tm) (T48 : Ty) (jm8 : (Typing G6 t27 T48)) =>
      jm8)
    | (evar G5 T49) => (fun (G6 : Env) (t27 : Tm) (T48 : Ty) (jm8 : (Typing G6 t27 T48)) =>
      (shift_evar_Typing (appendEnv G6 G5) (weakenTm t27 (domainEnv G5)) (weakenTy T48 (domainEnv G5)) (weaken_Typing G5 G6 t27 T48 jm8) C0 (evar (appendEnv G6 G5) T49) shift_evar_here))
    | (etvar G5) => (fun (G6 : Env) (t27 : Tm) (T48 : Ty) (jm8 : (Typing G6 t27 T48)) =>
      (shift_etvar_Typing (appendEnv G6 G5) (weakenTm t27 (domainEnv G5)) (weakenTy T48 (domainEnv G5)) (weaken_Typing G5 G6 t27 T48 jm8) C0 (etvar (appendEnv G6 G5)) shift_etvar_here))
  end.
Fixpoint PTyping_wf_0 (G2 : Env) (p24 : Pat) (T50 : Ty) (G7 : Env) (wtp7 : (PTyping G2 p24 T50 G7)) {struct wtp7} :
(wfPat (domainEnv G2) p24) :=
  match wtp7 in (PTyping _ p24 T50 G7) return (wfPat (domainEnv G2) p24) with
    | (P_Var T H26) => (wfPat_pvar (domainEnv G2) H26)
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H28) => (wfPat_pprod (domainEnv G2) (PTyping_wf_0 G2 p1 T1 G wtp1) (wfPat_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p1 T1 G wtp1))))) eq_refl (PTyping_wf_0 (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0 wtp2)))
  end
with PTyping_wf_1 (G2 : Env) (p24 : Pat) (T50 : Ty) (G8 : Env) (wtp8 : (PTyping G2 p24 T50 G8)) {struct wtp8} :
(wfTy (domainEnv G2) T50) :=
  match wtp8 in (PTyping _ p24 T50 G8) return (wfTy (domainEnv G2) T50) with
    | (P_Var T H26) => H26
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H28) => (wfTy_tprod (domainEnv G2) (PTyping_wf_1 G2 p1 T1 G wtp1) H28)
  end.
Fixpoint Typing_wf_0 (G2 : Env) (t28 : Tm) (T51 : Ty) (jm9 : (Typing G2 t28 T51)) {struct jm9} :
(wfTm (domainEnv G2) t28) :=
  match jm9 in (Typing _ t28 T51) return (wfTm (domainEnv G2) t28) with
    | (T_Var T x lk0 H26 H27) => (wfTm_var (domainEnv G2) _ H27)
    | (T_Abs T1 T2 t jm H28 H29) => (wfTm_abs (domainEnv G2) H28 (Typing_wf_0 (evar G2 T1) t (weakenTy T2 (HS tm H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_app (domainEnv G2) (Typing_wf_0 G2 t1 (tarr T11 T12) jm0) (Typing_wf_0 G2 t2 T11 jm1))
    | (T_Tabs T t jm2) => (wfTm_tabs (domainEnv G2) (Typing_wf_0 (etvar G2) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H38) => (wfTm_tapp (domainEnv G2) (Typing_wf_0 G2 t1 (tall T12) jm3) H38)
    | (T_Prod T1 T2 t1 t2 jm4 jm5) => (wfTm_prod (domainEnv G2) (Typing_wf_0 G2 t1 T1 jm4) (Typing_wf_0 G2 t2 T2 jm5))
    | (T_Let T1 T2 p t1 t2 G1 jm6 wtp jm7 H45) => (wfTm_lett (domainEnv G2) (PTyping_wf_0 G2 p T1 G1 wtp) (Typing_wf_0 G2 t1 T1 jm6) (wfTm_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G1)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G1) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p T1 G1 wtp))))) eq_refl (Typing_wf_0 (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p))) jm7)))
  end
with Typing_wf_1 (G2 : Env) (t28 : Tm) (T51 : Ty) (jm10 : (Typing G2 t28 T51)) {struct jm10} :
(wfTy (domainEnv G2) T51) :=
  match jm10 in (Typing _ t28 T51) return (wfTy (domainEnv G2) T51) with
    | (T_Var T x lk1 H26 H27) => H26
    | (T_Abs T1 T2 t jm H28 H29) => (wfTy_tarr (domainEnv G2) H28 H29)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_tarr_1 (domainEnv G2) T11 T12 (Typing_wf_1 G2 t1 (tarr T11 T12) jm0))
    | (T_Tabs T t jm2) => (wfTy_tall (domainEnv G2) (Typing_wf_1 (etvar G2) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H38) => (substhvl_ty_wfTy H38 (HS ty (domainEnv G2)) T12 (inversion_wfTy_tall_1 (domainEnv G2) T12 (Typing_wf_1 G2 t1 (tall T12) jm3)) (substhvl_ty_here (domainEnv G2)))
    | (T_Prod T1 T2 t1 t2 jm4 jm5) => (wfTy_tprod (domainEnv G2) (Typing_wf_1 G2 t1 T1 jm4) (Typing_wf_1 G2 t2 T2 jm5))
    | (T_Let T1 T2 p t1 t2 G1 jm6 wtp jm7 H45) => H45
  end.
 Hint Extern 8 => match goal with
  | H52 : (PTyping _ _ _ _) |- _ => pose proof ((PTyping_wf_0 _ _ _ _ H52)); pose proof ((PTyping_wf_1 _ _ _ _ H52)); clear H52
end : wf.
 Hint Extern 8 => match goal with
  | H53 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H53)); pose proof ((Typing_wf_1 _ _ _ H53)); clear H53
end : wf.
Lemma subst_evar_lookup_evar (G9 : Env) (s6 : Tm) (T52 : Ty) (jm11 : (Typing G9 s6 T52)) :
  (forall (d0 : (Trace tm)) (G10 : Env) (G12 : Env) (sub : (subst_evar G9 T52 s6 d0 G10 G12)) (x15 : (Index tm)) (T53 : Ty) ,
    (lookup_evar G10 x15 T53) -> (Typing G12 (substIndex d0 s6 x15) T53)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Fixpoint subst_evar_PTyping (G12 : Env) (s6 : Tm) (T52 : Ty) (jm11 : (Typing G12 s6 T52)) (G11 : Env) (p : Pat) (T : Ty) (G13 : Env) (wtp11 : (PTyping G11 p T G13)) :
(forall (G14 : Env) (d0 : (Trace tm)) (H60 : (subst_evar G12 T52 s6 d0 G11 G14)) ,
  (PTyping G14 p T G13)) :=
  match wtp11 in (PTyping _ p T G13) return (forall (G14 : Env) (d0 : (Trace tm)) (H60 : (subst_evar G12 T52 s6 d0 G11 G14)) ,
    (PTyping G14 p T G13)) with
    | (P_Var T53 H55) => (fun (G14 : Env) (d0 : (Trace tm)) (H60 : (subst_evar G12 T52 s6 d0 G11 G14)) =>
      (P_Var G14 T53 (substhvl_tm_wfTy _ _ H55 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H60)))))
    | (P_Prod T54 T55 p25 p26 G9 G10 wtp9 wtp10 H57) => (fun (G14 : Env) (d0 : (Trace tm)) (H60 : (subst_evar G12 T52 s6 d0 G11 G14)) =>
      (PTyping_cast G14 _ _ _ G14 (pprod p25 p26) (tprod T54 T55) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G14 T54 T55 p25 p26 G9 G10 (subst_evar_PTyping G12 s6 T52 jm11 G11 p25 T54 G9 wtp9 G14 d0 (weaken_subst_evar _ empty H60)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (subst_evar_PTyping G12 s6 T52 jm11 (appendEnv G11 (appendEnv empty G9)) p26 (weakenTy T55 (appendHvl H0 (bindPat p25))) G10 wtp10 (appendEnv G14 (appendEnv empty G9)) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_evar _ (appendEnv empty G9) H60))) (substhvl_tm_wfTy _ _ H57 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H60))))))
  end.
Fixpoint subst_etvar_PTyping (G12 : Env) (S6 : Ty) (H60 : (wfTy (domainEnv G12) S6)) (G11 : Env) (p : Pat) (T : Ty) (G13 : Env) (wtp11 : (PTyping G11 p T G13)) :
(forall (G14 : Env) (d0 : (Trace ty)) (H61 : (subst_etvar G12 S6 d0 G11 G14)) ,
  (PTyping G14 (tsubstPat d0 S6 p) (tsubstTy d0 S6 T) (tsubstEnv d0 S6 G13))) :=
  match wtp11 in (PTyping _ p T G13) return (forall (G14 : Env) (d0 : (Trace ty)) (H61 : (subst_etvar G12 S6 d0 G11 G14)) ,
    (PTyping G14 (tsubstPat d0 S6 p) (tsubstTy d0 S6 T) (tsubstEnv d0 S6 G13))) with
    | (P_Var T53 H55) => (fun (G14 : Env) (d0 : (Trace ty)) (H61 : (subst_etvar G12 S6 d0 G11 G14)) =>
      (P_Var G14 (tsubstTy (weakenTrace d0 H0) S6 T53) (substhvl_ty_wfTy H60 _ _ H55 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61)))))
    | (P_Prod T54 T55 p25 p26 G9 G10 wtp9 wtp10 H57) => (fun (G14 : Env) (d0 : (Trace ty)) (H61 : (subst_etvar G12 S6 d0 G11 G14)) =>
      (PTyping_cast G14 _ _ _ G14 (tsubstPat d0 S6 (pprod p25 p26)) (tsubstTy d0 S6 (tprod T54 T55)) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym (tsubstEnv_appendEnv d0 S6 empty G9)) eq_refl) (eq_sym (tsubstEnv_appendEnv d0 S6 (appendEnv empty G9) G10))) (P_Prod G14 (tsubstTy (weakenTrace d0 H0) S6 T54) (tsubstTy (weakenTrace d0 H0) S6 T55) (tsubstPat (weakenTrace d0 H0) S6 p25) (tsubstPat (weakenTrace d0 (appendHvl H0 (bindPat p25))) S6 p26) (tsubstEnv (weakenTrace d0 H0) S6 G9) (tsubstEnv (weakenTrace d0 (domainEnv (appendEnv empty G9))) S6 G10) (subst_etvar_PTyping G12 S6 H60 G11 p25 T54 G9 wtp9 G14 d0 (weaken_subst_etvar empty H61)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tsubstEnv_appendEnv d0 S6 empty G9)) (f_equal3 tsubstPat (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G11 p25 T54 G9 wtp9)))) eq_refl eq_refl) (eq_trans (f_equal3 tsubstTy (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G11 p25 T54 G9 wtp9)))) eq_refl eq_refl) (eq_trans (eq_sym (weakenTy_tsubstTy (appendHvl H0 (bindPat p25)) d0 S6 T55)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))))) eq_refl (subst_etvar_PTyping G12 S6 H60 (appendEnv G11 (appendEnv empty G9)) p26 (weakenTy T55 (appendHvl H0 (bindPat p25))) G10 wtp10 (appendEnv G14 (tsubstEnv d0 S6 (appendEnv empty G9))) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_etvar (appendEnv empty G9) H61))) (substhvl_ty_wfTy H60 _ _ H57 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61))))))
  end.
Fixpoint subst_evar_Typing (G11 : Env) (s6 : Tm) (T53 : Ty) (jm20 : (Typing G11 s6 T53)) (G10 : Env) (t : Tm) (T : Ty) (jm21 : (Typing G10 t T)) :
(forall (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) ,
  (Typing G12 (substTm d0 s6 t) T)) :=
  match jm21 in (Typing _ t T) return (forall (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) ,
    (Typing G12 (substTm d0 s6 t) T)) with
    | (T_Var T54 x15 lk2 H56 H57) => (fun (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) =>
      (subst_evar_lookup_evar G11 s6 T53 jm20 d0 G10 G12 H79 x15 T54 lk2))
    | (T_Abs T55 T58 t29 jm11 H58 H59) => (fun (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) =>
      (T_Abs G12 T55 T58 (substTm (weakenTrace d0 (HS tm H0)) s6 t29) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G11 s6 T53 jm20 (evar G10 T55) t29 (weakenTy T58 (HS tm H0)) jm11 (appendEnv G12 (evar empty T55)) (weakenTrace d0 (HS tm H0)) (weaken_subst_evar _ (evar empty T55) H79))) (substhvl_tm_wfTy _ _ H58 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H79))) (substhvl_tm_wfTy _ _ H59 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H79)))))
    | (T_App T56 T57 t30 t31 jm12 jm13) => (fun (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) =>
      (T_App G12 T56 T57 (substTm (weakenTrace d0 H0) s6 t30) (substTm (weakenTrace d0 H0) s6 t31) (subst_evar_Typing G11 s6 T53 jm20 G10 t30 (tarr T56 T57) jm12 G12 d0 (weaken_subst_evar _ empty H79)) (subst_evar_Typing G11 s6 T53 jm20 G10 t31 T56 jm13 G12 d0 (weaken_subst_evar _ empty H79))))
    | (T_Tabs T54 t29 jm14) => (fun (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) =>
      (T_Tabs G12 T54 (substTm (weakenTrace d0 (HS ty H0)) s6 t29) (subst_evar_Typing G11 s6 T53 jm20 (etvar G10) t29 T54 jm14 (appendEnv G12 (etvar empty)) (weakenTrace d0 (HS ty H0)) (weaken_subst_evar _ (etvar empty) H79))))
    | (T_Tapp T57 T58 t30 jm15 H68) => (fun (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) =>
      (T_Tapp G12 T57 T58 (substTm (weakenTrace d0 H0) s6 t30) (subst_evar_Typing G11 s6 T53 jm20 G10 t30 (tall T57) jm15 G12 d0 (weaken_subst_evar _ empty H79)) (substhvl_tm_wfTy _ _ H68 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H79)))))
    | (T_Prod T55 T58 t30 t31 jm16 jm17) => (fun (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) =>
      (T_Prod G12 T55 T58 (substTm (weakenTrace d0 H0) s6 t30) (substTm (weakenTrace d0 H0) s6 t31) (subst_evar_Typing G11 s6 T53 jm20 G10 t30 T55 jm16 G12 d0 (weaken_subst_evar _ empty H79)) (subst_evar_Typing G11 s6 T53 jm20 G10 t31 T58 jm17 G12 d0 (weaken_subst_evar _ empty H79))))
    | (T_Let T55 T58 p25 t30 t31 G9 jm18 wtp9 jm19 H75) => (fun (G12 : Env) (d0 : (Trace tm)) (H79 : (subst_evar G11 T53 s6 d0 G10 G12)) =>
      (T_Let G12 T55 T58 p25 (substTm (weakenTrace d0 H0) s6 t30) (substTm (weakenTrace d0 (appendHvl H0 (bindPat p25))) s6 t31) G9 (subst_evar_Typing G11 s6 T53 jm20 G10 t30 T55 jm18 G12 d0 (weaken_subst_evar _ empty H79)) (subst_evar_PTyping G11 s6 T53 jm20 G10 p25 T55 G9 wtp9 G12 d0 (weaken_subst_evar _ empty H79)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal3 substTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p25 T55 G9 wtp9)))) eq_refl eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (subst_evar_Typing G11 s6 T53 jm20 (appendEnv G10 (appendEnv empty G9)) t31 (weakenTy T58 (appendHvl H0 (bindPat p25))) jm19 (appendEnv G12 (appendEnv empty G9)) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_evar _ (appendEnv empty G9) H79))) (substhvl_tm_wfTy _ _ H75 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H79)))))
  end.
Fixpoint subst_etvar_Typing (G11 : Env) (S6 : Ty) (H79 : (wfTy (domainEnv G11) S6)) (G10 : Env) (t : Tm) (T : Ty) (jm20 : (Typing G10 t T)) :
(forall (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) ,
  (Typing G12 (tsubstTm d0 S6 t) (tsubstTy d0 S6 T))) :=
  match jm20 in (Typing _ t T) return (forall (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) ,
    (Typing G12 (tsubstTm d0 S6 t) (tsubstTy d0 S6 T))) with
    | (T_Var T54 x15 lk2 H56 H57) => (fun (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) =>
      (T_Var G12 (tsubstTy (weakenTrace d0 H0) S6 T54) x15 (subst_etvar_lookup_evar H79 H80 T54 lk2) (substhvl_ty_wfTy H79 _ _ H56 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H80))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H80)) H57)))
    | (T_Abs T55 T58 t29 jm11 H58 H59) => (fun (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) =>
      (T_Abs G12 (tsubstTy (weakenTrace d0 H0) S6 T55) (tsubstTy (weakenTrace d0 H0) S6 T58) (tsubstTm (weakenTrace d0 (HS tm H0)) S6 t29) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d0 S6 T58)) (subst_etvar_Typing G11 S6 H79 (evar G10 T55) t29 (weakenTy T58 (HS tm H0)) jm11 (appendEnv G12 (tsubstEnv d0 S6 (evar empty T55))) (weakenTrace d0 (HS tm H0)) (weaken_subst_etvar (evar empty T55) H80))) (substhvl_ty_wfTy H79 _ _ H58 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H80))) (substhvl_ty_wfTy H79 _ _ H59 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H80)))))
    | (T_App T56 T57 t30 t31 jm12 jm13) => (fun (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) =>
      (T_App G12 (tsubstTy (weakenTrace d0 H0) S6 T56) (tsubstTy (weakenTrace d0 H0) S6 T57) (tsubstTm (weakenTrace d0 H0) S6 t30) (tsubstTm (weakenTrace d0 H0) S6 t31) (subst_etvar_Typing G11 S6 H79 G10 t30 (tarr T56 T57) jm12 G12 d0 (weaken_subst_etvar empty H80)) (subst_etvar_Typing G11 S6 H79 G10 t31 T56 jm13 G12 d0 (weaken_subst_etvar empty H80))))
    | (T_Tabs T54 t29 jm14) => (fun (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) =>
      (T_Tabs G12 (tsubstTy (weakenTrace d0 (HS ty H0)) S6 T54) (tsubstTm (weakenTrace d0 (HS ty H0)) S6 t29) (subst_etvar_Typing G11 S6 H79 (etvar G10) t29 T54 jm14 (appendEnv G12 (tsubstEnv d0 S6 (etvar empty))) (weakenTrace d0 (HS ty H0)) (weaken_subst_etvar (etvar empty) H80))))
    | (T_Tapp T57 T58 t30 jm15 H68) => (fun (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) =>
      (Typing_cast G12 _ _ G12 (tsubstTm d0 S6 (tapp t30 T58)) (tsubstTy d0 S6 (tsubstTy X0 T58 T57)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T57 d0 S6 T58)) (T_Tapp G12 (tsubstTy (weakenTrace d0 (HS ty H0)) S6 T57) (tsubstTy (weakenTrace d0 H0) S6 T58) (tsubstTm (weakenTrace d0 H0) S6 t30) (subst_etvar_Typing G11 S6 H79 G10 t30 (tall T57) jm15 G12 d0 (weaken_subst_etvar empty H80)) (substhvl_ty_wfTy H79 _ _ H68 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H80))))))
    | (T_Prod T55 T58 t30 t31 jm16 jm17) => (fun (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) =>
      (T_Prod G12 (tsubstTy (weakenTrace d0 H0) S6 T55) (tsubstTy (weakenTrace d0 H0) S6 T58) (tsubstTm (weakenTrace d0 H0) S6 t30) (tsubstTm (weakenTrace d0 H0) S6 t31) (subst_etvar_Typing G11 S6 H79 G10 t30 T55 jm16 G12 d0 (weaken_subst_etvar empty H80)) (subst_etvar_Typing G11 S6 H79 G10 t31 T58 jm17 G12 d0 (weaken_subst_etvar empty H80))))
    | (T_Let T55 T58 p25 t30 t31 G9 jm18 wtp9 jm19 H75) => (fun (G12 : Env) (d0 : (Trace ty)) (H80 : (subst_etvar G11 S6 d0 G10 G12)) =>
      (T_Let G12 (tsubstTy (weakenTrace d0 H0) S6 T55) (tsubstTy (weakenTrace d0 H0) S6 T58) (tsubstPat (weakenTrace d0 H0) S6 p25) (tsubstTm (weakenTrace d0 H0) S6 t30) (tsubstTm (weakenTrace d0 (appendHvl H0 (bindPat p25))) S6 t31) (tsubstEnv (weakenTrace d0 H0) S6 G9) (subst_etvar_Typing G11 S6 H79 G10 t30 T55 jm18 G12 d0 (weaken_subst_etvar empty H80)) (subst_etvar_PTyping G11 S6 H79 G10 p25 T55 G9 wtp9 G12 d0 (weaken_subst_etvar empty H80)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tsubstEnv_appendEnv d0 S6 empty G9)) (f_equal3 tsubstTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p25 T55 G9 wtp9)))) eq_refl eq_refl) (eq_trans (f_equal3 tsubstTy (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p25 T55 G9 wtp9)))) eq_refl eq_refl) (eq_trans (eq_sym (weakenTy_tsubstTy (appendHvl H0 (bindPat p25)) d0 S6 T58)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))))) (subst_etvar_Typing G11 S6 H79 (appendEnv G10 (appendEnv empty G9)) t31 (weakenTy T58 (appendHvl H0 (bindPat p25))) jm19 (appendEnv G12 (tsubstEnv d0 S6 (appendEnv empty G9))) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_etvar (appendEnv empty G9) H80))) (substhvl_ty_wfTy H79 _ _ H75 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H80)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.