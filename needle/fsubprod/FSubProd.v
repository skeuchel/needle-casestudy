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
  
  Fixpoint weakenIndextm (x11 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x11
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x11 k))
        | _ => (weakenIndextm x11 k)
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
    (forall (x11 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x11 k) k0) = (weakenIndextm x11 (appendHvl k k0)))).
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
    | tall (T1 : Ty) (T2 : Ty)
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
    | tabs (T : Ty) (t : Tm)
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
  Fixpoint shiftIndex (c : (Cutoff tm)) (x11 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x11)
      | (CS c) => match x11 with
        | (I0) => I0
        | (IS x11) => (IS (shiftIndex c x11))
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
  Fixpoint tshiftTy (c : (Cutoff ty)) (S13 : Ty) {struct S13} :
  Ty :=
    match S13 with
      | (tvar X19) => (tvar (tshiftIndex c X19))
      | (top) => (top)
      | (tarr T73 T74) => (tarr (tshiftTy c T73) (tshiftTy c T74))
      | (tall T75 T76) => (tall (tshiftTy c T75) (tshiftTy (CS c) T76))
      | (tprod T77 T78) => (tprod (tshiftTy c T77) (tshiftTy c T78))
    end.
  Fixpoint tshiftPat (c : (Cutoff ty)) (p18 : Pat) {struct p18} :
  Pat :=
    match p18 with
      | (pvar T73) => (pvar (tshiftTy c T73))
      | (pprod p19 p20) => (pprod (tshiftPat c p19) (tshiftPat (weakenCutoffty c (appendHvl H0 (bindPat p19))) p20))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x11) => (var (shiftIndex c x11))
      | (abs T73 t29) => (abs T73 (shiftTm (CS c) t29))
      | (app t30 t31) => (app (shiftTm c t30) (shiftTm c t31))
      | (tabs T74 t32) => (tabs T74 (shiftTm c t32))
      | (tapp t33 T75) => (tapp (shiftTm c t33) T75)
      | (prod t34 t35) => (prod (shiftTm c t34) (shiftTm c t35))
      | (lett p18 t36 t37) => (lett p18 (shiftTm c t36) (shiftTm (weakenCutofftm c (appendHvl H0 (bindPat p18))) t37))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x11) => (var x11)
      | (abs T73 t29) => (abs (tshiftTy c T73) (tshiftTm c t29))
      | (app t30 t31) => (app (tshiftTm c t30) (tshiftTm c t31))
      | (tabs T74 t32) => (tabs (tshiftTy c T74) (tshiftTm (CS c) t32))
      | (tapp t33 T75) => (tapp (tshiftTm c t33) (tshiftTy c T75))
      | (prod t34 t35) => (prod (tshiftTm c t34) (tshiftTm c t35))
      | (lett p18 t36 t37) => (lett (tshiftPat c p18) (tshiftTm c t36) (tshiftTm (weakenCutoffty c (appendHvl H0 (bindPat p18))) t37))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S13 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S13
      | (HS tm k) => (weakenTy S13 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S13 k))
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
        (T73 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x11 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x11
      | (HS b k) => (XS b (weakenTrace x11 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x11 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x11 k) k0) = (weakenTrace x11 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x11 : (Index tm)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x11 with
        | (I0) => s
        | (IS x11) => (var x11)
      end
      | (XS tm d) => match x11 with
        | (I0) => (var I0)
        | (IS x11) => (shiftTm C0 (substIndex d s x11))
      end
      | (XS ty d) => (tshiftTm C0 (substIndex d s x11))
    end.
  Fixpoint tsubstIndex (d : (Trace ty)) (S13 : Ty) (X19 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X19 with
        | (I0) => S13
        | (IS X19) => (tvar X19)
      end
      | (XS tm d) => (tsubstIndex d S13 X19)
      | (XS ty d) => match X19 with
        | (I0) => (tvar I0)
        | (IS X19) => (tshiftTy C0 (tsubstIndex d S13 X19))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S13 : Ty) (S14 : Ty) {struct S14} :
  Ty :=
    match S14 with
      | (tvar X19) => (tsubstIndex d S13 X19)
      | (top) => (top)
      | (tarr T73 T74) => (tarr (tsubstTy d S13 T73) (tsubstTy d S13 T74))
      | (tall T75 T76) => (tall (tsubstTy d S13 T75) (tsubstTy (weakenTrace d (HS ty H0)) S13 T76))
      | (tprod T77 T78) => (tprod (tsubstTy d S13 T77) (tsubstTy d S13 T78))
    end.
  Fixpoint tsubstPat (d : (Trace ty)) (S13 : Ty) (p18 : Pat) {struct p18} :
  Pat :=
    match p18 with
      | (pvar T73) => (pvar (tsubstTy d S13 T73))
      | (pprod p19 p20) => (pprod (tsubstPat d S13 p19) (tsubstPat (weakenTrace d (appendHvl H0 (bindPat p19))) S13 p20))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x11) => (substIndex d s x11)
      | (abs T73 t29) => (abs T73 (substTm (weakenTrace d (HS tm H0)) s t29))
      | (app t30 t31) => (app (substTm d s t30) (substTm d s t31))
      | (tabs T74 t32) => (tabs T74 (substTm (weakenTrace d (HS ty H0)) s t32))
      | (tapp t33 T75) => (tapp (substTm d s t33) T75)
      | (prod t34 t35) => (prod (substTm d s t34) (substTm d s t35))
      | (lett p18 t36 t37) => (lett p18 (substTm d s t36) (substTm (weakenTrace d (appendHvl H0 (bindPat p18))) s t37))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S13 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x11) => (var x11)
      | (abs T73 t29) => (abs (tsubstTy d S13 T73) (tsubstTm (weakenTrace d (HS tm H0)) S13 t29))
      | (app t30 t31) => (app (tsubstTm d S13 t30) (tsubstTm d S13 t31))
      | (tabs T74 t32) => (tabs (tsubstTy d S13 T74) (tsubstTm (weakenTrace d (HS ty H0)) S13 t32))
      | (tapp t33 T75) => (tapp (tsubstTm d S13 t33) (tsubstTy d S13 T75))
      | (prod t34 t35) => (prod (tsubstTm d S13 t34) (tsubstTm d S13 t35))
      | (lett p18 t36 t37) => (lett (tsubstPat d S13 p18) (tsubstTm d S13 t36) (tsubstTm (weakenTrace d (appendHvl H0 (bindPat p18))) S13 t37))
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
    (forall (d : (Trace ty)) (S13 : Ty) ,
      ((bindPat (tsubstPat d S13 p19)) = (bindPat p19)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tsubst_bindPat : interaction.
 Hint Rewrite stability_tsubst_bindPat : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x11 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x11)) = (var x11))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S14 : Ty) :
    (forall (k : Hvl) (X19 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S14 (tshiftIndex (weakenCutoffty C0 k) X19)) = (tvar X19))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S15 : Ty) (k : Hvl) (S14 : Ty) {struct S15} :
  ((tsubstTy (weakenTrace X0 k) S14 (tshiftTy (weakenCutoffty C0 k) S15)) = S15) :=
    match S15 return ((tsubstTy (weakenTrace X0 k) S14 (tshiftTy (weakenCutoffty C0 k) S15)) = S15) with
      | (tvar X19) => (tsubstIndex0_tshiftIndex0_reflection_ind S14 k X19)
      | (top) => eq_refl
      | (tarr T73 T74) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T73 k S14) (tsubst0_tshift0_Ty_reflection_ind T74 k S14))
      | (tall T73 T74) => (f_equal2 tall (tsubst0_tshift0_Ty_reflection_ind T73 k S14) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T74 (HS ty k) S14)))
      | (tprod T73 T74) => (f_equal2 tprod (tsubst0_tshift0_Ty_reflection_ind T73 k S14) (tsubst0_tshift0_Ty_reflection_ind T74 k S14))
    end.
  Fixpoint tsubst0_tshift0_Pat_reflection_ind (p20 : Pat) (k : Hvl) (S14 : Ty) {struct p20} :
  ((tsubstPat (weakenTrace X0 k) S14 (tshiftPat (weakenCutoffty C0 k) p20)) = p20) :=
    match p20 return ((tsubstPat (weakenTrace X0 k) S14 (tshiftPat (weakenCutoffty C0 k) p20)) = p20) with
      | (pvar T73) => (f_equal pvar (tsubst0_tshift0_Ty_reflection_ind T73 k S14))
      | (pprod p21 p22) => (f_equal2 pprod (tsubst0_tshift0_Pat_reflection_ind p21 k S14) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (tsubst0_tshift0_Pat_reflection_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) S14)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x11) => (substIndex0_shiftIndex0_reflection_ind s k x11)
      | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t29 (HS tm k) s)))
      | (app t30 t31) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t30 k s) (subst0_shift0_Tm_reflection_ind t31 k s))
      | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t29 (HS ty k) s)))
      | (tapp t29 T73) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t29 k s) eq_refl)
      | (prod t30 t31) => (f_equal2 prod (subst0_shift0_Tm_reflection_ind t30 k s) (subst0_shift0_Tm_reflection_ind t31 k s))
      | (lett p20 t30 t31) => (f_equal3 lett eq_refl (subst0_shift0_Tm_reflection_ind t30 k s) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (subst0_shift0_Tm_reflection_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) s)))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S14 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S14 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S14 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x11) => eq_refl
      | (abs T73 t29) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T73 k S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t29 (HS tm k) S14)))
      | (app t30 t31) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t30 k S14) (tsubst0_tshift0_Tm_reflection_ind t31 k S14))
      | (tabs T73 t29) => (f_equal2 tabs (tsubst0_tshift0_Ty_reflection_ind T73 k S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t29 (HS ty k) S14)))
      | (tapp t29 T73) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t29 k S14) (tsubst0_tshift0_Ty_reflection_ind T73 k S14))
      | (prod t30 t31) => (f_equal2 prod (tsubst0_tshift0_Tm_reflection_ind t30 k S14) (tsubst0_tshift0_Tm_reflection_ind t31 k S14))
      | (lett p20 t30 t31) => (f_equal3 lett (tsubst0_tshift0_Pat_reflection_ind p20 k S14) (tsubst0_tshift0_Tm_reflection_ind t30 k S14) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (tsubst0_tshift0_Tm_reflection_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) S14)))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S15 : Ty) : (forall (S14 : Ty) ,
    ((tsubstTy X0 S14 (tshiftTy C0 S15)) = S15)) := (tsubst0_tshift0_Ty_reflection_ind S15 H0).
  Definition tsubstPat0_tshiftPat0_reflection (p20 : Pat) : (forall (S14 : Ty) ,
    ((tsubstPat X0 S14 (tshiftPat C0 p20)) = p20)) := (tsubst0_tshift0_Pat_reflection_ind p20 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S14 : Ty) ,
    ((tsubstTm X0 S14 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff tm)) (x11 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c0) k) (shiftIndex (weakenCutofftm C0 k) x11)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c0 k) x11)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff ty)) (X19 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c0) k) (tshiftIndex (weakenCutoffty C0 k) X19)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c0 k) X19)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S14 : Ty) (k : Hvl) (c0 : (Cutoff ty)) {struct S14} :
    ((tshiftTy (weakenCutoffty (CS c0) k) (tshiftTy (weakenCutoffty C0 k) S14)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c0 k) S14))) :=
      match S14 return ((tshiftTy (weakenCutoffty (CS c0) k) (tshiftTy (weakenCutoffty C0 k) S14)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c0 k) S14))) with
        | (tvar X19) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c0 X19))
        | (top) => eq_refl
        | (tarr T73 T74) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T73 k c0) (tshift_tshift0_Ty_comm_ind T74 k c0))
        | (tall T73 T74) => (f_equal2 tall (tshift_tshift0_Ty_comm_ind T73 k c0) (tshift_tshift0_Ty_comm_ind T74 (HS ty k) c0))
        | (tprod T73 T74) => (f_equal2 tprod (tshift_tshift0_Ty_comm_ind T73 k c0) (tshift_tshift0_Ty_comm_ind T74 k c0))
      end.
    Fixpoint tshift_tshift0_Pat_comm_ind (p20 : Pat) (k : Hvl) (c0 : (Cutoff ty)) {struct p20} :
    ((tshiftPat (weakenCutoffty (CS c0) k) (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c0 k) p20))) :=
      match p20 return ((tshiftPat (weakenCutoffty (CS c0) k) (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c0 k) p20))) with
        | (pvar T73) => (f_equal pvar (tshift_tshift0_Ty_comm_ind T73 k c0))
        | (pprod p21 p22) => (f_equal2 pprod (tshift_tshift0_Pat_comm_ind p21 k c0) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p21)))) (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (eq_trans (tshift_tshift0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) c0) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftPat (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p21)))) eq_refl)))))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c0) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c0) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x11) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c0 x11))
        | (abs T73 t29) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t29 (HS tm k) c0))
        | (app t30 t31) => (f_equal2 app (shift_shift0_Tm_comm_ind t30 k c0) (shift_shift0_Tm_comm_ind t31 k c0))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (shift_shift0_Tm_comm_ind t29 (HS ty k) c0))
        | (tapp t29 T73) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t29 k c0) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (shift_shift0_Tm_comm_ind t30 k c0) (shift_shift0_Tm_comm_ind t31 k c0))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (shift_shift0_Tm_comm_ind t30 k c0) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c0) k (appendHvl H0 (bindPat p20))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c0 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c0 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t29 (HS tm k) c0))
        | (app t30 t31) => (f_equal2 app (shift_tshift0_Tm_comm_ind t30 k c0) (shift_tshift0_Tm_comm_ind t31 k c0))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (shift_tshift0_Tm_comm_ind t29 (HS ty k) c0))
        | (tapp t29 T73) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t29 k c0) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (shift_tshift0_Tm_comm_ind t30 k c0) (shift_tshift0_Tm_comm_ind t31 k c0))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (shift_tshift0_Tm_comm_ind t30 k c0) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c0 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c0 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c0 k) s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t29 (HS tm k) c0))
        | (app t30 t31) => (f_equal2 app (tshift_shift0_Tm_comm_ind t30 k c0) (tshift_shift0_Tm_comm_ind t31 k c0))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (tshift_shift0_Tm_comm_ind t29 (HS ty k) c0))
        | (tapp t29 T73) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t29 k c0) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (tshift_shift0_Tm_comm_ind t30 k c0) (tshift_shift0_Tm_comm_ind t31 k c0))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (tshift_shift0_Tm_comm_ind t30 k c0) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c0) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c0) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c0 k) s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T73 k c0) (tshift_tshift0_Tm_comm_ind t29 (HS tm k) c0))
        | (app t30 t31) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t30 k c0) (tshift_tshift0_Tm_comm_ind t31 k c0))
        | (tabs T73 t29) => (f_equal2 tabs (tshift_tshift0_Ty_comm_ind T73 k c0) (tshift_tshift0_Tm_comm_ind t29 (HS ty k) c0))
        | (tapp t29 T73) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t29 k c0) (tshift_tshift0_Ty_comm_ind T73 k c0))
        | (prod t30 t31) => (f_equal2 prod (tshift_tshift0_Tm_comm_ind t30 k c0) (tshift_tshift0_Tm_comm_ind t31 k c0))
        | (lett p20 t30 t31) => (f_equal3 lett (tshift_tshift0_Pat_comm_ind p20 k c0) (tshift_tshift0_Tm_comm_ind t30 k c0) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p20)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S14 : Ty) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftTy (CS c0) (tshiftTy C0 S14)) = (tshiftTy C0 (tshiftTy c0 S14)))) := (tshift_tshift0_Ty_comm_ind S14 H0).
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
    (forall (k : Hvl) (c0 : (Cutoff ty)) (S14 : Ty) ,
      ((weakenTy (tshiftTy c0 S14) k) = (tshiftTy (weakenCutoffty c0 k) (weakenTy S14 k)))).
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
      (forall (k : Hvl) (x11 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c0 k) (substIndex (weakenTrace X0 k) s x11)) = (substIndex (weakenTrace X0 k) (shiftTm c0 s) (shiftIndex (weakenCutofftm (CS c0) k) x11)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c0 : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x11 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c0 k) (substIndex (weakenTrace X0 k) s x11)) = (substIndex (weakenTrace X0 k) (tshiftTm c0 s) x11))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c0 : (Cutoff ty)) (S14 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c0 k) (tsubstIndex (weakenTrace X0 k) S14 X19)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c0 S14) (tshiftIndex (weakenCutoffty (CS c0) k) X19)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S15 : Ty) (k : Hvl) (c0 : (Cutoff ty)) (S14 : Ty) {struct S15} :
    ((tshiftTy (weakenCutoffty c0 k) (tsubstTy (weakenTrace X0 k) S14 S15)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S14) (tshiftTy (weakenCutoffty (CS c0) k) S15))) :=
      match S15 return ((tshiftTy (weakenCutoffty c0 k) (tsubstTy (weakenTrace X0 k) S14 S15)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S14) (tshiftTy (weakenCutoffty (CS c0) k) S15))) with
        | (tvar X19) => (tshiftTy_tsubstIndex0_comm_ind c0 S14 k X19)
        | (top) => eq_refl
        | (tarr T73 T74) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T73 k c0 S14) (tshift_tsubst0_Ty_comm_ind T74 k c0 S14))
        | (tall T73 T74) => (f_equal2 tall (tshift_tsubst0_Ty_comm_ind T73 k c0 S14) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T74 (HS ty k) c0 S14) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tprod T73 T74) => (f_equal2 tprod (tshift_tsubst0_Ty_comm_ind T73 k c0 S14) (tshift_tsubst0_Ty_comm_ind T74 k c0 S14))
      end.
    Fixpoint tshift_tsubst0_Pat_comm_ind (p20 : Pat) (k : Hvl) (c0 : (Cutoff ty)) (S14 : Ty) {struct p20} :
    ((tshiftPat (weakenCutoffty c0 k) (tsubstPat (weakenTrace X0 k) S14 p20)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S14) (tshiftPat (weakenCutoffty (CS c0) k) p20))) :=
      match p20 return ((tshiftPat (weakenCutoffty c0 k) (tsubstPat (weakenTrace X0 k) S14 p20)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S14) (tshiftPat (weakenCutoffty (CS c0) k) p20))) with
        | (pvar T73) => (f_equal pvar (tshift_tsubst0_Ty_comm_ind T73 k c0 S14))
        | (pprod p21 p22) => (f_equal2 pprod (tshift_tsubst0_Pat_comm_ind p21 k c0 S14) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p21)))) (f_equal3 tsubstPat (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) c0 S14) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftPat (eq_sym (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p21)))) eq_refl)))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutofftm (CS c0) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutofftm (CS c0) k) s0))) with
        | (var x11) => (shiftTm_substIndex0_comm_ind c0 s k x11)
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t29 (HS tm k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t30 t31) => (f_equal2 app (shift_subst0_Tm_comm_ind t30 k c0 s) (shift_subst0_Tm_comm_ind t31 k c0 s))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t29 (HS ty k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t29 T73) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t29 k c0 s) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (shift_subst0_Tm_comm_ind t30 k c0 s) (shift_subst0_Tm_comm_ind t31 k c0 s))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (shift_subst0_Tm_comm_ind t30 k c0 s) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c0) k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) (S14 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c0 k) (tsubstTm (weakenTrace X0 k) S14 s)) = (tsubstTm (weakenTrace X0 k) S14 (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c0 k) (tsubstTm (weakenTrace X0 k) S14 s)) = (tsubstTm (weakenTrace X0 k) S14 (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t29 (HS tm k) c0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t30 t31) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t30 k c0 S14) (shift_tsubst0_Tm_comm_ind t31 k c0 S14))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t29 (HS ty k) c0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t29 T73) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t29 k c0 S14) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (shift_tsubst0_Tm_comm_ind t30 k c0 S14) (shift_tsubst0_Tm_comm_ind t31 k c0 S14))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (shift_tsubst0_Tm_comm_ind t30 k c0 S14) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffty c0 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffty c0 k) s0))) with
        | (var x11) => (tshiftTm_substIndex0_comm_ind c0 s k x11)
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t29 (HS tm k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t30 t31) => (f_equal2 app (tshift_subst0_Tm_comm_ind t30 k c0 s) (tshift_subst0_Tm_comm_ind t31 k c0 s))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t29 (HS ty k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t29 T73) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t29 k c0 s) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (tshift_subst0_Tm_comm_ind t30 k c0 s) (tshift_subst0_Tm_comm_ind t31 k c0 s))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (tshift_subst0_Tm_comm_ind t30 k c0 s) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) (S14 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c0 k) (tsubstTm (weakenTrace X0 k) S14 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S14) (tshiftTm (weakenCutoffty (CS c0) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c0 k) (tsubstTm (weakenTrace X0 k) S14 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S14) (tshiftTm (weakenCutoffty (CS c0) k) s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T73 k c0 S14) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t29 (HS tm k) c0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t30 t31) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t30 k c0 S14) (tshift_tsubst0_Tm_comm_ind t31 k c0 S14))
        | (tabs T73 t29) => (f_equal2 tabs (tshift_tsubst0_Ty_comm_ind T73 k c0 S14) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t29 (HS ty k) c0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t29 T73) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t29 k c0 S14) (tshift_tsubst0_Ty_comm_ind T73 k c0 S14))
        | (prod t30 t31) => (f_equal2 prod (tshift_tsubst0_Tm_comm_ind t30 k c0 S14) (tshift_tsubst0_Tm_comm_ind t31 k c0 S14))
        | (lett p20 t30 t31) => (f_equal3 lett (tshift_tsubst0_Pat_comm_ind p20 k c0 S14) (tshift_tsubst0_Tm_comm_ind t30 k c0 S14) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) c0 S14) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S15 : Ty) : (forall (c0 : (Cutoff ty)) (S14 : Ty) ,
      ((tshiftTy c0 (tsubstTy X0 S14 S15)) = (tsubstTy X0 (tshiftTy c0 S14) (tshiftTy (CS c0) S15)))) := (tshift_tsubst0_Ty_comm_ind S15 H0).
    Definition tshiftPat_tsubstPat0_comm (p20 : Pat) : (forall (c0 : (Cutoff ty)) (S14 : Ty) ,
      ((tshiftPat c0 (tsubstPat X0 S14 p20)) = (tsubstPat X0 (tshiftTy c0 S14) (tshiftPat (CS c0) p20)))) := (tshift_tsubst0_Pat_comm_ind p20 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c0 (substTm X0 s s0)) = (substTm X0 (shiftTm c0 s) (shiftTm (CS c0) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff tm)) (S14 : Ty) ,
      ((shiftTm c0 (tsubstTm X0 S14 s)) = (tsubstTm X0 S14 (shiftTm c0 s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c0 (substTm X0 s s0)) = (substTm X0 (tshiftTm c0 s) (tshiftTm c0 s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff ty)) (S14 : Ty) ,
      ((tshiftTm c0 (tsubstTm X0 S14 s)) = (tsubstTm X0 (tshiftTy c0 S14) (tshiftTm (CS c0) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d0 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x11 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d0) k) s (shiftIndex (weakenCutofftm C0 k) x11)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d0 k) s x11)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d0 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x11 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d0) k) s x11) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d0 k) s x11)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d0 : (Trace ty)) (S14 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d0) k) S14 X19) = (tsubstIndex (weakenTrace d0 k) S14 X19))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d0 : (Trace ty)) (S14 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d0) k) S14 (tshiftIndex (weakenCutoffty C0 k) X19)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d0 k) S14 X19)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S15 : Ty) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) {struct S15} :
    ((tsubstTy (weakenTrace (XS ty d0) k) S14 (tshiftTy (weakenCutoffty C0 k) S15)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d0 k) S14 S15))) :=
      match S15 return ((tsubstTy (weakenTrace (XS ty d0) k) S14 (tshiftTy (weakenCutoffty C0 k) S15)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d0 k) S14 S15))) with
        | (tvar X19) => (tsubstIndex_tshiftTy0_comm_ind d0 S14 k X19)
        | (top) => eq_refl
        | (tarr T73 T74) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T73 k d0 S14) (tsubst_tshift0_Ty_comm_ind T74 k d0 S14))
        | (tall T73 T74) => (f_equal2 tall (tsubst_tshift0_Ty_comm_ind T73 k d0 S14) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T74 (HS ty k) d0 S14) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tprod T73 T74) => (f_equal2 tprod (tsubst_tshift0_Ty_comm_ind T73 k d0 S14) (tsubst_tshift0_Ty_comm_ind T74 k d0 S14))
      end.
    Fixpoint tsubst_tshift0_Pat_comm_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace (XS ty d0) k) S14 (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d0 k) S14 p20))) :=
      match p20 return ((tsubstPat (weakenTrace (XS ty d0) k) S14 (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d0 k) S14 p20))) with
        | (pvar T73) => (f_equal pvar (tsubst_tshift0_Ty_comm_ind T73 k d0 S14))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tshift0_Pat_comm_ind p21 k d0 S14) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (eq_trans (tsubst_tshift0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S14) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d0) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d0) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x11) => (substIndex_shiftTm0_comm_ind d0 s k x11)
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t29 (HS tm k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (subst_shift0_Tm_comm_ind t30 k d0 s) (subst_shift0_Tm_comm_ind t31 k d0 s))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t29 (HS ty k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t29 k d0 s) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (subst_shift0_Tm_comm_ind t30 k d0 s) (subst_shift0_Tm_comm_ind t31 k d0 s))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (subst_shift0_Tm_comm_ind t30 k d0 s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d0) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d0) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x11) => (substIndex_tshiftTm0_comm_ind d0 s k x11)
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t29 (HS tm k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (subst_tshift0_Tm_comm_ind t30 k d0 s) (subst_tshift0_Tm_comm_ind t31 k d0 s))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t29 (HS ty k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t29 k d0 s) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (subst_tshift0_Tm_comm_ind t30 k d0 s) (subst_tshift0_Tm_comm_ind t31 k d0 s))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (subst_tshift0_Tm_comm_ind t30 k d0 s) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append tm (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (subst_tshift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S14 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d0 k) S14 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S14 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d0 k) S14 s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t29 (HS tm k) d0 S14) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t30 k d0 S14) (tsubst_shift0_Tm_comm_ind t31 k d0 S14))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t29 (HS ty k) d0 S14) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t29 k d0 S14) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (tsubst_shift0_Tm_comm_ind t30 k d0 S14) (tsubst_shift0_Tm_comm_ind t31 k d0 S14))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (tsubst_shift0_Tm_comm_ind t30 k d0 S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tsubst_shift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S14) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d0) k) S14 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d0 k) S14 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d0) k) S14 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d0 k) S14 s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T73 k d0 S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t29 (HS tm k) d0 S14) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t30 k d0 S14) (tsubst_tshift0_Tm_comm_ind t31 k d0 S14))
        | (tabs T73 t29) => (f_equal2 tabs (tsubst_tshift0_Ty_comm_ind T73 k d0 S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t29 (HS ty k) d0 S14) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t29 k d0 S14) (tsubst_tshift0_Ty_comm_ind T73 k d0 S14))
        | (prod t30 t31) => (f_equal2 prod (tsubst_tshift0_Tm_comm_ind t30 k d0 S14) (tsubst_tshift0_Tm_comm_ind t31 k d0 S14))
        | (lett p20 t30 t31) => (f_equal3 lett (tsubst_tshift0_Pat_comm_ind p20 k d0 S14) (tsubst_tshift0_Tm_comm_ind t30 k d0 S14) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tsubst_tshift0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S14) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S15 : Ty) : (forall (d0 : (Trace ty)) (S14 : Ty) ,
      ((tsubstTy (XS ty d0) S14 (tshiftTy C0 S15)) = (tshiftTy C0 (tsubstTy d0 S14 S15)))) := (tsubst_tshift0_Ty_comm_ind S15 H0).
    Definition tsubstPat_tshiftPat0_comm (p20 : Pat) : (forall (d0 : (Trace ty)) (S14 : Ty) ,
      ((tsubstPat (XS ty d0) S14 (tshiftPat C0 p20)) = (tshiftPat C0 (tsubstPat d0 S14 p20)))) := (tsubst_tshift0_Pat_comm_ind p20 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d0) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d0 s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d0) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d0 s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S14 : Ty) ,
      ((tsubstTm d0 S14 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d0 S14 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S14 : Ty) ,
      ((tsubstTm (XS ty d0) S14 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d0 S14 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S15 : Ty) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) {struct S15} :
    ((tsubstTy (weakenTrace (XS tm d0) k) S14 S15) = (tsubstTy (weakenTrace d0 k) S14 S15)) :=
      match S15 return ((tsubstTy (weakenTrace (XS tm d0) k) S14 S15) = (tsubstTy (weakenTrace d0 k) S14 S15)) with
        | (tvar X19) => (tsubstIndex_shiftTy0_comm_ind d0 S14 k X19)
        | (top) => eq_refl
        | (tarr T73 T74) => (f_equal2 tarr (tsubst_tm_Ty_ind T73 k d0 S14) (tsubst_tm_Ty_ind T74 k d0 S14))
        | (tall T73 T74) => (f_equal2 tall (tsubst_tm_Ty_ind T73 k d0 S14) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T74 (HS ty k) d0 S14) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl))))
        | (tprod T73 T74) => (f_equal2 tprod (tsubst_tm_Ty_ind T73 k d0 S14) (tsubst_tm_Ty_ind T74 k d0 S14))
      end.
    Fixpoint tsubst_tm_Pat_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace (XS tm d0) k) S14 p20) = (tsubstPat (weakenTrace d0 k) S14 p20)) :=
      match p20 return ((tsubstPat (weakenTrace (XS tm d0) k) S14 p20) = (tsubstPat (weakenTrace d0 k) S14 p20)) with
        | (pvar T73) => (f_equal pvar (tsubst_tm_Ty_ind T73 k d0 S14))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tm_Pat_ind p21 k d0 S14) (eq_trans (f_equal3 tsubstPat (weakenTrace_append ty (XS tm d0) k (appendHvl H0 (bindPat p21))) eq_refl eq_refl) (eq_trans (tsubst_tm_Pat_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S14) (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d0) k) S14 s) = (tsubstTm (weakenTrace d0 k) S14 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d0) k) S14 s) = (tsubstTm (weakenTrace d0 k) S14 s)) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs (tsubst_tm_Ty_ind T73 k d0 S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t29 (HS tm k) d0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t30 t31) => (f_equal2 app (tsubst_tm_Tm_ind t30 k d0 S14) (tsubst_tm_Tm_ind t31 k d0 S14))
        | (tabs T73 t29) => (f_equal2 tabs (tsubst_tm_Ty_ind T73 k d0 S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t29 (HS ty k) d0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t29 T73) => (f_equal2 tapp (tsubst_tm_Tm_ind t29 k d0 S14) (tsubst_tm_Ty_ind T73 k d0 S14))
        | (prod t30 t31) => (f_equal2 prod (tsubst_tm_Tm_ind t30 k d0 S14) (tsubst_tm_Tm_ind t31 k d0 S14))
        | (lett p20 t30 t31) => (f_equal3 lett (tsubst_tm_Pat_ind p20 k d0 S14) (tsubst_tm_Tm_ind t30 k d0 S14) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (appendHvl H0 (bindPat p20))) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl))))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S15 : Ty) : (forall (d0 : (Trace ty)) (S14 : Ty) ,
      ((tsubstTy (XS tm d0) S14 S15) = (tsubstTy d0 S14 S15))) := (tsubst_tm_Ty_ind S15 H0).
    Definition tsubstPat_tm (p20 : Pat) : (forall (d0 : (Trace ty)) (S14 : Ty) ,
      ((tsubstPat (XS tm d0) S14 p20) = (tsubstPat d0 S14 p20))) := (tsubst_tm_Pat_ind p20 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d0 : (Trace ty)) (S14 : Ty) ,
      ((tsubstTm (XS tm d0) S14 s) = (tsubstTm d0 S14 s))) := (tsubst_tm_Tm_ind s H0).
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
      (forall (k : Hvl) (x11 : (Index tm)) ,
        ((substTm (weakenTrace d0 k) s (substIndex (weakenTrace X0 k) s0 x11)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substIndex (weakenTrace (XS tm d0) k) s x11)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d0 : (Trace ty)) (S14 : Ty) (s : Tm) :
      (forall (k : Hvl) (x11 : (Index tm)) ,
        ((tsubstTm (weakenTrace d0 k) S14 (substIndex (weakenTrace X0 k) s x11)) = (substIndex (weakenTrace X0 k) (tsubstTm d0 S14 s) x11))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) :
      (forall (k : Hvl) (X19 : (Index ty)) ,
        ((tsubstTy (weakenTrace d0 k) S14 (tsubstIndex (weakenTrace X0 k) S15 X19)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S14 S15) (tsubstIndex (weakenTrace (XS ty d0) k) S14 X19)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d0 : (Trace tm)) (s : Tm) (S14 : Ty) :
      (forall (k : Hvl) (x11 : (Index tm)) ,
        ((substIndex (weakenTrace d0 k) s x11) = (tsubstTm (weakenTrace X0 k) S14 (substIndex (weakenTrace (XS ty d0) k) s x11)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S16 : Ty) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) {struct S16} :
    ((tsubstTy (weakenTrace d0 k) S14 (tsubstTy (weakenTrace X0 k) S15 S16)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S14 S15) (tsubstTy (weakenTrace (XS ty d0) k) S14 S16))) :=
      match S16 return ((tsubstTy (weakenTrace d0 k) S14 (tsubstTy (weakenTrace X0 k) S15 S16)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S14 S15) (tsubstTy (weakenTrace (XS ty d0) k) S14 S16))) with
        | (tvar X19) => (tsubstTy_tsubstIndex0_commright_ind d0 S14 S15 k X19)
        | (top) => eq_refl
        | (tarr T73 T74) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T73 k d0 S14 S15) (tsubst_tsubst0_Ty_comm_ind T74 k d0 S14 S15))
        | (tall T73 T74) => (f_equal2 tall (tsubst_tsubst0_Ty_comm_ind T73 k d0 S14 S15) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T74 (HS ty k) d0 S14 S15) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tprod T73 T74) => (f_equal2 tprod (tsubst_tsubst0_Ty_comm_ind T73 k d0 S14 S15) (tsubst_tsubst0_Ty_comm_ind T74 k d0 S14 S15))
      end.
    Fixpoint tsubst_tsubst0_Pat_comm_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace d0 k) S14 (tsubstPat (weakenTrace X0 k) S15 p20)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S14 S15) (tsubstPat (weakenTrace (XS ty d0) k) S14 p20))) :=
      match p20 return ((tsubstPat (weakenTrace d0 k) S14 (tsubstPat (weakenTrace X0 k) S15 p20)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S14 S15) (tsubstPat (weakenTrace (XS ty d0) k) S14 p20))) with
        | (pvar T73) => (f_equal pvar (tsubst_tsubst0_Ty_comm_ind T73 k d0 S14 S15))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tsubst0_Pat_comm_ind p21 k d0 S14 S15) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal3 tsubstPat (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S14 S15) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS tm d0) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS tm d0) k) s s1))) with
        | (var x11) => (substTm_substIndex0_commright_ind d0 s s0 k x11)
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t29 (HS tm k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (subst_subst0_Tm_comm_ind t30 k d0 s s0) (subst_subst0_Tm_comm_ind t31 k d0 s s0))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t29 (HS ty k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t29 k d0 s s0) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (subst_subst0_Tm_comm_ind t30 k d0 s s0) (subst_subst0_Tm_comm_ind t31 k d0 s s0))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (subst_subst0_Tm_comm_ind t30 k d0 s s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) (S14 : Ty) {struct s0} :
    ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S14 s0)) = (tsubstTm (weakenTrace X0 k) S14 (substTm (weakenTrace (XS ty d0) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S14 s0)) = (tsubstTm (weakenTrace X0 k) S14 (substTm (weakenTrace (XS ty d0) k) s s0))) with
        | (var x11) => (substTy_tsubstIndex0_commleft_ind d0 s S14 k x11)
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t29 (HS tm k) d0 s S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t30 k d0 s S14) (subst_tsubst0_Tm_comm_ind t31 k d0 s S14))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t29 (HS ty k) d0 s S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t29 k d0 s S14) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (subst_tsubst0_Tm_comm_ind t30 k d0 s S14) (subst_tsubst0_Tm_comm_ind t31 k d0 s S14))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (subst_tsubst0_Tm_comm_ind t30 k d0 s S14) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s S14) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d0 k) S14 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S14 s) (tsubstTm (weakenTrace d0 k) S14 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d0 k) S14 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S14 s) (tsubstTm (weakenTrace d0 k) S14 s0))) with
        | (var x11) => (tsubstTm_substIndex0_commright_ind d0 S14 s k x11)
        | (abs T73 t29) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t29 (HS tm k) d0 S14 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t30 k d0 S14 s) (tsubst_subst0_Tm_comm_ind t31 k d0 S14 s))
        | (tabs T73 t29) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t29 (HS ty k) d0 S14 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t29 k d0 S14 s) eq_refl)
        | (prod t30 t31) => (f_equal2 prod (tsubst_subst0_Tm_comm_ind t30 k d0 S14 s) (tsubst_subst0_Tm_comm_ind t31 k d0 S14 s))
        | (lett p20 t30 t31) => (f_equal3 lett eq_refl (tsubst_subst0_Tm_comm_ind t30 k d0 S14 s) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S14 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S14 (tsubstTm (weakenTrace X0 k) S15 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S14 S15) (tsubstTm (weakenTrace (XS ty d0) k) S14 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S14 (tsubstTm (weakenTrace X0 k) S15 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S14 S15) (tsubstTm (weakenTrace (XS ty d0) k) S14 s))) with
        | (var x11) => eq_refl
        | (abs T73 t29) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T73 k d0 S14 S15) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t29 (HS tm k) d0 S14 S15) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t30 t31) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t30 k d0 S14 S15) (tsubst_tsubst0_Tm_comm_ind t31 k d0 S14 S15))
        | (tabs T73 t29) => (f_equal2 tabs (tsubst_tsubst0_Ty_comm_ind T73 k d0 S14 S15) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t29 (HS ty k) d0 S14 S15) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t29 T73) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t29 k d0 S14 S15) (tsubst_tsubst0_Ty_comm_ind T73 k d0 S14 S15))
        | (prod t30 t31) => (f_equal2 prod (tsubst_tsubst0_Tm_comm_ind t30 k d0 S14 S15) (tsubst_tsubst0_Tm_comm_ind t31 k d0 S14 S15))
        | (lett p20 t30 t31) => (f_equal3 lett (tsubst_tsubst0_Pat_comm_ind p20 k d0 S14 S15) (tsubst_tsubst0_Tm_comm_ind t30 k d0 S14 S15) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t31 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S14 S15) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S16 : Ty) : (forall (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) ,
      ((tsubstTy d0 S14 (tsubstTy X0 S15 S16)) = (tsubstTy X0 (tsubstTy d0 S14 S15) (tsubstTy (XS ty d0) S14 S16)))) := (tsubst_tsubst0_Ty_comm_ind S16 H0).
    Definition tsubstPat_tsubstPat0_comm (p20 : Pat) : (forall (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) ,
      ((tsubstPat d0 S14 (tsubstPat X0 S15 p20)) = (tsubstPat X0 (tsubstTy d0 S14 S15) (tsubstPat (XS ty d0) S14 p20)))) := (tsubst_tsubst0_Pat_comm_ind p20 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d0 s (substTm X0 s0 s1)) = (substTm X0 (substTm d0 s s0) (substTm (XS tm d0) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) (S14 : Ty) ,
      ((substTm d0 s (tsubstTm X0 S14 s0)) = (tsubstTm X0 S14 (substTm (XS ty d0) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d0 : (Trace ty)) (S14 : Ty) (s : Tm) ,
      ((tsubstTm d0 S14 (substTm X0 s s0)) = (substTm X0 (tsubstTm d0 S14 s) (tsubstTm d0 S14 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) ,
      ((tsubstTm d0 S14 (tsubstTm X0 S15 s)) = (tsubstTm X0 (tsubstTy d0 S14 S15) (tsubstTm (XS ty d0) S14 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) (S15 : Ty) ,
        ((weakenTy (tsubstTy d0 S14 S15) k) = (tsubstTy (weakenTrace d0 k) S14 (weakenTy S15 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) (p20 : Pat) ,
        ((weakenPat (tsubstPat d0 S14 p20) k) = (tsubstPat (weakenTrace d0 k) S14 (weakenPat p20 k)))).
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
      (forall (k : Hvl) (d0 : (Trace ty)) (S14 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d0 S14 s) k) = (tsubstTm (weakenTrace d0 k) S14 (weakenTm s k)))).
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
    | wfTy_tvar (X19 : (Index ty))
        (wfi : (wfindex k X19)) :
        (wfTy k (tvar X19))
    | wfTy_top : (wfTy k (top))
    | wfTy_tarr {T73 : Ty}
        (wf : (wfTy k T73)) {T74 : Ty}
        (wf0 : (wfTy k T74)) :
        (wfTy k (tarr T73 T74))
    | wfTy_tall {T75 : Ty}
        (wf : (wfTy k T75)) {T76 : Ty}
        (wf0 : (wfTy (HS ty k) T76)) :
        (wfTy k (tall T75 T76))
    | wfTy_tprod {T77 : Ty}
        (wf : (wfTy k T77)) {T78 : Ty}
        (wf0 : (wfTy k T78)) :
        (wfTy k (tprod T77 T78)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T73 : Ty}
        (wf : (wfTy k T73)) :
        (wfPat k (pvar T73))
    | wfPat_pprod {p20 : Pat}
        (wf : (wfPat k p20)) {p21 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bindPat p20))) p21))
        : (wfPat k (pprod p20 p21)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x11 : (Index tm))
        (wfi : (wfindex k x11)) :
        (wfTm k (var x11))
    | wfTm_abs {T73 : Ty}
        (wf : (wfTy k T73)) {t29 : Tm}
        (wf0 : (wfTm (HS tm k) t29)) :
        (wfTm k (abs T73 t29))
    | wfTm_app {t30 : Tm}
        (wf : (wfTm k t30)) {t31 : Tm}
        (wf0 : (wfTm k t31)) :
        (wfTm k (app t30 t31))
    | wfTm_tabs {T74 : Ty}
        (wf : (wfTy k T74)) {t32 : Tm}
        (wf0 : (wfTm (HS ty k) t32)) :
        (wfTm k (tabs T74 t32))
    | wfTm_tapp {t33 : Tm}
        (wf : (wfTm k t33)) {T75 : Ty}
        (wf0 : (wfTy k T75)) :
        (wfTm k (tapp t33 T75))
    | wfTm_prod {t34 : Tm}
        (wf : (wfTm k t34)) {t35 : Tm}
        (wf0 : (wfTm k t35)) :
        (wfTm k (prod t34 t35))
    | wfTm_lett {p20 : Pat}
        (wf : (wfPat k p20)) {t36 : Tm}
        (wf0 : (wfTm k t36)) {t37 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bindPat p20))) t37))
        : (wfTm k (lett p20 t36 t37)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H27 : (wfTy k (tvar X))) : (wfindex k X) := match H27 in (wfTy _ S14) return match S14 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H29 : (wfTy k1 (tarr T1 T2))) : (wfTy k1 T1) := match H29 in (wfTy _ S16) return match S16 return Prop with
    | (tarr T1 T2) => (wfTy k1 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H29 : (wfTy k1 (tarr T1 T2))) : (wfTy k1 T2) := match H29 in (wfTy _ S16) return match S16 return Prop with
    | (tarr T1 T2) => (wfTy k1 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H30 : (wfTy k2 (tall T1 T2))) : (wfTy k2 T1) := match H30 in (wfTy _ S17) return match S17 return Prop with
    | (tall T1 T2) => (wfTy k2 T1)
    | _ => True
  end with
    | (wfTy_tall T1 H4 T2 H5) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tall_2 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H30 : (wfTy k2 (tall T1 T2))) : (wfTy (HS ty k2) T2) := match H30 in (wfTy _ S17) return match S17 return Prop with
    | (tall T1 T2) => (wfTy (HS ty k2) T2)
    | _ => True
  end with
    | (wfTy_tall T1 H4 T2 H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tprod_0 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H31 : (wfTy k3 (tprod T1 T2))) : (wfTy k3 T1) := match H31 in (wfTy _ S18) return match S18 return Prop with
    | (tprod T1 T2) => (wfTy k3 T1)
    | _ => True
  end with
    | (wfTy_tprod T1 H6 T2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTy_tprod_1 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H31 : (wfTy k3 (tprod T1 T2))) : (wfTy k3 T2) := match H31 in (wfTy _ S18) return match S18 return Prop with
    | (tprod T1 T2) => (wfTy k3 T2)
    | _ => True
  end with
    | (wfTy_tprod T1 H6 T2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfPat_pvar_1 (k4 : Hvl) (T : Ty) (H32 : (wfPat k4 (pvar T))) : (wfTy k4 T) := match H32 in (wfPat _ p20) return match p20 return Prop with
    | (pvar T) => (wfTy k4 T)
    | _ => True
  end with
    | (wfPat_pvar T H8) => H8
    | _ => I
  end.
  Definition inversion_wfPat_pprod_0 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H33 : (wfPat k5 (pprod p1 p2))) : (wfPat k5 p1) := match H33 in (wfPat _ p21) return match p21 return Prop with
    | (pprod p1 p2) => (wfPat k5 p1)
    | _ => True
  end with
    | (wfPat_pprod p1 H9 p2 H10) => H9
    | _ => I
  end.
  Definition inversion_wfPat_pprod_1 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H33 : (wfPat k5 (pprod p1 p2))) : (wfPat (appendHvl k5 (appendHvl H0 (bindPat p1))) p2) := match H33 in (wfPat _ p21) return match p21 return Prop with
    | (pprod p1 p2) => (wfPat (appendHvl k5 (appendHvl H0 (bindPat p1))) p2)
    | _ => True
  end with
    | (wfPat_pprod p1 H9 p2 H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k6 : Hvl) (x : (Index tm)) (H34 : (wfTm k6 (var x))) : (wfindex k6 x) := match H34 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k6 x)
    | _ => True
  end with
    | (wfTm_var x H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k7 : Hvl) (T : Ty) (t : Tm) (H35 : (wfTm k7 (abs T t))) : (wfTy k7 T) := match H35 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_abs T H12 t H13) => H12
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k7 : Hvl) (T : Ty) (t : Tm) (H35 : (wfTm k7 (abs T t))) : (wfTm (HS tm k7) t) := match H35 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k7) t)
    | _ => True
  end with
    | (wfTm_abs T H12 t H13) => H13
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k8 (app t1 t2))) : (wfTm k8 t1) := match H36 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_app t1 H14 t2 H15) => H14
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k8 (app t1 t2))) : (wfTm k8 t2) := match H36 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_app t1 H14 t2 H15) => H15
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k9 : Hvl) (T : Ty) (t : Tm) (H37 : (wfTm k9 (tabs T t))) : (wfTy k9 T) := match H37 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTy k9 T)
    | _ => True
  end with
    | (wfTm_tabs T H16 t H17) => H16
    | _ => I
  end.
  Definition inversion_wfTm_tabs_2 (k9 : Hvl) (T : Ty) (t : Tm) (H37 : (wfTm k9 (tabs T t))) : (wfTm (HS ty k9) t) := match H37 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTm (HS ty k9) t)
    | _ => True
  end with
    | (wfTm_tabs T H16 t H17) => H17
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k10 : Hvl) (t : Tm) (T : Ty) (H38 : (wfTm k10 (tapp t T))) : (wfTm k10 t) := match H38 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k10 t)
    | _ => True
  end with
    | (wfTm_tapp t H18 T H19) => H18
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k10 : Hvl) (t : Tm) (T : Ty) (H38 : (wfTm k10 (tapp t T))) : (wfTy k10 T) := match H38 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k10 T)
    | _ => True
  end with
    | (wfTm_tapp t H18 T H19) => H19
    | _ => I
  end.
  Definition inversion_wfTm_prod_0 (k11 : Hvl) (t1 : Tm) (t2 : Tm) (H39 : (wfTm k11 (prod t1 t2))) : (wfTm k11 t1) := match H39 in (wfTm _ s4) return match s4 return Prop with
    | (prod t1 t2) => (wfTm k11 t1)
    | _ => True
  end with
    | (wfTm_prod t1 H20 t2 H21) => H20
    | _ => I
  end.
  Definition inversion_wfTm_prod_1 (k11 : Hvl) (t1 : Tm) (t2 : Tm) (H39 : (wfTm k11 (prod t1 t2))) : (wfTm k11 t2) := match H39 in (wfTm _ s4) return match s4 return Prop with
    | (prod t1 t2) => (wfTm k11 t2)
    | _ => True
  end with
    | (wfTm_prod t1 H20 t2 H21) => H21
    | _ => I
  end.
  Definition inversion_wfTm_lett_0 (k12 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H40 : (wfTm k12 (lett p t1 t2))) : (wfPat k12 p) := match H40 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfPat k12 p)
    | _ => True
  end with
    | (wfTm_lett p H22 t1 H23 t2 H24) => H22
    | _ => I
  end.
  Definition inversion_wfTm_lett_1 (k12 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H40 : (wfTm k12 (lett p t1 t2))) : (wfTm k12 t1) := match H40 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfTm k12 t1)
    | _ => True
  end with
    | (wfTm_lett p H22 t1 H23 t2 H24) => H23
    | _ => I
  end.
  Definition inversion_wfTm_lett_2 (k12 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H40 : (wfTm k12 (lett p t1 t2))) : (wfTm (appendHvl k12 (appendHvl H0 (bindPat p))) t2) := match H40 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfTm (appendHvl k12 (appendHvl H0 (bindPat p))) t2)
    | _ => True
  end with
    | (wfTm_lett p H22 t1 H23 t2 H24) => H24
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c0 : (Cutoff tm)) (k13 : Hvl) (k14 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k13 : Hvl)
        :
        (shifthvl_tm C0 k13 (HS tm k13))
    | shifthvl_tm_there_tm
        (c0 : (Cutoff tm)) (k13 : Hvl)
        (k14 : Hvl) :
        (shifthvl_tm c0 k13 k14) -> (shifthvl_tm (CS c0) (HS tm k13) (HS tm k14))
    | shifthvl_tm_there_ty
        (c0 : (Cutoff tm)) (k13 : Hvl)
        (k14 : Hvl) :
        (shifthvl_tm c0 k13 k14) -> (shifthvl_tm c0 (HS ty k13) (HS ty k14)).
  Inductive shifthvl_ty : (forall (c0 : (Cutoff ty)) (k13 : Hvl) (k14 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k13 : Hvl)
        :
        (shifthvl_ty C0 k13 (HS ty k13))
    | shifthvl_ty_there_tm
        (c0 : (Cutoff ty)) (k13 : Hvl)
        (k14 : Hvl) :
        (shifthvl_ty c0 k13 k14) -> (shifthvl_ty c0 (HS tm k13) (HS tm k14))
    | shifthvl_ty_there_ty
        (c0 : (Cutoff ty)) (k13 : Hvl)
        (k14 : Hvl) :
        (shifthvl_ty c0 k13 k14) -> (shifthvl_ty (CS c0) (HS ty k13) (HS ty k14)).
  Lemma weaken_shifthvl_tm  :
    (forall (k13 : Hvl) {c0 : (Cutoff tm)} {k14 : Hvl} {k15 : Hvl} ,
      (shifthvl_tm c0 k14 k15) -> (shifthvl_tm (weakenCutofftm c0 k13) (appendHvl k14 k13) (appendHvl k15 k13))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k13 : Hvl) {c0 : (Cutoff ty)} {k14 : Hvl} {k15 : Hvl} ,
      (shifthvl_ty c0 k14 k15) -> (shifthvl_ty (weakenCutoffty c0 k13) (appendHvl k14 k13) (appendHvl k15 k13))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c0 : (Cutoff tm)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) (x11 : (Index tm)) ,
      (wfindex k13 x11) -> (wfindex k14 (shiftIndex c0 x11))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c0 : (Cutoff tm)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) (X19 : (Index ty)) ,
      (wfindex k13 X19) -> (wfindex k14 X19)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c0 : (Cutoff ty)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) (x11 : (Index tm)) ,
      (wfindex k13 x11) -> (wfindex k14 x11)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c0 : (Cutoff ty)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) (X19 : (Index ty)) ,
      (wfindex k13 X19) -> (wfindex k14 (tshiftIndex c0 X19))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k13 : Hvl) ,
    (forall (S19 : Ty) (wf : (wfTy k13 S19)) ,
      (forall (c0 : (Cutoff tm)) (k14 : Hvl) ,
        (shifthvl_tm c0 k13 k14) -> (wfTy k14 S19)))) := (ind_wfTy (fun (k13 : Hvl) (S19 : Ty) (wf : (wfTy k13 S19)) =>
    (forall (c0 : (Cutoff tm)) (k14 : Hvl) ,
      (shifthvl_tm c0 k13 k14) -> (wfTy k14 S19))) (fun (k13 : Hvl) (X19 : (Index ty)) (wfi : (wfindex k13 X19)) (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTy_tvar k14 _ (shift_wfindex_ty c0 k13 k14 ins X19 wfi))) (fun (k13 : Hvl) (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTy_top k14)) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTy_tarr k14 (IHT1 c0 k14 (weaken_shifthvl_tm H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_tm H0 ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS ty k13) T2)) IHT2 (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTy_tall k14 (IHT1 c0 k14 (weaken_shifthvl_tm H0 ins)) (IHT2 c0 (HS ty k14) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTy_tprod k14 (IHT1 c0 k14 (weaken_shifthvl_tm H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTy : (forall (k13 : Hvl) ,
    (forall (S19 : Ty) (wf : (wfTy k13 S19)) ,
      (forall (c0 : (Cutoff ty)) (k14 : Hvl) ,
        (shifthvl_ty c0 k13 k14) -> (wfTy k14 (tshiftTy c0 S19))))) := (ind_wfTy (fun (k13 : Hvl) (S19 : Ty) (wf : (wfTy k13 S19)) =>
    (forall (c0 : (Cutoff ty)) (k14 : Hvl) ,
      (shifthvl_ty c0 k13 k14) -> (wfTy k14 (tshiftTy c0 S19)))) (fun (k13 : Hvl) (X19 : (Index ty)) (wfi : (wfindex k13 X19)) (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTy_tvar k14 _ (tshift_wfindex_ty c0 k13 k14 ins X19 wfi))) (fun (k13 : Hvl) (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTy_top k14)) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTy_tarr k14 (IHT1 c0 k14 (weaken_shifthvl_ty H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_ty H0 ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS ty k13) T2)) IHT2 (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTy_tall k14 (IHT1 c0 k14 (weaken_shifthvl_ty H0 ins)) (IHT2 (CS c0) (HS ty k14) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTy_tprod k14 (IHT1 c0 k14 (weaken_shifthvl_ty H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_ty H0 ins))))).
  Definition shift_wfPat : (forall (k13 : Hvl) ,
    (forall (p22 : Pat) (wf : (wfPat k13 p22)) ,
      (forall (c0 : (Cutoff tm)) (k14 : Hvl) ,
        (shifthvl_tm c0 k13 k14) -> (wfPat k14 p22)))) := (ind_wfPat (fun (k13 : Hvl) (p22 : Pat) (wf : (wfPat k13 p22)) =>
    (forall (c0 : (Cutoff tm)) (k14 : Hvl) ,
      (shifthvl_tm c0 k13 k14) -> (wfPat k14 p22))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfPat_pvar k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_tm H0 ins)))) (fun (k13 : Hvl) (p1 : Pat) (wf : (wfPat k13 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k13 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfPat_pprod k14 (IHp1 c0 k14 (weaken_shifthvl_tm H0 ins)) (IHp2 (weakenCutofftm c0 (appendHvl H0 (bindPat p1))) (appendHvl k14 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p1)) ins))))).
  Definition tshift_wfPat : (forall (k13 : Hvl) ,
    (forall (p22 : Pat) (wf : (wfPat k13 p22)) ,
      (forall (c0 : (Cutoff ty)) (k14 : Hvl) ,
        (shifthvl_ty c0 k13 k14) -> (wfPat k14 (tshiftPat c0 p22))))) := (ind_wfPat (fun (k13 : Hvl) (p22 : Pat) (wf : (wfPat k13 p22)) =>
    (forall (c0 : (Cutoff ty)) (k14 : Hvl) ,
      (shifthvl_ty c0 k13 k14) -> (wfPat k14 (tshiftPat c0 p22)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfPat_pvar k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_ty H0 ins)))) (fun (k13 : Hvl) (p1 : Pat) (wf : (wfPat k13 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k13 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfPat_pprod k14 (IHp1 c0 k14 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHp2 (weakenCutoffty c0 (appendHvl H0 (bindPat p1))) (appendHvl k14 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p1)) ins)))))).
  Definition shift_wfTm : (forall (k13 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k13 s6)) ,
      (forall (c0 : (Cutoff tm)) (k14 : Hvl) ,
        (shifthvl_tm c0 k13 k14) -> (wfTm k14 (shiftTm c0 s6))))) := (ind_wfTm (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
    (forall (c0 : (Cutoff tm)) (k14 : Hvl) ,
      (shifthvl_tm c0 k13 k14) -> (wfTm k14 (shiftTm c0 s6)))) (fun (k13 : Hvl) (x11 : (Index tm)) (wfi : (wfindex k13 x11)) (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTm_var k14 _ (shift_wfindex_tm c0 k13 k14 ins x11 wfi))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS tm k13) t)) IHt (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTm_abs k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_tm H0 ins)) (IHt (CS c0) (HS tm k14) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTm_app k14 (IHt1 c0 k14 (weaken_shifthvl_tm H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_tm H0 ins)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS ty k13) t)) IHt (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTm_tabs k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_tm H0 ins)) (IHt c0 (HS ty k14) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm k13 t)) IHt (T : Ty) (wf0 : (wfTy k13 T)) (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTm_tapp k14 (IHt c0 k14 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k13 T wf0 c0 k14 (weaken_shifthvl_tm H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTm_prod k14 (IHt1 c0 k14 (weaken_shifthvl_tm H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_tm H0 ins)))) (fun (k13 : Hvl) (p : Pat) (wf : (wfPat k13 p)) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff tm)) (k14 : Hvl) (ins : (shifthvl_tm c0 k13 k14)) =>
    (wfTm_lett k14 (shift_wfPat k13 p wf c0 k14 (weaken_shifthvl_tm H0 ins)) (IHt1 c0 k14 (weaken_shifthvl_tm H0 ins)) (IHt2 (weakenCutofftm c0 (appendHvl H0 (bindPat p))) (appendHvl k14 (appendHvl H0 (bindPat p))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p)) ins))))).
  Definition tshift_wfTm : (forall (k13 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k13 s6)) ,
      (forall (c0 : (Cutoff ty)) (k14 : Hvl) ,
        (shifthvl_ty c0 k13 k14) -> (wfTm k14 (tshiftTm c0 s6))))) := (ind_wfTm (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
    (forall (c0 : (Cutoff ty)) (k14 : Hvl) ,
      (shifthvl_ty c0 k13 k14) -> (wfTm k14 (tshiftTm c0 s6)))) (fun (k13 : Hvl) (x11 : (Index tm)) (wfi : (wfindex k13 x11)) (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTm_var k14 _ (tshift_wfindex_tm c0 k13 k14 ins x11 wfi))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS tm k13) t)) IHt (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTm_abs k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_ty H0 ins)) (IHt c0 (HS tm k14) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTm_app k14 (IHt1 c0 k14 (weaken_shifthvl_ty H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_ty H0 ins)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS ty k13) t)) IHt (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTm_tabs k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_ty H0 ins)) (IHt (CS c0) (HS ty k14) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm k13 t)) IHt (T : Ty) (wf0 : (wfTy k13 T)) (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTm_tapp k14 (IHt c0 k14 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k13 T wf0 c0 k14 (weaken_shifthvl_ty H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTm_prod k14 (IHt1 c0 k14 (weaken_shifthvl_ty H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_ty H0 ins)))) (fun (k13 : Hvl) (p : Pat) (wf : (wfPat k13 p)) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff ty)) (k14 : Hvl) (ins : (shifthvl_ty c0 k13 k14)) =>
    (wfTm_lett k14 (tshift_wfPat k13 p wf c0 k14 (weaken_shifthvl_ty H0 ins)) (IHt1 c0 k14 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHt2 (weakenCutoffty c0 (appendHvl H0 (bindPat p))) (appendHvl k14 (appendHvl H0 (bindPat p))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p)) ins)))))).
  Fixpoint weaken_wfTy (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (S19 : Ty) (wf : (wfTy k14 S19)) ,
    (wfTy (appendHvl k14 k13) (weakenTy S19 k13))) :=
    match k13 return (forall (k14 : Hvl) (S19 : Ty) (wf : (wfTy k14 S19)) ,
      (wfTy (appendHvl k14 k13) (weakenTy S19 k13))) with
      | (H0) => (fun (k14 : Hvl) (S19 : Ty) (wf : (wfTy k14 S19)) =>
        wf)
      | (HS tm k13) => (fun (k14 : Hvl) (S19 : Ty) (wf : (wfTy k14 S19)) =>
        (shift_wfTy (appendHvl k14 k13) (weakenTy S19 k13) (weaken_wfTy k13 k14 S19 wf) C0 (HS tm (appendHvl k14 k13)) (shifthvl_tm_here (appendHvl k14 k13))))
      | (HS ty k13) => (fun (k14 : Hvl) (S19 : Ty) (wf : (wfTy k14 S19)) =>
        (tshift_wfTy (appendHvl k14 k13) (weakenTy S19 k13) (weaken_wfTy k13 k14 S19 wf) C0 (HS ty (appendHvl k14 k13)) (shifthvl_ty_here (appendHvl k14 k13))))
    end.
  Fixpoint weaken_wfPat (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (p22 : Pat) (wf : (wfPat k14 p22)) ,
    (wfPat (appendHvl k14 k13) (weakenPat p22 k13))) :=
    match k13 return (forall (k14 : Hvl) (p22 : Pat) (wf : (wfPat k14 p22)) ,
      (wfPat (appendHvl k14 k13) (weakenPat p22 k13))) with
      | (H0) => (fun (k14 : Hvl) (p22 : Pat) (wf : (wfPat k14 p22)) =>
        wf)
      | (HS tm k13) => (fun (k14 : Hvl) (p22 : Pat) (wf : (wfPat k14 p22)) =>
        (shift_wfPat (appendHvl k14 k13) (weakenPat p22 k13) (weaken_wfPat k13 k14 p22 wf) C0 (HS tm (appendHvl k14 k13)) (shifthvl_tm_here (appendHvl k14 k13))))
      | (HS ty k13) => (fun (k14 : Hvl) (p22 : Pat) (wf : (wfPat k14 p22)) =>
        (tshift_wfPat (appendHvl k14 k13) (weakenPat p22 k13) (weaken_wfPat k13 k14 p22 wf) C0 (HS ty (appendHvl k14 k13)) (shifthvl_ty_here (appendHvl k14 k13))))
    end.
  Fixpoint weaken_wfTm (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) ,
    (wfTm (appendHvl k14 k13) (weakenTm s6 k13))) :=
    match k13 return (forall (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) ,
      (wfTm (appendHvl k14 k13) (weakenTm s6 k13))) with
      | (H0) => (fun (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) =>
        wf)
      | (HS tm k13) => (fun (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) =>
        (shift_wfTm (appendHvl k14 k13) (weakenTm s6 k13) (weaken_wfTm k13 k14 s6 wf) C0 (HS tm (appendHvl k14 k13)) (shifthvl_tm_here (appendHvl k14 k13))))
      | (HS ty k13) => (fun (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) =>
        (tshift_wfTm (appendHvl k14 k13) (weakenTm s6 k13) (weaken_wfTm k13 k14 s6 wf) C0 (HS ty (appendHvl k14 k13)) (shifthvl_ty_here (appendHvl k14 k13))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k17 : Hvl) (S20 : Ty) (k18 : Hvl) (S21 : Ty) ,
    (k17 = k18) -> (S20 = S21) -> (wfTy k17 S20) -> (wfTy k18 S21)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k17 : Hvl) (p23 : Pat) (k18 : Hvl) (p24 : Pat) ,
    (k17 = k18) -> (p23 = p24) -> (wfPat k17 p23) -> (wfPat k18 p24)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k17 : Hvl) (s6 : Tm) (k18 : Hvl) (s7 : Tm) ,
    (k17 = k18) -> (s6 = s7) -> (wfTm k17 s6) -> (wfTm k18 s7)).
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
  Inductive substhvl_tm (k13 : Hvl) : (forall (d0 : (Trace tm)) (k14 : Hvl) (k15 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k13 X0 (HS tm k13) k13)
    | substhvl_tm_there_tm
        {d0 : (Trace tm)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_tm k13 d0 k14 k15) -> (substhvl_tm k13 (XS tm d0) (HS tm k14) (HS tm k15))
    | substhvl_tm_there_ty
        {d0 : (Trace tm)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_tm k13 d0 k14 k15) -> (substhvl_tm k13 (XS ty d0) (HS ty k14) (HS ty k15)).
  Inductive substhvl_ty (k13 : Hvl) : (forall (d0 : (Trace ty)) (k14 : Hvl) (k15 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k13 X0 (HS ty k13) k13)
    | substhvl_ty_there_tm
        {d0 : (Trace ty)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_ty k13 d0 k14 k15) -> (substhvl_ty k13 (XS tm d0) (HS tm k14) (HS tm k15))
    | substhvl_ty_there_ty
        {d0 : (Trace ty)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_ty k13 d0 k14 k15) -> (substhvl_ty k13 (XS ty d0) (HS ty k14) (HS ty k15)).
  Lemma weaken_substhvl_tm  :
    (forall {k14 : Hvl} (k13 : Hvl) {d0 : (Trace tm)} {k15 : Hvl} {k16 : Hvl} ,
      (substhvl_tm k14 d0 k15 k16) -> (substhvl_tm k14 (weakenTrace d0 k13) (appendHvl k15 k13) (appendHvl k16 k13))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k14 : Hvl} (k13 : Hvl) {d0 : (Trace ty)} {k15 : Hvl} {k16 : Hvl} ,
      (substhvl_ty k14 d0 k15 k16) -> (substhvl_ty k14 (weakenTrace d0 k13) (appendHvl k15 k13) (appendHvl k16 k13))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k17 : Hvl} {s6 : Tm} (wft : (wfTm k17 s6)) :
    (forall {d0 : (Trace tm)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_tm k17 d0 k18 k19) -> (forall {x11 : (Index tm)} ,
        (wfindex k18 x11) -> (wfTm k19 (substIndex d0 s6 x11)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k17 : Hvl} {S20 : Ty} (wft : (wfTy k17 S20)) :
    (forall {d0 : (Trace ty)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_ty k17 d0 k18 k19) -> (forall {X19 : (Index ty)} ,
        (wfindex k18 X19) -> (wfTy k19 (tsubstIndex d0 S20 X19)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k17 : Hvl} :
    (forall {d0 : (Trace tm)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_tm k17 d0 k18 k19) -> (forall {X19 : (Index ty)} ,
        (wfindex k18 X19) -> (wfindex k19 X19))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k17 : Hvl} :
    (forall {d0 : (Trace ty)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_ty k17 d0 k18 k19) -> (forall {x11 : (Index tm)} ,
        (wfindex k18 x11) -> (wfindex k19 x11))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k17 : Hvl} : (forall (k18 : Hvl) ,
    (forall (S20 : Ty) (wf0 : (wfTy k18 S20)) ,
      (forall {d0 : (Trace tm)} {k19 : Hvl} ,
        (substhvl_tm k17 d0 k18 k19) -> (wfTy k19 S20)))) := (ind_wfTy (fun (k18 : Hvl) (S20 : Ty) (wf0 : (wfTy k18 S20)) =>
    (forall {d0 : (Trace tm)} {k19 : Hvl} ,
      (substhvl_tm k17 d0 k18 k19) -> (wfTy k19 S20))) (fun (k18 : Hvl) {X19 : (Index ty)} (wfi : (wfindex k18 X19)) {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTy_tvar k19 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k18 : Hvl) {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTy_top k19)) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTy_tarr k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS ty k18) T2)) IHT2 {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTy_tall k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d0 (HS ty H0)) (HS ty k19) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTy_tprod k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTy {k17 : Hvl} {S20 : Ty} (wf : (wfTy k17 S20)) : (forall (k18 : Hvl) ,
    (forall (S21 : Ty) (wf0 : (wfTy k18 S21)) ,
      (forall {d0 : (Trace ty)} {k19 : Hvl} ,
        (substhvl_ty k17 d0 k18 k19) -> (wfTy k19 (tsubstTy d0 S20 S21))))) := (ind_wfTy (fun (k18 : Hvl) (S21 : Ty) (wf0 : (wfTy k18 S21)) =>
    (forall {d0 : (Trace ty)} {k19 : Hvl} ,
      (substhvl_ty k17 d0 k18 k19) -> (wfTy k19 (tsubstTy d0 S20 S21)))) (fun (k18 : Hvl) {X19 : (Index ty)} (wfi : (wfindex k18 X19)) {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k18 : Hvl) {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTy_top k19)) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTy_tarr k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS ty k18) T2)) IHT2 {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTy_tall k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d0 (HS ty H0)) (HS ty k19) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTy_tprod k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del))))).
  Definition substhvl_tm_wfPat {k17 : Hvl} : (forall (k18 : Hvl) ,
    (forall (p23 : Pat) (wf0 : (wfPat k18 p23)) ,
      (forall {d0 : (Trace tm)} {k19 : Hvl} ,
        (substhvl_tm k17 d0 k18 k19) -> (wfPat k19 p23)))) := (ind_wfPat (fun (k18 : Hvl) (p23 : Pat) (wf0 : (wfPat k18 p23)) =>
    (forall {d0 : (Trace tm)} {k19 : Hvl} ,
      (substhvl_tm k17 d0 k18 k19) -> (wfPat k19 p23))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfPat_pvar k19 (substhvl_tm_wfTy k18 T wf0 (weaken_substhvl_tm H0 del)))) (fun (k18 : Hvl) (p1 : Pat) (wf0 : (wfPat k18 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k18 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfPat_pprod k19 (IHp1 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k19 (appendHvl H0 (bindPat p1))) (weaken_substhvl_tm (appendHvl H0 (bindPat p1)) del))))).
  Definition substhvl_ty_wfPat {k17 : Hvl} {S20 : Ty} (wf : (wfTy k17 S20)) : (forall (k18 : Hvl) ,
    (forall (p23 : Pat) (wf0 : (wfPat k18 p23)) ,
      (forall {d0 : (Trace ty)} {k19 : Hvl} ,
        (substhvl_ty k17 d0 k18 k19) -> (wfPat k19 (tsubstPat d0 S20 p23))))) := (ind_wfPat (fun (k18 : Hvl) (p23 : Pat) (wf0 : (wfPat k18 p23)) =>
    (forall {d0 : (Trace ty)} {k19 : Hvl} ,
      (substhvl_ty k17 d0 k18 k19) -> (wfPat k19 (tsubstPat d0 S20 p23)))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfPat_pvar k19 (substhvl_ty_wfTy wf k18 T wf0 (weaken_substhvl_ty H0 del)))) (fun (k18 : Hvl) (p1 : Pat) (wf0 : (wfPat k18 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k18 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfPat_pprod k19 (IHp1 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k19) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k19 (appendHvl H0 (bindPat p1))) (weaken_substhvl_ty (appendHvl H0 (bindPat p1)) del)))))).
  Definition substhvl_tm_wfTm {k17 : Hvl} {s6 : Tm} (wf : (wfTm k17 s6)) : (forall (k18 : Hvl) ,
    (forall (s7 : Tm) (wf0 : (wfTm k18 s7)) ,
      (forall {d0 : (Trace tm)} {k19 : Hvl} ,
        (substhvl_tm k17 d0 k18 k19) -> (wfTm k19 (substTm d0 s6 s7))))) := (ind_wfTm (fun (k18 : Hvl) (s7 : Tm) (wf0 : (wfTm k18 s7)) =>
    (forall {d0 : (Trace tm)} {k19 : Hvl} ,
      (substhvl_tm k17 d0 k18 k19) -> (wfTm k19 (substTm d0 s6 s7)))) (fun (k18 : Hvl) {x11 : (Index tm)} (wfi : (wfindex k18 x11)) {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS tm k18) t)) IHt {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTm_abs k19 (substhvl_tm_wfTy k18 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d0 (HS tm H0)) (HS tm k19) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTm_app k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS ty k18) t)) IHt {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTm_tabs k19 (substhvl_tm_wfTy k18 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d0 (HS ty H0)) (HS ty k19) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k18 : Hvl) (t : Tm) (wf0 : (wfTm k18 t)) IHt (T : Ty) (wf1 : (wfTy k18 T)) {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTm_tapp k19 (IHt (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k18 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTm_prod k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)))) (fun (k18 : Hvl) (p : Pat) (wf0 : (wfPat k18 p)) (t1 : Tm) (wf1 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k18 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace tm)} {k19 : Hvl} (del : (substhvl_tm k17 d0 k18 k19)) =>
    (wfTm_lett k19 (substhvl_tm_wfPat k18 p wf0 (weaken_substhvl_tm H0 del)) (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k19 (appendHvl H0 (bindPat p))) (weaken_substhvl_tm (appendHvl H0 (bindPat p)) del))))).
  Definition substhvl_ty_wfTm {k17 : Hvl} {S20 : Ty} (wf : (wfTy k17 S20)) : (forall (k18 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k18 s6)) ,
      (forall {d0 : (Trace ty)} {k19 : Hvl} ,
        (substhvl_ty k17 d0 k18 k19) -> (wfTm k19 (tsubstTm d0 S20 s6))))) := (ind_wfTm (fun (k18 : Hvl) (s6 : Tm) (wf0 : (wfTm k18 s6)) =>
    (forall {d0 : (Trace ty)} {k19 : Hvl} ,
      (substhvl_ty k17 d0 k18 k19) -> (wfTm k19 (tsubstTm d0 S20 s6)))) (fun (k18 : Hvl) {x11 : (Index tm)} (wfi : (wfindex k18 x11)) {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTm_var k19 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS tm k18) t)) IHt {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTm_abs k19 (substhvl_ty_wfTy wf k18 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d0 (HS tm H0)) (HS tm k19) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTm_app k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS ty k18) t)) IHt {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTm_tabs k19 (substhvl_ty_wfTy wf k18 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d0 (HS ty H0)) (HS ty k19) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k18 : Hvl) (t : Tm) (wf0 : (wfTm k18 t)) IHt (T : Ty) (wf1 : (wfTy k18 T)) {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTm_tapp k19 (IHt (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k18 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTm_prod k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)))) (fun (k18 : Hvl) (p : Pat) (wf0 : (wfPat k18 p)) (t1 : Tm) (wf1 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k18 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace ty)} {k19 : Hvl} (del : (substhvl_ty k17 d0 k18 k19)) =>
    (wfTm_lett k19 (substhvl_ty_wfPat wf k18 p wf0 (weaken_substhvl_ty H0 del)) (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k19) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k19 (appendHvl H0 (bindPat p))) (weaken_substhvl_ty (appendHvl H0 (bindPat p)) del)))))).
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
Fixpoint subhvl_tm (k17 : Hvl) {struct k17} :
Prop :=
  match k17 with
    | (H0) => True
    | (HS a k17) => match a with
      | (tm) => (subhvl_tm k17)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k17 : Hvl) (k18 : Hvl) ,
    (subhvl_tm k17) -> (subhvl_tm k18) -> (subhvl_tm (appendHvl k17 k18))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k14 : Hvl) (k13 : Hvl) (p22 : Pat) ,
    (subhvl_tm k14) -> (wfPat (appendHvl k13 k14) (weakenPat p22 k14)) -> (wfPat k13 p22)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k16 : Hvl) (k15 : Hvl) (S19 : Ty) ,
    (subhvl_tm k16) -> (wfTy (appendHvl k15 k16) (weakenTy S19 k16)) -> (wfTy k15 S19)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H47 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_tm) in H47
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H48 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H48
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G2 : Env) (T : Ty)
    | etvar (G2 : Env) (T : Ty).
  Fixpoint appendEnv (G2 : Env) (G3 : Env) :
  Env :=
    match G3 with
      | (empty) => G2
      | (evar G4 T) => (evar (appendEnv G2 G4) T)
      | (etvar G4 T) => (etvar (appendEnv G2 G4) T)
    end.
  Fixpoint domainEnv (G2 : Env) :
  Hvl :=
    match G2 with
      | (empty) => H0
      | (evar G3 T) => (HS tm (domainEnv G3))
      | (etvar G3 T) => (HS ty (domainEnv G3))
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
      | (etvar G3 T) => (etvar (shiftEnv c0 G3) T)
    end.
  Fixpoint tshiftEnv (c0 : (Cutoff ty)) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (tshiftEnv c0 G3) (tshiftTy (weakenCutoffty c0 (domainEnv G3)) T))
      | (etvar G3 T) => (etvar (tshiftEnv c0 G3) (tshiftTy (weakenCutoffty c0 (domainEnv G3)) T))
    end.
  Fixpoint weakenEnv (G2 : Env) (k17 : Hvl) {struct k17} :
  Env :=
    match k17 with
      | (H0) => G2
      | (HS tm k17) => (weakenEnv G2 k17)
      | (HS ty k17) => (tshiftEnv C0 (weakenEnv G2 k17))
    end.
  Fixpoint substEnv (d0 : (Trace tm)) (s6 : Tm) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (substEnv d0 s6 G3) T)
      | (etvar G3 T) => (etvar (substEnv d0 s6 G3) T)
    end.
  Fixpoint tsubstEnv (d0 : (Trace ty)) (S20 : Ty) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (tsubstEnv d0 S20 G3) (tsubstTy (weakenTrace d0 (domainEnv G3)) S20 T))
      | (etvar G3 T) => (etvar (tsubstEnv d0 S20 G3) (tsubstTy (weakenTrace d0 (domainEnv G3)) S20 T))
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
    (forall (d0 : (Trace ty)) (S20 : Ty) (G2 : Env) ,
      ((domainEnv (tsubstEnv d0 S20 G2)) = (domainEnv G2))).
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
      (forall (d0 : (Trace ty)) (S20 : Ty) (G2 : Env) (G3 : Env) ,
        ((tsubstEnv d0 S20 (appendEnv G2 G3)) = (appendEnv (tsubstEnv d0 S20 G2) (tsubstEnv (weakenTrace d0 (domainEnv G2)) S20 G3)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S20 : Ty) (k17 : Hvl) (k18 : Hvl) ,
      ((weakenTy (weakenTy S20 k17) k18) = (weakenTy S20 (appendHvl k17 k18)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p23 : Pat) (k17 : Hvl) (k18 : Hvl) ,
      ((weakenPat (weakenPat p23 k17) k18) = (weakenPat p23 (appendHvl k17 k18)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s6 : Tm) (k17 : Hvl) (k18 : Hvl) ,
      ((weakenTm (weakenTm s6 k17) k18) = (weakenTm s6 (appendHvl k17 k18)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G2 : Env}
          (T73 : Ty) :
          (wfTy (domainEnv G2) T73) -> (lookup_evar (evar G2 T73) I0 T73)
      | lookup_evar_there_evar
          {G2 : Env} {x11 : (Index tm)}
          (T74 : Ty) (T75 : Ty) :
          (lookup_evar G2 x11 T74) -> (lookup_evar (evar G2 T75) (IS x11) T74)
      | lookup_evar_there_etvar
          {G2 : Env} {x11 : (Index tm)}
          (T74 : Ty) (T75 : Ty) :
          (lookup_evar G2 x11 T74) -> (lookup_evar (etvar G2 T75) x11 (tshiftTy C0 T74)).
    Inductive lookup_etvar : Env -> (Index ty) -> Ty -> Prop :=
      | lookup_etvar_here {G2 : Env}
          (T74 : Ty) :
          (wfTy (domainEnv G2) T74) -> (lookup_etvar (etvar G2 T74) I0 (tshiftTy C0 T74))
      | lookup_etvar_there_evar
          {G2 : Env} {X19 : (Index ty)}
          (T75 : Ty) (T76 : Ty) :
          (lookup_etvar G2 X19 T75) -> (lookup_etvar (evar G2 T76) X19 T75)
      | lookup_etvar_there_etvar
          {G2 : Env} {X19 : (Index ty)}
          (T75 : Ty) (T76 : Ty) :
          (lookup_etvar G2 X19 T75) -> (lookup_etvar (etvar G2 T76) (IS X19) (tshiftTy C0 T75)).
    Lemma lookup_evar_inversion_here  :
      (forall (G2 : Env) (T75 : Ty) (T76 : Ty) ,
        (lookup_evar (evar G2 T75) I0 T76) -> (T75 = T76)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G2 : Env) (T75 : Ty) (T76 : Ty) ,
        (lookup_etvar (etvar G2 T75) I0 T76) -> ((tshiftTy C0 T75) = T76)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G2 : Env} {x11 : (Index tm)} ,
        (forall (T75 : Ty) ,
          (lookup_evar G2 x11 T75) -> (forall (T76 : Ty) ,
            (lookup_evar G2 x11 T76) -> (T75 = T76)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G2 : Env} {X19 : (Index ty)} ,
        (forall (T75 : Ty) ,
          (lookup_etvar G2 X19 T75) -> (forall (T76 : Ty) ,
            (lookup_etvar G2 X19 T76) -> (T75 = T76)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G2 : Env} {x11 : (Index tm)} (T75 : Ty) ,
        (lookup_evar G2 x11 T75) -> (wfTy (domainEnv G2) T75)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G2 : Env} {X19 : (Index ty)} (T75 : Ty) ,
        (lookup_etvar G2 X19 T75) -> (wfTy (domainEnv G2) T75)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G2 : Env} (G3 : Env) {x11 : (Index tm)} (T75 : Ty) ,
        (lookup_evar G2 x11 T75) -> (lookup_evar (appendEnv G2 G3) (weakenIndextm x11 (domainEnv G3)) (weakenTy T75 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G2 : Env} (G3 : Env) {X19 : (Index ty)} (T75 : Ty) ,
        (lookup_etvar G2 X19 T75) -> (lookup_etvar (appendEnv G2 G3) (weakenIndexty X19 (domainEnv G3)) (weakenTy T75 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G2 : Env} {x11 : (Index tm)} (T79 : Ty) ,
        (lookup_evar G2 x11 T79) -> (wfindex (domainEnv G2) x11)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G2 : Env} {X19 : (Index ty)} (T79 : Ty) ,
        (lookup_etvar G2 X19 T79) -> (wfindex (domainEnv G2) X19)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G2 : Env}
        {T75 : Ty} :
        (shift_evar C0 G2 (evar G2 T75))
    | shiftevar_there_evar
        {c0 : (Cutoff tm)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_evar c0 G2 G3) -> (shift_evar (CS c0) (evar G2 T) (evar G3 T))
    | shiftevar_there_etvar
        {c0 : (Cutoff tm)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_evar c0 G2 G3) -> (shift_evar c0 (etvar G2 T) (etvar G3 T)).
  Lemma weaken_shift_evar  :
    (forall (G2 : Env) {c0 : (Cutoff tm)} {G3 : Env} {G4 : Env} ,
      (shift_evar c0 G3 G4) -> (shift_evar (weakenCutofftm c0 (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 G2))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G2 : Env}
        {T75 : Ty} :
        (shift_etvar C0 G2 (etvar G2 T75))
    | shiftetvar_there_evar
        {c0 : (Cutoff ty)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_etvar c0 G2 G3) -> (shift_etvar c0 (evar G2 T) (evar G3 (tshiftTy c0 T)))
    | shiftetvar_there_etvar
        {c0 : (Cutoff ty)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_etvar c0 G2 G3) -> (shift_etvar (CS c0) (etvar G2 T) (etvar G3 (tshiftTy c0 T))).
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
  Inductive subst_evar (G2 : Env) (T75 : Ty) (s6 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G2 T75 s6 X0 (evar G2 T75) G2)
    | subst_evar_there_evar
        {d0 : (Trace tm)} {G3 : Env}
        {G4 : Env} (T76 : Ty) :
        (subst_evar G2 T75 s6 d0 G3 G4) -> (subst_evar G2 T75 s6 (XS tm d0) (evar G3 T76) (evar G4 T76))
    | subst_evar_there_etvar
        {d0 : (Trace tm)} {G3 : Env}
        {G4 : Env} (T76 : Ty) :
        (subst_evar G2 T75 s6 d0 G3 G4) -> (subst_evar G2 T75 s6 (XS ty d0) (etvar G3 T76) (etvar G4 T76)).
  Lemma weaken_subst_evar {G2 : Env} (T75 : Ty) {s6 : Tm} :
    (forall (G3 : Env) {d0 : (Trace tm)} {G4 : Env} {G5 : Env} ,
      (subst_evar G2 T75 s6 d0 G4 G5) -> (subst_evar G2 T75 s6 (weakenTrace d0 (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 G3))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G2 : Env) (T75 : Ty) (S20 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G2 T75 S20 X0 (etvar G2 T75) G2)
    | subst_etvar_there_evar
        {d0 : (Trace ty)} {G3 : Env}
        {G4 : Env} (T76 : Ty) :
        (subst_etvar G2 T75 S20 d0 G3 G4) -> (subst_etvar G2 T75 S20 (XS tm d0) (evar G3 T76) (evar G4 (tsubstTy d0 S20 T76)))
    | subst_etvar_there_etvar
        {d0 : (Trace ty)} {G3 : Env}
        {G4 : Env} (T76 : Ty) :
        (subst_etvar G2 T75 S20 d0 G3 G4) -> (subst_etvar G2 T75 S20 (XS ty d0) (etvar G3 T76) (etvar G4 (tsubstTy d0 S20 T76))).
  Lemma weaken_subst_etvar {G2 : Env} (T75 : Ty) {S20 : Ty} :
    (forall (G3 : Env) {d0 : (Trace ty)} {G4 : Env} {G5 : Env} ,
      (subst_etvar G2 T75 S20 d0 G4 G5) -> (subst_etvar G2 T75 S20 (weakenTrace d0 (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 (tsubstEnv d0 S20 G3)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G2 : Env} {s6 : Tm} (T75 : Ty) :
    (forall {d0 : (Trace tm)} {G3 : Env} {G4 : Env} ,
      (subst_evar G2 T75 s6 d0 G3 G4) -> (substhvl_tm (domainEnv G2) d0 (domainEnv G3) (domainEnv G4))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G2 : Env} {S20 : Ty} (T76 : Ty) :
    (forall {d0 : (Trace ty)} {G3 : Env} {G4 : Env} ,
      (subst_etvar G2 T76 S20 d0 G3 G4) -> (substhvl_ty (domainEnv G2) d0 (domainEnv G3) (domainEnv G4))).
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
  (forall {G2 : Env} (G3 : Env) {T75 : Ty} (wf : (wfTy (domainEnv G2) T75)) ,
    (lookup_evar (appendEnv (evar G2 T75) G3) (weakenIndextm I0 (domainEnv G3)) (weakenTy T75 (domainEnv G3)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G2 : Env} (G3 : Env) {T75 : Ty} (wf : (wfTy (domainEnv G2) T75)) ,
    (lookup_etvar (appendEnv (etvar G2 T75) G3) (weakenIndexty I0 (domainEnv G3)) (weakenTy (tshiftTy C0 T75) (domainEnv G3)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H47 : (wfTy _ (tvar _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (top)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (tarr _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (tall _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (tprod _ _)) |- _ => inversion H47; subst; clear H47
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H47 : (wfPat _ (pvar _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfPat _ (pprod _ _)) |- _ => inversion H47; subst; clear H47
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H47 : (wfTm _ (var _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (abs _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (app _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (tabs _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (tapp _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (prod _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (lett _ _ _)) |- _ => inversion H47; subst; clear H47
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
  (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} (ins : (shift_evar c0 G2 G3)) {x11 : (Index tm)} {T75 : Ty} ,
    (lookup_evar G2 x11 T75) -> (lookup_evar G3 (shiftIndex c0 x11) T75)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} (ins : (shift_evar c0 G2 G3)) {X19 : (Index ty)} {T75 : Ty} ,
    (lookup_etvar G2 X19 T75) -> (lookup_etvar G3 X19 T75)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} (ins : (shift_etvar c0 G2 G3)) {x11 : (Index tm)} {T75 : Ty} ,
    (lookup_evar G2 x11 T75) -> (lookup_evar G3 x11 (tshiftTy c0 T75))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} (ins : (shift_etvar c0 G2 G3)) {X19 : (Index ty)} {T75 : Ty} ,
    (lookup_etvar G2 X19 T75) -> (lookup_etvar G3 (tshiftIndex c0 X19) (tshiftTy c0 T75))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G2 : Env} (T77 : Ty) {s6 : Tm} :
  (forall {d0 : (Trace tm)} {G3 : Env} {G4 : Env} (sub : (subst_evar G2 T77 s6 d0 G3 G4)) {X19 : (Index ty)} (T78 : Ty) ,
    (lookup_etvar G3 X19 T78) -> (lookup_etvar G4 X19 T78)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G2 : Env} (T77 : Ty) {S20 : Ty} (wf : (wfTy (domainEnv G2) S20)) :
  (forall {d0 : (Trace ty)} {G3 : Env} {G4 : Env} (sub : (subst_etvar G2 T77 S20 d0 G3 G4)) {x11 : (Index tm)} (T78 : Ty) ,
    (lookup_evar G3 x11 T78) -> (lookup_evar G4 x11 (tsubstTy d0 S20 T78))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S13 : Ty) {struct S13} :
nat :=
  match S13 with
    | (tvar X19) => 1
    | (top) => 1
    | (tarr T73 T74) => (plus 1 (plus (size_Ty T73) (size_Ty T74)))
    | (tall T75 T76) => (plus 1 (plus (size_Ty T75) (size_Ty T76)))
    | (tprod T77 T78) => (plus 1 (plus (size_Ty T77) (size_Ty T78)))
  end.
Fixpoint size_Pat (p18 : Pat) {struct p18} :
nat :=
  match p18 with
    | (pvar T73) => (plus 1 (size_Ty T73))
    | (pprod p19 p20) => (plus 1 (plus (size_Pat p19) (size_Pat p20)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x11) => 1
    | (abs T73 t29) => (plus 1 (plus (size_Ty T73) (size_Tm t29)))
    | (app t30 t31) => (plus 1 (plus (size_Tm t30) (size_Tm t31)))
    | (tabs T74 t32) => (plus 1 (plus (size_Ty T74) (size_Tm t32)))
    | (tapp t33 T75) => (plus 1 (plus (size_Tm t33) (size_Ty T75)))
    | (prod t34 t35) => (plus 1 (plus (size_Tm t34) (size_Tm t35)))
    | (lett p18 t36 t37) => (plus 1 (plus (size_Pat p18) (plus (size_Tm t36) (size_Tm t37))))
  end.
Fixpoint tshift_size_Ty (S14 : Ty) (c0 : (Cutoff ty)) {struct S14} :
((size_Ty (tshiftTy c0 S14)) = (size_Ty S14)) :=
  match S14 return ((size_Ty (tshiftTy c0 S14)) = (size_Ty S14)) with
    | (tvar _) => eq_refl
    | (top) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
    | (tall T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 (CS c0))))
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
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t c0)))
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
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c0) (tshift_size_Tm t (CS c0))))
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
  (forall (k : Hvl) (S14 : Ty) ,
    ((size_Ty (weakenTy S14 k)) = (size_Ty S14))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive Sub (G2 : Env) : Ty -> Ty -> Prop :=
  | SA_Top (S1 : Ty)
      (H29 : (wfTy (domainEnv G2) S1))
      : (Sub G2 S1 (top))
  | SA_Refl_TVar (X : (Index ty))
      (H30 : (wfindex (domainEnv G2) X))
      : (Sub G2 (tvar X) (tvar X))
  | SA_Trans_TVar (T : Ty)
      (U : Ty) (X : (Index ty))
      (lk : (lookup_etvar G2 X U))
      (jm : (Sub G2 U T))
      (H33 : (wfindex (domainEnv G2) X))
      : (Sub G2 (tvar X) T)
  | SA_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm0 : (Sub G2 T1 S1))
      (jm1 : (Sub G2 S2 T2)) :
      (Sub G2 (tarr S1 S2) (tarr T1 T2))
  | SA_All (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm2 : (Sub G2 T1 S1))
      (jm3 : (Sub (etvar G2 T1) S2 T2))
      :
      (Sub G2 (tall S1 S2) (tall T1 T2))
  | SA_Prod (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm4 : (Sub G2 S1 T1))
      (jm5 : (Sub G2 S2 T2)) :
      (Sub G2 (tprod S1 S2) (tprod T1 T2)).
Inductive PTyping (G2 : Env) : Pat -> Ty -> Env -> Prop :=
  | P_Var (T : Ty)
      (H29 : (wfTy (domainEnv G2) T))
      :
      (PTyping G2 (pvar T) T (evar empty T))
  | P_Prod (T1 : Ty) (T2 : Ty)
      (p1 : Pat) (p2 : Pat) (G : Env)
      (G0 : Env)
      (wtp1 : (PTyping G2 p1 T1 G))
      (wtp2 : (PTyping (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0))
      (H31 : (wfTy (domainEnv G2) T2))
      :
      (PTyping G2 (pprod p1 p2) (tprod T1 T2) (appendEnv (appendEnv empty G) G0)).
Inductive Typing (G2 : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (y : (Index tm))
      (lk : (lookup_evar G2 y T))
      (H29 : (wfTy (domainEnv G2) T))
      (H30 : (wfindex (domainEnv G2) y))
      : (Typing G2 (var y) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm6 : (Typing (evar G2 T1) t (weakenTy T2 (HS tm H0))))
      (H31 : (wfTy (domainEnv G2) T1))
      (H32 : (wfTy (domainEnv G2) T2))
      :
      (Typing G2 (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm7 : (Typing G2 t1 (tarr T11 T12)))
      (jm8 : (Typing G2 t2 T11)) :
      (Typing G2 (app t1 t2) T12)
  | T_Tabs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm9 : (Typing (etvar G2 T1) t T2))
      (H38 : (wfTy (domainEnv G2) T1))
      :
      (Typing G2 (tabs T1 t) (tall T1 T2))
  | T_Tapp (T11 : Ty) (T12 : Ty)
      (T2 : Ty) (t1 : Tm)
      (jm10 : (Typing G2 t1 (tall T11 T12)))
      (jm11 : (Sub G2 T2 T11)) :
      (Typing G2 (tapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Prod (T1 : Ty) (T2 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm12 : (Typing G2 t1 T1))
      (jm13 : (Typing G2 t2 T2)) :
      (Typing G2 (prod t1 t2) (tprod T1 T2))
  | T_Let (T1 : Ty) (T2 : Ty)
      (p : Pat) (t1 : Tm) (t2 : Tm)
      (G1 : Env)
      (jm14 : (Typing G2 t1 T1))
      (wtp : (PTyping G2 p T1 G1))
      (jm15 : (Typing (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p)))))
      (H50 : (wfTy (domainEnv G2) T2))
      : (Typing G2 (lett p t1 t2) T2)
  | T_Sub (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm16 : (Typing G2 t T1))
      (jm17 : (Sub G2 T1 T2)) :
      (Typing G2 t T2).
Fixpoint domain_PTyping_bindPat (G4 : Env) (p25 : Pat) (T82 : Ty) (G5 : Env) (wtp8 : (PTyping G4 p25 T82 G5)) :
((domainEnv G5) = (bindPat p25)) :=
  match wtp8 in (PTyping _ p25 T82 G5) return ((domainEnv G5) = (bindPat p25)) with
    | (P_Var T79 H49) => (eq_refl (HS tm H0))
    | (P_Prod T80 T81 p23 p24 G2 G3 wtp6 wtp7 H51) => (eq_trans (domainEnv_appendEnv (appendEnv empty G2) G3) (f_equal2 appendHvl (eq_trans (domainEnv_appendEnv empty G2) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G4 p23 T80 G2 wtp6))) (domain_PTyping_bindPat (appendEnv G4 (appendEnv empty G2)) p24 (weakenTy T81 (appendHvl H0 (bindPat p23))) G3 wtp7)))
  end.
Lemma Sub_cast  :
  (forall (G2 : Env) (T79 : Ty) (T80 : Ty) (G3 : Env) (T81 : Ty) (T82 : Ty) ,
    (G2 = G3) -> (T79 = T81) -> (T80 = T82) -> (Sub G2 T79 T80) -> (Sub G3 T81 T82)).
Proof.
  congruence .
Qed.
Lemma PTyping_cast  :
  (forall (G2 : Env) (p23 : Pat) (T79 : Ty) (G4 : Env) (G3 : Env) (p24 : Pat) (T80 : Ty) (G5 : Env) ,
    (G2 = G3) -> (p23 = p24) -> (T79 = T80) -> (G4 = G5) -> (PTyping G2 p23 T79 G4) -> (PTyping G3 p24 T80 G5)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G2 : Env) (t29 : Tm) (T79 : Ty) (G3 : Env) (t30 : Tm) (T80 : Ty) ,
    (G2 = G3) -> (t29 = t30) -> (T79 = T80) -> (Typing G2 t29 T79) -> (Typing G3 t30 T80)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_Sub (G9 : Env) (T92 : Ty) (T93 : Ty) (jm27 : (Sub G9 T92 T93)) :
(forall (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) ,
  (Sub G10 T92 T93)) :=
  match jm27 in (Sub _ T92 T93) return (forall (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) ,
    (Sub G10 T92 T93)) with
    | (SA_Top S20 H61) => (fun (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) =>
      (SA_Top G10 S20 (shift_wfTy _ _ H61 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80)))))
    | (SA_Refl_TVar X22 H62) => (fun (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) =>
      (SA_Refl_TVar G10 X22 (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80)) _ H62)))
    | (SA_Trans_TVar T89 U1 X22 lk0 jm20 H65) => (fun (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) =>
      (SA_Trans_TVar G10 T89 U1 X22 (shift_evar_lookup_etvar H80 lk0) (shift_evar_Sub G9 U1 T89 jm20 c0 G10 (weaken_shift_evar empty H80)) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H80)) _ H65)))
    | (SA_Arrow S20 S21 T90 T91 jm21 jm22) => (fun (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) =>
      (SA_Arrow G10 S20 S21 T90 T91 (shift_evar_Sub G9 T90 S20 jm21 c0 G10 (weaken_shift_evar empty H80)) (shift_evar_Sub G9 S21 T91 jm22 c0 G10 (weaken_shift_evar empty H80))))
    | (SA_All S20 S21 T90 T91 jm23 jm24) => (fun (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) =>
      (SA_All G10 S20 S21 T90 T91 (shift_evar_Sub G9 T90 S20 jm23 c0 G10 (weaken_shift_evar empty H80)) (shift_evar_Sub (etvar G9 T90) S21 T91 jm24 c0 (etvar G10 T90) (weaken_shift_evar (etvar empty T90) H80))))
    | (SA_Prod S20 S21 T90 T91 jm25 jm26) => (fun (c0 : (Cutoff tm)) (G10 : Env) (H80 : (shift_evar c0 G9 G10)) =>
      (SA_Prod G10 S20 S21 T90 T91 (shift_evar_Sub G9 S20 T90 jm25 c0 G10 (weaken_shift_evar empty H80)) (shift_evar_Sub G9 S21 T91 jm26 c0 G10 (weaken_shift_evar empty H80))))
  end.
Fixpoint shift_etvar_Sub (G9 : Env) (T92 : Ty) (T93 : Ty) (jm27 : (Sub G9 T92 T93)) :
(forall (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) ,
  (Sub G10 (tshiftTy c0 T92) (tshiftTy c0 T93))) :=
  match jm27 in (Sub _ T92 T93) return (forall (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) ,
    (Sub G10 (tshiftTy c0 T92) (tshiftTy c0 T93))) with
    | (SA_Top S20 H61) => (fun (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) =>
      (SA_Top G10 (tshiftTy c0 S20) (tshift_wfTy _ _ H61 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80)))))
    | (SA_Refl_TVar X22 H62) => (fun (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) =>
      (SA_Refl_TVar G10 (tshiftIndex c0 X22) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80)) _ H62)))
    | (SA_Trans_TVar T89 U1 X22 lk0 jm20 H65) => (fun (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) =>
      (SA_Trans_TVar G10 (tshiftTy c0 T89) (tshiftTy c0 U1) (tshiftIndex c0 X22) (shift_etvar_lookup_etvar H80 lk0) (shift_etvar_Sub G9 U1 T89 jm20 c0 G10 (weaken_shift_etvar empty H80)) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H80)) _ H65)))
    | (SA_Arrow S20 S21 T90 T91 jm21 jm22) => (fun (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) =>
      (SA_Arrow G10 (tshiftTy c0 S20) (tshiftTy c0 S21) (tshiftTy c0 T90) (tshiftTy c0 T91) (shift_etvar_Sub G9 T90 S20 jm21 c0 G10 (weaken_shift_etvar empty H80)) (shift_etvar_Sub G9 S21 T91 jm22 c0 G10 (weaken_shift_etvar empty H80))))
    | (SA_All S20 S21 T90 T91 jm23 jm24) => (fun (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) =>
      (SA_All G10 (tshiftTy c0 S20) (tshiftTy (CS c0) S21) (tshiftTy c0 T90) (tshiftTy (CS c0) T91) (shift_etvar_Sub G9 T90 S20 jm23 c0 G10 (weaken_shift_etvar empty H80)) (shift_etvar_Sub (etvar G9 T90) S21 T91 jm24 (CS c0) (etvar G10 (tshiftTy c0 T90)) (weaken_shift_etvar (etvar empty T90) H80))))
    | (SA_Prod S20 S21 T90 T91 jm25 jm26) => (fun (c0 : (Cutoff ty)) (G10 : Env) (H80 : (shift_etvar c0 G9 G10)) =>
      (SA_Prod G10 (tshiftTy c0 S20) (tshiftTy c0 S21) (tshiftTy c0 T90) (tshiftTy c0 T91) (shift_etvar_Sub G9 S20 T90 jm25 c0 G10 (weaken_shift_etvar empty H80)) (shift_etvar_Sub G9 S21 T91 jm26 c0 G10 (weaken_shift_etvar empty H80))))
  end.
Fixpoint shift_evar_PTyping (G11 : Env) (p26 : Pat) (T92 : Ty) (G12 : Env) (wtp9 : (PTyping G11 p26 T92 G12)) :
(forall (c0 : (Cutoff tm)) (G13 : Env) (H68 : (shift_evar c0 G11 G13)) ,
  (PTyping G13 p26 T92 G12)) :=
  match wtp9 in (PTyping _ p26 T92 G12) return (forall (c0 : (Cutoff tm)) (G13 : Env) (H68 : (shift_evar c0 G11 G13)) ,
    (PTyping G13 p26 T92 G12)) with
    | (P_Var T89 H61) => (fun (c0 : (Cutoff tm)) (G13 : Env) (H68 : (shift_evar c0 G11 G13)) =>
      (P_Var G13 T89 (shift_wfTy _ _ H61 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H68)))))
    | (P_Prod T90 T91 p24 p25 G9 G10 wtp7 wtp8 H63) => (fun (c0 : (Cutoff tm)) (G13 : Env) (H68 : (shift_evar c0 G11 G13)) =>
      (PTyping_cast G13 _ _ _ G13 (pprod p24 p25) (tprod T90 T91) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G13 T90 T91 p24 p25 G9 G10 (shift_evar_PTyping G11 p24 T90 G9 wtp7 c0 G13 (weaken_shift_evar empty H68)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (shift_evar_PTyping (appendEnv G11 (appendEnv empty G9)) p25 (weakenTy T91 (appendHvl H0 (bindPat p24))) G10 wtp8 (weakenCutofftm c0 (domainEnv (appendEnv empty G9))) (appendEnv G13 (appendEnv empty G9)) (weaken_shift_evar (appendEnv empty G9) H68))) (shift_wfTy _ _ H63 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H68))))))
  end.
Fixpoint shift_etvar_PTyping (G11 : Env) (p26 : Pat) (T92 : Ty) (G12 : Env) (wtp9 : (PTyping G11 p26 T92 G12)) :
(forall (c0 : (Cutoff ty)) (G13 : Env) (H68 : (shift_etvar c0 G11 G13)) ,
  (PTyping G13 (tshiftPat c0 p26) (tshiftTy c0 T92) (tshiftEnv c0 G12))) :=
  match wtp9 in (PTyping _ p26 T92 G12) return (forall (c0 : (Cutoff ty)) (G13 : Env) (H68 : (shift_etvar c0 G11 G13)) ,
    (PTyping G13 (tshiftPat c0 p26) (tshiftTy c0 T92) (tshiftEnv c0 G12))) with
    | (P_Var T89 H61) => (fun (c0 : (Cutoff ty)) (G13 : Env) (H68 : (shift_etvar c0 G11 G13)) =>
      (P_Var G13 (tshiftTy c0 T89) (tshift_wfTy _ _ H61 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H68)))))
    | (P_Prod T90 T91 p24 p25 G9 G10 wtp7 wtp8 H63) => (fun (c0 : (Cutoff ty)) (G13 : Env) (H68 : (shift_etvar c0 G11 G13)) =>
      (PTyping_cast G13 _ _ _ G13 (tshiftPat c0 (pprod p24 p25)) (tshiftTy c0 (tprod T90 T91)) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym (tshiftEnv_appendEnv c0 empty G9)) eq_refl) (eq_sym (tshiftEnv_appendEnv c0 (appendEnv empty G9) G10))) (P_Prod G13 (tshiftTy c0 T90) (tshiftTy c0 T91) (tshiftPat c0 p24) (tshiftPat (weakenCutoffty c0 (appendHvl H0 (bindPat p24))) p25) (tshiftEnv c0 G9) (tshiftEnv (weakenCutoffty c0 (domainEnv (appendEnv empty G9))) G10) (shift_etvar_PTyping G11 p24 T90 G9 wtp7 c0 G13 (weaken_shift_etvar empty H68)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tshiftEnv_appendEnv c0 empty G9)) (f_equal2 tshiftPat (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G11 p24 T90 G9 wtp7)))) eq_refl) (eq_trans (f_equal2 tshiftTy (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G11 p24 T90 G9 wtp7)))) eq_refl) (eq_trans (eq_sym (weakenTy_tshiftTy (appendHvl H0 (bindPat p24)) c0 T91)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))))) eq_refl (shift_etvar_PTyping (appendEnv G11 (appendEnv empty G9)) p25 (weakenTy T91 (appendHvl H0 (bindPat p24))) G10 wtp8 (weakenCutoffty c0 (domainEnv (appendEnv empty G9))) (appendEnv G13 (tshiftEnv c0 (appendEnv empty G9))) (weaken_shift_etvar (appendEnv empty G9) H68))) (tshift_wfTy _ _ H63 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H68))))))
  end.
Fixpoint shift_evar_Typing (G10 : Env) (t33 : Tm) (T94 : Ty) (jm32 : (Typing G10 t33 T94)) :
(forall (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) ,
  (Typing G11 (shiftTm c0 t33) T94)) :=
  match jm32 in (Typing _ t33 T94) return (forall (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) ,
    (Typing G11 (shiftTm c0 t33) T94)) with
    | (T_Var T89 y1 lk0 H61 H62) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_Var G11 T89 (shiftIndex c0 y1) (shift_evar_lookup_evar H91 lk0) (shift_wfTy _ _ H61 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H91))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H91)) _ H62)))
    | (T_Abs T90 T93 t30 jm28 H63 H64) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_Abs G11 T90 T93 (shiftTm (CS c0) t30) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G10 T90) t30 (weakenTy T93 (HS tm H0)) jm28 (CS c0) (evar G11 T90) (weaken_shift_evar (evar empty T90) H91))) (shift_wfTy _ _ H63 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H91))) (shift_wfTy _ _ H64 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H91)))))
    | (T_App T91 T92 t31 t32 jm29 jm30) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_App G11 T91 T92 (shiftTm c0 t31) (shiftTm c0 t32) (shift_evar_Typing G10 t31 (tarr T91 T92) jm29 c0 G11 (weaken_shift_evar empty H91)) (shift_evar_Typing G10 t32 T91 jm30 c0 G11 (weaken_shift_evar empty H91))))
    | (T_Tabs T90 T93 t30 jm31 H70) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_Tabs G11 T90 T93 (shiftTm c0 t30) (shift_evar_Typing (etvar G10 T90) t30 T93 jm31 c0 (etvar G11 T90) (weaken_shift_evar (etvar empty T90) H91)) (shift_wfTy _ _ H70 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H91)))))
    | (T_Tapp T91 T92 T93 t31 jm20 jm21) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_Tapp G11 T91 T92 T93 (shiftTm c0 t31) (shift_evar_Typing G10 t31 (tall T91 T92) jm20 c0 G11 (weaken_shift_evar empty H91)) (shift_evar_Sub G10 T93 T91 jm21 c0 G11 (weaken_shift_evar empty H91))))
    | (T_Prod T90 T93 t31 t32 jm22 jm23) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_Prod G11 T90 T93 (shiftTm c0 t31) (shiftTm c0 t32) (shift_evar_Typing G10 t31 T90 jm22 c0 G11 (weaken_shift_evar empty H91)) (shift_evar_Typing G10 t32 T93 jm23 c0 G11 (weaken_shift_evar empty H91))))
    | (T_Let T90 T93 p24 t31 t32 G9 jm24 wtp7 jm25 H82) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_Let G11 T90 T93 p24 (shiftTm c0 t31) (shiftTm (weakenCutofftm c0 (appendHvl H0 (bindPat p24))) t32) G9 (shift_evar_Typing G10 t31 T90 jm24 c0 G11 (weaken_shift_evar empty H91)) (shift_evar_PTyping G10 p24 T90 G9 wtp7 c0 G11 (weaken_shift_evar empty H91)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal2 shiftTm (f_equal2 weakenCutofftm eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p24 T90 G9 wtp7)))) eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (shift_evar_Typing (appendEnv G10 (appendEnv empty G9)) t32 (weakenTy T93 (appendHvl H0 (bindPat p24))) jm25 (weakenCutofftm c0 (domainEnv (appendEnv empty G9))) (appendEnv G11 (appendEnv empty G9)) (weaken_shift_evar (appendEnv empty G9) H91))) (shift_wfTy _ _ H82 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H91)))))
    | (T_Sub T90 T93 t30 jm26 jm27) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H91 : (shift_evar c0 G10 G11)) =>
      (T_Sub G11 T90 T93 (shiftTm c0 t30) (shift_evar_Typing G10 t30 T90 jm26 c0 G11 (weaken_shift_evar empty H91)) (shift_evar_Sub G10 T90 T93 jm27 c0 G11 (weaken_shift_evar empty H91))))
  end.
Fixpoint shift_etvar_Typing (G10 : Env) (t33 : Tm) (T94 : Ty) (jm32 : (Typing G10 t33 T94)) :
(forall (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) ,
  (Typing G11 (tshiftTm c0 t33) (tshiftTy c0 T94))) :=
  match jm32 in (Typing _ t33 T94) return (forall (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) ,
    (Typing G11 (tshiftTm c0 t33) (tshiftTy c0 T94))) with
    | (T_Var T89 y1 lk0 H61 H62) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (T_Var G11 (tshiftTy c0 T89) y1 (shift_etvar_lookup_evar H91 lk0) (tshift_wfTy _ _ H61 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H91))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H91)) _ H62)))
    | (T_Abs T90 T93 t30 jm28 H63 H64) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (T_Abs G11 (tshiftTy c0 T90) (tshiftTy c0 T93) (tshiftTm c0 t30) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c0 T93)) (shift_etvar_Typing (evar G10 T90) t30 (weakenTy T93 (HS tm H0)) jm28 c0 (evar G11 (tshiftTy c0 T90)) (weaken_shift_etvar (evar empty T90) H91))) (tshift_wfTy _ _ H63 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H91))) (tshift_wfTy _ _ H64 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H91)))))
    | (T_App T91 T92 t31 t32 jm29 jm30) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (T_App G11 (tshiftTy c0 T91) (tshiftTy c0 T92) (tshiftTm c0 t31) (tshiftTm c0 t32) (shift_etvar_Typing G10 t31 (tarr T91 T92) jm29 c0 G11 (weaken_shift_etvar empty H91)) (shift_etvar_Typing G10 t32 T91 jm30 c0 G11 (weaken_shift_etvar empty H91))))
    | (T_Tabs T90 T93 t30 jm31 H70) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (T_Tabs G11 (tshiftTy c0 T90) (tshiftTy (CS c0) T93) (tshiftTm (CS c0) t30) (shift_etvar_Typing (etvar G10 T90) t30 T93 jm31 (CS c0) (etvar G11 (tshiftTy c0 T90)) (weaken_shift_etvar (etvar empty T90) H91)) (tshift_wfTy _ _ H70 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H91)))))
    | (T_Tapp T91 T92 T93 t31 jm20 jm21) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (Typing_cast G11 _ _ G11 (tshiftTm c0 (tapp t31 T93)) (tshiftTy c0 (tsubstTy X0 T93 T92)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T92 c0 T93)) (T_Tapp G11 (tshiftTy c0 T91) (tshiftTy (CS c0) T92) (tshiftTy c0 T93) (tshiftTm c0 t31) (shift_etvar_Typing G10 t31 (tall T91 T92) jm20 c0 G11 (weaken_shift_etvar empty H91)) (shift_etvar_Sub G10 T93 T91 jm21 c0 G11 (weaken_shift_etvar empty H91)))))
    | (T_Prod T90 T93 t31 t32 jm22 jm23) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (T_Prod G11 (tshiftTy c0 T90) (tshiftTy c0 T93) (tshiftTm c0 t31) (tshiftTm c0 t32) (shift_etvar_Typing G10 t31 T90 jm22 c0 G11 (weaken_shift_etvar empty H91)) (shift_etvar_Typing G10 t32 T93 jm23 c0 G11 (weaken_shift_etvar empty H91))))
    | (T_Let T90 T93 p24 t31 t32 G9 jm24 wtp7 jm25 H82) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (T_Let G11 (tshiftTy c0 T90) (tshiftTy c0 T93) (tshiftPat c0 p24) (tshiftTm c0 t31) (tshiftTm (weakenCutoffty c0 (appendHvl H0 (bindPat p24))) t32) (tshiftEnv c0 G9) (shift_etvar_Typing G10 t31 T90 jm24 c0 G11 (weaken_shift_etvar empty H91)) (shift_etvar_PTyping G10 p24 T90 G9 wtp7 c0 G11 (weaken_shift_etvar empty H91)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tshiftEnv_appendEnv c0 empty G9)) (f_equal2 tshiftTm (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p24 T90 G9 wtp7)))) eq_refl) (eq_trans (f_equal2 tshiftTy (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p24 T90 G9 wtp7)))) eq_refl) (eq_trans (eq_sym (weakenTy_tshiftTy (appendHvl H0 (bindPat p24)) c0 T93)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))))) (shift_etvar_Typing (appendEnv G10 (appendEnv empty G9)) t32 (weakenTy T93 (appendHvl H0 (bindPat p24))) jm25 (weakenCutoffty c0 (domainEnv (appendEnv empty G9))) (appendEnv G11 (tshiftEnv c0 (appendEnv empty G9))) (weaken_shift_etvar (appendEnv empty G9) H91))) (tshift_wfTy _ _ H82 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H91)))))
    | (T_Sub T90 T93 t30 jm26 jm27) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H91 : (shift_etvar c0 G10 G11)) =>
      (T_Sub G11 (tshiftTy c0 T90) (tshiftTy c0 T93) (tshiftTm c0 t30) (shift_etvar_Typing G10 t30 T90 jm26 c0 G11 (weaken_shift_etvar empty H91)) (shift_etvar_Sub G10 T90 T93 jm27 c0 G11 (weaken_shift_etvar empty H91))))
  end.
 Hint Resolve shift_evar_PTyping shift_etvar_PTyping shift_evar_Sub shift_etvar_Sub shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_PTyping shift_etvar_PTyping shift_evar_Sub shift_etvar_Sub shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_Sub (G2 : Env) :
(forall (G3 : Env) (T79 : Ty) (T80 : Ty) (jm18 : (Sub G3 T79 T80)) ,
  (Sub (appendEnv G3 G2) (weakenTy T79 (domainEnv G2)) (weakenTy T80 (domainEnv G2)))) :=
  match G2 return (forall (G3 : Env) (T79 : Ty) (T80 : Ty) (jm18 : (Sub G3 T79 T80)) ,
    (Sub (appendEnv G3 G2) (weakenTy T79 (domainEnv G2)) (weakenTy T80 (domainEnv G2)))) with
    | (empty) => (fun (G3 : Env) (T79 : Ty) (T80 : Ty) (jm18 : (Sub G3 T79 T80)) =>
      jm18)
    | (evar G2 T81) => (fun (G3 : Env) (T79 : Ty) (T80 : Ty) (jm18 : (Sub G3 T79 T80)) =>
      (shift_evar_Sub (appendEnv G3 G2) (weakenTy T79 (domainEnv G2)) (weakenTy T80 (domainEnv G2)) (weaken_Sub G2 G3 T79 T80 jm18) C0 (evar (appendEnv G3 G2) T81) shift_evar_here))
    | (etvar G2 T82) => (fun (G3 : Env) (T79 : Ty) (T80 : Ty) (jm18 : (Sub G3 T79 T80)) =>
      (shift_etvar_Sub (appendEnv G3 G2) (weakenTy T79 (domainEnv G2)) (weakenTy T80 (domainEnv G2)) (weaken_Sub G2 G3 T79 T80 jm18) C0 (etvar (appendEnv G3 G2) T82) shift_etvar_here))
  end.
Fixpoint weaken_PTyping (G4 : Env) :
(forall (G5 : Env) (p23 : Pat) (T83 : Ty) (G6 : Env) (wtp6 : (PTyping G5 p23 T83 G6)) ,
  (PTyping (appendEnv G5 G4) (weakenPat p23 (domainEnv G4)) (weakenTy T83 (domainEnv G4)) (weakenEnv G6 (domainEnv G4)))) :=
  match G4 return (forall (G5 : Env) (p23 : Pat) (T83 : Ty) (G6 : Env) (wtp6 : (PTyping G5 p23 T83 G6)) ,
    (PTyping (appendEnv G5 G4) (weakenPat p23 (domainEnv G4)) (weakenTy T83 (domainEnv G4)) (weakenEnv G6 (domainEnv G4)))) with
    | (empty) => (fun (G5 : Env) (p23 : Pat) (T83 : Ty) (G6 : Env) (wtp6 : (PTyping G5 p23 T83 G6)) =>
      wtp6)
    | (evar G4 T84) => (fun (G5 : Env) (p23 : Pat) (T83 : Ty) (G6 : Env) (wtp6 : (PTyping G5 p23 T83 G6)) =>
      (shift_evar_PTyping (appendEnv G5 G4) (weakenPat p23 (domainEnv G4)) (weakenTy T83 (domainEnv G4)) (weakenEnv G6 (domainEnv G4)) (weaken_PTyping G4 G5 p23 T83 G6 wtp6) C0 (evar (appendEnv G5 G4) T84) shift_evar_here))
    | (etvar G4 T85) => (fun (G5 : Env) (p23 : Pat) (T83 : Ty) (G6 : Env) (wtp6 : (PTyping G5 p23 T83 G6)) =>
      (shift_etvar_PTyping (appendEnv G5 G4) (weakenPat p23 (domainEnv G4)) (weakenTy T83 (domainEnv G4)) (weakenEnv G6 (domainEnv G4)) (weaken_PTyping G4 G5 p23 T83 G6 wtp6) C0 (etvar (appendEnv G5 G4) T85) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G7 : Env) :
(forall (G8 : Env) (t29 : Tm) (T86 : Ty) (jm19 : (Typing G8 t29 T86)) ,
  (Typing (appendEnv G8 G7) (weakenTm t29 (domainEnv G7)) (weakenTy T86 (domainEnv G7)))) :=
  match G7 return (forall (G8 : Env) (t29 : Tm) (T86 : Ty) (jm19 : (Typing G8 t29 T86)) ,
    (Typing (appendEnv G8 G7) (weakenTm t29 (domainEnv G7)) (weakenTy T86 (domainEnv G7)))) with
    | (empty) => (fun (G8 : Env) (t29 : Tm) (T86 : Ty) (jm19 : (Typing G8 t29 T86)) =>
      jm19)
    | (evar G7 T87) => (fun (G8 : Env) (t29 : Tm) (T86 : Ty) (jm19 : (Typing G8 t29 T86)) =>
      (shift_evar_Typing (appendEnv G8 G7) (weakenTm t29 (domainEnv G7)) (weakenTy T86 (domainEnv G7)) (weaken_Typing G7 G8 t29 T86 jm19) C0 (evar (appendEnv G8 G7) T87) shift_evar_here))
    | (etvar G7 T88) => (fun (G8 : Env) (t29 : Tm) (T86 : Ty) (jm19 : (Typing G8 t29 T86)) =>
      (shift_etvar_Typing (appendEnv G8 G7) (weakenTm t29 (domainEnv G7)) (weakenTy T86 (domainEnv G7)) (weaken_Typing G7 G8 t29 T86 jm19) C0 (etvar (appendEnv G8 G7) T88) shift_etvar_here))
  end.
Fixpoint Sub_wf_0 (G2 : Env) (T89 : Ty) (T90 : Ty) (jm20 : (Sub G2 T89 T90)) {struct jm20} :
(wfTy (domainEnv G2) T89) :=
  match jm20 in (Sub _ T89 T90) return (wfTy (domainEnv G2) T89) with
    | (SA_Top S1 H29) => H29
    | (SA_Refl_TVar X H30) => (wfTy_tvar (domainEnv G2) _ H30)
    | (SA_Trans_TVar T U X lk jm H33) => (wfTy_tvar (domainEnv G2) _ H33)
    | (SA_Arrow S1 S2 T1 T2 jm0 jm1) => (wfTy_tarr (domainEnv G2) (Sub_wf_1 G2 T1 S1 jm0) (Sub_wf_0 G2 S2 T2 jm1))
    | (SA_All S1 S2 T1 T2 jm2 jm3) => (wfTy_tall (domainEnv G2) (Sub_wf_1 G2 T1 S1 jm2) (Sub_wf_0 (etvar G2 T1) S2 T2 jm3))
    | (SA_Prod S1 S2 T1 T2 jm4 jm5) => (wfTy_tprod (domainEnv G2) (Sub_wf_0 G2 S1 T1 jm4) (Sub_wf_0 G2 S2 T2 jm5))
  end
with Sub_wf_1 (G2 : Env) (T89 : Ty) (T90 : Ty) (jm21 : (Sub G2 T89 T90)) {struct jm21} :
(wfTy (domainEnv G2) T90) :=
  match jm21 in (Sub _ T89 T90) return (wfTy (domainEnv G2) T90) with
    | (SA_Top S1 H29) => (wfTy_top (domainEnv G2))
    | (SA_Refl_TVar X H30) => (wfTy_tvar (domainEnv G2) _ H30)
    | (SA_Trans_TVar T U X lk jm H33) => (Sub_wf_1 G2 U T jm)
    | (SA_Arrow S1 S2 T1 T2 jm0 jm1) => (wfTy_tarr (domainEnv G2) (Sub_wf_0 G2 T1 S1 jm0) (Sub_wf_1 G2 S2 T2 jm1))
    | (SA_All S1 S2 T1 T2 jm2 jm3) => (wfTy_tall (domainEnv G2) (Sub_wf_0 G2 T1 S1 jm2) (Sub_wf_1 (etvar G2 T1) S2 T2 jm3))
    | (SA_Prod S1 S2 T1 T2 jm4 jm5) => (wfTy_tprod (domainEnv G2) (Sub_wf_1 G2 S1 T1 jm4) (Sub_wf_1 G2 S2 T2 jm5))
  end.
Fixpoint PTyping_wf_0 (G2 : Env) (p24 : Pat) (T91 : Ty) (G9 : Env) (wtp7 : (PTyping G2 p24 T91 G9)) {struct wtp7} :
(wfPat (domainEnv G2) p24) :=
  match wtp7 in (PTyping _ p24 T91 G9) return (wfPat (domainEnv G2) p24) with
    | (P_Var T H29) => (wfPat_pvar (domainEnv G2) H29)
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H31) => (wfPat_pprod (domainEnv G2) (PTyping_wf_0 G2 p1 T1 G wtp1) (wfPat_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p1 T1 G wtp1))))) eq_refl (PTyping_wf_0 (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0 wtp2)))
  end
with PTyping_wf_1 (G2 : Env) (p24 : Pat) (T91 : Ty) (G10 : Env) (wtp8 : (PTyping G2 p24 T91 G10)) {struct wtp8} :
(wfTy (domainEnv G2) T91) :=
  match wtp8 in (PTyping _ p24 T91 G10) return (wfTy (domainEnv G2) T91) with
    | (P_Var T H29) => H29
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H31) => (wfTy_tprod (domainEnv G2) (PTyping_wf_1 G2 p1 T1 G wtp1) H31)
  end.
Fixpoint Typing_wf_0 (G2 : Env) (t30 : Tm) (T92 : Ty) (jm22 : (Typing G2 t30 T92)) {struct jm22} :
(wfTm (domainEnv G2) t30) :=
  match jm22 in (Typing _ t30 T92) return (wfTm (domainEnv G2) t30) with
    | (T_Var T y lk0 H29 H30) => (wfTm_var (domainEnv G2) _ H30)
    | (T_Abs T1 T2 t jm6 H31 H32) => (wfTm_abs (domainEnv G2) H31 (Typing_wf_0 (evar G2 T1) t (weakenTy T2 (HS tm H0)) jm6))
    | (T_App T11 T12 t1 t2 jm7 jm8) => (wfTm_app (domainEnv G2) (Typing_wf_0 G2 t1 (tarr T11 T12) jm7) (Typing_wf_0 G2 t2 T11 jm8))
    | (T_Tabs T1 T2 t jm9 H38) => (wfTm_tabs (domainEnv G2) H38 (Typing_wf_0 (etvar G2 T1) t T2 jm9))
    | (T_Tapp T11 T12 T2 t1 jm10 jm11) => (wfTm_tapp (domainEnv G2) (Typing_wf_0 G2 t1 (tall T11 T12) jm10) (Sub_wf_0 G2 T2 T11 jm11))
    | (T_Prod T1 T2 t1 t2 jm12 jm13) => (wfTm_prod (domainEnv G2) (Typing_wf_0 G2 t1 T1 jm12) (Typing_wf_0 G2 t2 T2 jm13))
    | (T_Let T1 T2 p t1 t2 G1 jm14 wtp jm15 H50) => (wfTm_lett (domainEnv G2) (PTyping_wf_0 G2 p T1 G1 wtp) (Typing_wf_0 G2 t1 T1 jm14) (wfTm_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G1)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G1) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p T1 G1 wtp))))) eq_refl (Typing_wf_0 (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p))) jm15)))
    | (T_Sub T1 T2 t jm16 jm17) => (Typing_wf_0 G2 t T1 jm16)
  end
with Typing_wf_1 (G2 : Env) (t30 : Tm) (T92 : Ty) (jm23 : (Typing G2 t30 T92)) {struct jm23} :
(wfTy (domainEnv G2) T92) :=
  match jm23 in (Typing _ t30 T92) return (wfTy (domainEnv G2) T92) with
    | (T_Var T y lk1 H29 H30) => H29
    | (T_Abs T1 T2 t jm6 H31 H32) => (wfTy_tarr (domainEnv G2) H31 H32)
    | (T_App T11 T12 t1 t2 jm7 jm8) => (inversion_wfTy_tarr_1 (domainEnv G2) T11 T12 (Typing_wf_1 G2 t1 (tarr T11 T12) jm7))
    | (T_Tabs T1 T2 t jm9 H38) => (wfTy_tall (domainEnv G2) H38 (Typing_wf_1 (etvar G2 T1) t T2 jm9))
    | (T_Tapp T11 T12 T2 t1 jm10 jm11) => (substhvl_ty_wfTy (Sub_wf_0 G2 T2 T11 jm11) (HS ty (domainEnv G2)) T12 (inversion_wfTy_tall_2 (domainEnv G2) T11 T12 (Typing_wf_1 G2 t1 (tall T11 T12) jm10)) (substhvl_ty_here (domainEnv G2)))
    | (T_Prod T1 T2 t1 t2 jm12 jm13) => (wfTy_tprod (domainEnv G2) (Typing_wf_1 G2 t1 T1 jm12) (Typing_wf_1 G2 t2 T2 jm13))
    | (T_Let T1 T2 p t1 t2 G1 jm14 wtp jm15 H50) => H50
    | (T_Sub T1 T2 t jm16 jm17) => (Sub_wf_1 G2 T1 T2 jm17)
  end.
 Hint Extern 8 => match goal with
  | H67 : (Sub _ _ _) |- _ => pose proof ((Sub_wf_0 _ _ _ H67)); pose proof ((Sub_wf_1 _ _ _ H67)); clear H67
end : wf.
 Hint Extern 8 => match goal with
  | H68 : (PTyping _ _ _ _) |- _ => pose proof ((PTyping_wf_0 _ _ _ _ H68)); pose proof ((PTyping_wf_1 _ _ _ _ H68)); clear H68
end : wf.
 Hint Extern 8 => match goal with
  | H69 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H69)); pose proof ((Typing_wf_1 _ _ _ H69)); clear H69
end : wf.
Class Obligation_Env_var_ty : Prop := { Env_var_ty (G11 : Env) (X22 : (Index ty)) (T : Ty) : (lookup_etvar G11 X22 T) -> (Sub G11 (tvar X22) T) }.
Context {obligation_Env_var_ty : Obligation_Env_var_ty} .
Lemma subst_evar_lookup_evar (G12 : Env) (s6 : Tm) (T93 : Ty) (jm24 : (Typing G12 s6 T93)) :
  (forall (d0 : (Trace tm)) (G13 : Env) (G15 : Env) (sub : (subst_evar G12 T93 s6 d0 G13 G15)) (x14 : (Index tm)) (T94 : Ty) ,
    (lookup_evar G13 x14 T94) -> (Typing G15 (substIndex d0 s6 x14) T94)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Lemma subst_etvar_lookup_etvar (G12 : Env) (S20 : Ty) (T93 : Ty) (jm24 : (Sub G12 S20 T93)) :
  (forall (d0 : (Trace ty)) (G13 : Env) (G15 : Env) (sub : (subst_etvar G12 T93 S20 d0 G13 G15)) (X23 : (Index ty)) (T94 : Ty) ,
    (lookup_etvar G13 X23 T94) -> (Sub G15 (tsubstIndex d0 S20 X23) (tsubstTy d0 S20 T94))).
Proof.
  needleGenericSubstEnvLookupHom (Env_var_ty).
Qed.
Class Obligation_Env_reg_Sub : Prop := { Env_reg_SA_Refl_TVar (G2 : Env) (S20 : Ty) (H70 : (wfTy (domainEnv G2) S20)) : (Sub G2 (weakenTy S20 H0) (weakenTy S20 H0)) ; Env_reg_SA_Trans_TVar (G2 : Env) (T : Ty) (U : Ty) (S21 : Ty) (jm24 : (Sub G2 S21 U)) (jm : (Sub G2 U T)) (H71 : (wfTy (domainEnv G2) S21)) : (Sub G2 (weakenTy S21 H0) T) }.
Context {obligation_Env_reg_Sub : Obligation_Env_reg_Sub} .
Fixpoint subst_evar_Sub (G13 : Env) (s6 : Tm) (T93 : Ty) (jm32 : (Typing G13 s6 T93)) (G12 : Env) (T1 : Ty) (T2 : Ty) (jm33 : (Sub G12 T1 T2)) :
(forall (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) ,
  (Sub G14 T1 T2)) :=
  match jm33 in (Sub _ T1 T2) return (forall (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) ,
    (Sub G14 T1 T2)) with
    | (SA_Top S22 H73) => (fun (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) =>
      (SA_Top G14 S22 (substhvl_tm_wfTy _ _ H73 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H90)))))
    | (SA_Refl_TVar X23 H74) => (fun (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) =>
      (SA_Refl_TVar G14 X23 (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H90)) H74)))
    | (SA_Trans_TVar T94 U1 X23 lk2 jm25 H77) => (fun (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) =>
      (SA_Trans_TVar G14 T94 U1 X23 (subst_evar_lookup_etvar T93 H90 U1 lk2) (subst_evar_Sub G13 s6 T93 jm32 G12 U1 T94 jm25 G14 d0 (weaken_subst_evar _ empty H90)) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H90)) H77)))
    | (SA_Arrow S22 S23 T95 T96 jm26 jm27) => (fun (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) =>
      (SA_Arrow G14 S22 S23 T95 T96 (subst_evar_Sub G13 s6 T93 jm32 G12 T95 S22 jm26 G14 d0 (weaken_subst_evar _ empty H90)) (subst_evar_Sub G13 s6 T93 jm32 G12 S23 T96 jm27 G14 d0 (weaken_subst_evar _ empty H90))))
    | (SA_All S22 S23 T95 T96 jm28 jm29) => (fun (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) =>
      (SA_All G14 S22 S23 T95 T96 (subst_evar_Sub G13 s6 T93 jm32 G12 T95 S22 jm28 G14 d0 (weaken_subst_evar _ empty H90)) (subst_evar_Sub G13 s6 T93 jm32 (etvar G12 T95) S23 T96 jm29 (appendEnv G14 (etvar empty T95)) (weakenTrace d0 (HS ty H0)) (weaken_subst_evar _ (etvar empty T95) H90))))
    | (SA_Prod S22 S23 T95 T96 jm30 jm31) => (fun (G14 : Env) (d0 : (Trace tm)) (H90 : (subst_evar G13 T93 s6 d0 G12 G14)) =>
      (SA_Prod G14 S22 S23 T95 T96 (subst_evar_Sub G13 s6 T93 jm32 G12 S22 T95 jm30 G14 d0 (weaken_subst_evar _ empty H90)) (subst_evar_Sub G13 s6 T93 jm32 G12 S23 T96 jm31 G14 d0 (weaken_subst_evar _ empty H90))))
  end.
Fixpoint subst_etvar_Sub (G13 : Env) (S24 : Ty) (T94 : Ty) (jm32 : (Sub G13 S24 T94)) (G12 : Env) (T1 : Ty) (T2 : Ty) (jm33 : (Sub G12 T1 T2)) :
(forall (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) ,
  (Sub G14 (tsubstTy d0 S24 T1) (tsubstTy d0 S24 T2))) :=
  match jm33 in (Sub _ T1 T2) return (forall (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) ,
    (Sub G14 (tsubstTy d0 S24 T1) (tsubstTy d0 S24 T2))) with
    | (SA_Top S22 H74) => (fun (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) =>
      (SA_Top G14 (tsubstTy (weakenTrace d0 H0) S24 S22) (substhvl_ty_wfTy (Sub_wf_0 G13 S24 T94 jm32) _ _ H74 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H91)))))
    | (SA_Refl_TVar X23 H75) => (fun (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) =>
      (Env_reg_SA_Refl_TVar G14 _ (substhvl_ty_wfindex_ty (Sub_wf_0 G13 S24 T94 jm32) (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H91)) H75)))
    | (SA_Trans_TVar T95 U1 X23 lk2 jm25 H78) => (fun (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) =>
      (Env_reg_SA_Trans_TVar G14 (tsubstTy (weakenTrace d0 H0) S24 T95) (tsubstTy (weakenTrace d0 H0) S24 U1) _ (subst_etvar_lookup_etvar G13 S24 T94 jm32 d0 _ _ H91 X23 U1 lk2) (subst_etvar_Sub G13 S24 T94 jm32 G12 U1 T95 jm25 G14 d0 (weaken_subst_etvar _ empty H91)) (substhvl_ty_wfindex_ty (Sub_wf_0 G13 S24 T94 jm32) (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H91)) H78)))
    | (SA_Arrow S22 S23 T96 T97 jm26 jm27) => (fun (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) =>
      (SA_Arrow G14 (tsubstTy (weakenTrace d0 H0) S24 S22) (tsubstTy (weakenTrace d0 H0) S24 S23) (tsubstTy (weakenTrace d0 H0) S24 T96) (tsubstTy (weakenTrace d0 H0) S24 T97) (subst_etvar_Sub G13 S24 T94 jm32 G12 T96 S22 jm26 G14 d0 (weaken_subst_etvar _ empty H91)) (subst_etvar_Sub G13 S24 T94 jm32 G12 S23 T97 jm27 G14 d0 (weaken_subst_etvar _ empty H91))))
    | (SA_All S22 S23 T96 T97 jm28 jm29) => (fun (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) =>
      (SA_All G14 (tsubstTy (weakenTrace d0 H0) S24 S22) (tsubstTy (weakenTrace d0 (HS ty H0)) S24 S23) (tsubstTy (weakenTrace d0 H0) S24 T96) (tsubstTy (weakenTrace d0 (HS ty H0)) S24 T97) (subst_etvar_Sub G13 S24 T94 jm32 G12 T96 S22 jm28 G14 d0 (weaken_subst_etvar _ empty H91)) (subst_etvar_Sub G13 S24 T94 jm32 (etvar G12 T96) S23 T97 jm29 (appendEnv G14 (tsubstEnv d0 S24 (etvar empty T96))) (weakenTrace d0 (HS ty H0)) (weaken_subst_etvar _ (etvar empty T96) H91))))
    | (SA_Prod S22 S23 T96 T97 jm30 jm31) => (fun (G14 : Env) (d0 : (Trace ty)) (H91 : (subst_etvar G13 T94 S24 d0 G12 G14)) =>
      (SA_Prod G14 (tsubstTy (weakenTrace d0 H0) S24 S22) (tsubstTy (weakenTrace d0 H0) S24 S23) (tsubstTy (weakenTrace d0 H0) S24 T96) (tsubstTy (weakenTrace d0 H0) S24 T97) (subst_etvar_Sub G13 S24 T94 jm32 G12 S22 T96 jm30 G14 d0 (weaken_subst_etvar _ empty H91)) (subst_etvar_Sub G13 S24 T94 jm32 G12 S23 T97 jm31 G14 d0 (weaken_subst_etvar _ empty H91))))
  end.
Fixpoint subst_evar_PTyping (G15 : Env) (s6 : Tm) (T95 : Ty) (jm25 : (Typing G15 s6 T95)) (G14 : Env) (p : Pat) (T : Ty) (G16 : Env) (wtp11 : (PTyping G14 p T G16)) :
(forall (G17 : Env) (d0 : (Trace tm)) (H80 : (subst_evar G15 T95 s6 d0 G14 G17)) ,
  (PTyping G17 p T G16)) :=
  match wtp11 in (PTyping _ p T G16) return (forall (G17 : Env) (d0 : (Trace tm)) (H80 : (subst_evar G15 T95 s6 d0 G14 G17)) ,
    (PTyping G17 p T G16)) with
    | (P_Var T96 H75) => (fun (G17 : Env) (d0 : (Trace tm)) (H80 : (subst_evar G15 T95 s6 d0 G14 G17)) =>
      (P_Var G17 T96 (substhvl_tm_wfTy _ _ H75 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H80)))))
    | (P_Prod T97 T98 p25 p26 G12 G13 wtp9 wtp10 H77) => (fun (G17 : Env) (d0 : (Trace tm)) (H80 : (subst_evar G15 T95 s6 d0 G14 G17)) =>
      (PTyping_cast G17 _ _ _ G17 (pprod p25 p26) (tprod T97 T98) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G17 T97 T98 p25 p26 G12 G13 (subst_evar_PTyping G15 s6 T95 jm25 G14 p25 T97 G12 wtp9 G17 d0 (weaken_subst_evar _ empty H80)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (subst_evar_PTyping G15 s6 T95 jm25 (appendEnv G14 (appendEnv empty G12)) p26 (weakenTy T98 (appendHvl H0 (bindPat p25))) G13 wtp10 (appendEnv G17 (appendEnv empty G12)) (weakenTrace d0 (domainEnv (appendEnv empty G12))) (weaken_subst_evar _ (appendEnv empty G12) H80))) (substhvl_tm_wfTy _ _ H77 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H80))))))
  end.
Fixpoint subst_etvar_PTyping (G15 : Env) (S22 : Ty) (T96 : Ty) (jm25 : (Sub G15 S22 T96)) (G14 : Env) (p : Pat) (T : Ty) (G16 : Env) (wtp11 : (PTyping G14 p T G16)) :
(forall (G17 : Env) (d0 : (Trace ty)) (H81 : (subst_etvar G15 T96 S22 d0 G14 G17)) ,
  (PTyping G17 (tsubstPat d0 S22 p) (tsubstTy d0 S22 T) (tsubstEnv d0 S22 G16))) :=
  match wtp11 in (PTyping _ p T G16) return (forall (G17 : Env) (d0 : (Trace ty)) (H81 : (subst_etvar G15 T96 S22 d0 G14 G17)) ,
    (PTyping G17 (tsubstPat d0 S22 p) (tsubstTy d0 S22 T) (tsubstEnv d0 S22 G16))) with
    | (P_Var T97 H76) => (fun (G17 : Env) (d0 : (Trace ty)) (H81 : (subst_etvar G15 T96 S22 d0 G14 G17)) =>
      (P_Var G17 (tsubstTy (weakenTrace d0 H0) S22 T97) (substhvl_ty_wfTy (Sub_wf_0 G15 S22 T96 jm25) _ _ H76 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H81)))))
    | (P_Prod T98 T99 p25 p26 G12 G13 wtp9 wtp10 H78) => (fun (G17 : Env) (d0 : (Trace ty)) (H81 : (subst_etvar G15 T96 S22 d0 G14 G17)) =>
      (PTyping_cast G17 _ _ _ G17 (tsubstPat d0 S22 (pprod p25 p26)) (tsubstTy d0 S22 (tprod T98 T99)) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym (tsubstEnv_appendEnv d0 S22 empty G12)) eq_refl) (eq_sym (tsubstEnv_appendEnv d0 S22 (appendEnv empty G12) G13))) (P_Prod G17 (tsubstTy (weakenTrace d0 H0) S22 T98) (tsubstTy (weakenTrace d0 H0) S22 T99) (tsubstPat (weakenTrace d0 H0) S22 p25) (tsubstPat (weakenTrace d0 (appendHvl H0 (bindPat p25))) S22 p26) (tsubstEnv (weakenTrace d0 H0) S22 G12) (tsubstEnv (weakenTrace d0 (domainEnv (appendEnv empty G12))) S22 G13) (subst_etvar_PTyping G15 S22 T96 jm25 G14 p25 T98 G12 wtp9 G17 d0 (weaken_subst_etvar _ empty H81)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tsubstEnv_appendEnv d0 S22 empty G12)) (f_equal3 tsubstPat (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G12) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G14 p25 T98 G12 wtp9)))) eq_refl eq_refl) (eq_trans (f_equal3 tsubstTy (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G12) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G14 p25 T98 G12 wtp9)))) eq_refl eq_refl) (eq_trans (eq_sym (weakenTy_tsubstTy (appendHvl H0 (bindPat p25)) d0 S22 T99)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))))) eq_refl (subst_etvar_PTyping G15 S22 T96 jm25 (appendEnv G14 (appendEnv empty G12)) p26 (weakenTy T99 (appendHvl H0 (bindPat p25))) G13 wtp10 (appendEnv G17 (tsubstEnv d0 S22 (appendEnv empty G12))) (weakenTrace d0 (domainEnv (appendEnv empty G12))) (weaken_subst_etvar _ (appendEnv empty G12) H81))) (substhvl_ty_wfTy (Sub_wf_0 G15 S22 T96 jm25) _ _ H78 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H81))))))
  end.
Fixpoint subst_evar_Typing (G14 : Env) (s6 : Tm) (T97 : Ty) (jm37 : (Typing G14 s6 T97)) (G13 : Env) (t : Tm) (T : Ty) (jm38 : (Typing G13 t T)) :
(forall (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) ,
  (Typing G15 (substTm d0 s6 t) T)) :=
  match jm38 in (Typing _ t T) return (forall (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) ,
    (Typing G15 (substTm d0 s6 t) T)) with
    | (T_Var T98 y1 lk2 H77 H78) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (subst_evar_lookup_evar G14 s6 T97 jm37 d0 G13 G15 H105 y1 T98 lk2))
    | (T_Abs T99 T102 t31 jm33 H79 H80) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (T_Abs G15 T99 T102 (substTm (weakenTrace d0 (HS tm H0)) s6 t31) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G14 s6 T97 jm37 (evar G13 T99) t31 (weakenTy T102 (HS tm H0)) jm33 (appendEnv G15 (evar empty T99)) (weakenTrace d0 (HS tm H0)) (weaken_subst_evar _ (evar empty T99) H105))) (substhvl_tm_wfTy _ _ H79 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H105))) (substhvl_tm_wfTy _ _ H80 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H105)))))
    | (T_App T100 T101 t32 t33 jm34 jm35) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (T_App G15 T100 T101 (substTm (weakenTrace d0 H0) s6 t32) (substTm (weakenTrace d0 H0) s6 t33) (subst_evar_Typing G14 s6 T97 jm37 G13 t32 (tarr T100 T101) jm34 G15 d0 (weaken_subst_evar _ empty H105)) (subst_evar_Typing G14 s6 T97 jm37 G13 t33 T100 jm35 G15 d0 (weaken_subst_evar _ empty H105))))
    | (T_Tabs T99 T102 t31 jm36 H86) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (T_Tabs G15 T99 T102 (substTm (weakenTrace d0 (HS ty H0)) s6 t31) (subst_evar_Typing G14 s6 T97 jm37 (etvar G13 T99) t31 T102 jm36 (appendEnv G15 (etvar empty T99)) (weakenTrace d0 (HS ty H0)) (weaken_subst_evar _ (etvar empty T99) H105)) (substhvl_tm_wfTy _ _ H86 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H105)))))
    | (T_Tapp T100 T101 T102 t32 jm25 jm26) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (T_Tapp G15 T100 T101 T102 (substTm (weakenTrace d0 H0) s6 t32) (subst_evar_Typing G14 s6 T97 jm37 G13 t32 (tall T100 T101) jm25 G15 d0 (weaken_subst_evar _ empty H105)) (subst_evar_Sub G14 s6 T97 jm37 G13 T102 T100 jm26 G15 d0 (weaken_subst_evar _ empty H105))))
    | (T_Prod T99 T102 t32 t33 jm27 jm28) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (T_Prod G15 T99 T102 (substTm (weakenTrace d0 H0) s6 t32) (substTm (weakenTrace d0 H0) s6 t33) (subst_evar_Typing G14 s6 T97 jm37 G13 t32 T99 jm27 G15 d0 (weaken_subst_evar _ empty H105)) (subst_evar_Typing G14 s6 T97 jm37 G13 t33 T102 jm28 G15 d0 (weaken_subst_evar _ empty H105))))
    | (T_Let T99 T102 p25 t32 t33 G12 jm29 wtp9 jm30 H98) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (T_Let G15 T99 T102 p25 (substTm (weakenTrace d0 H0) s6 t32) (substTm (weakenTrace d0 (appendHvl H0 (bindPat p25))) s6 t33) G12 (subst_evar_Typing G14 s6 T97 jm37 G13 t32 T99 jm29 G15 d0 (weaken_subst_evar _ empty H105)) (subst_evar_PTyping G14 s6 T97 jm37 G13 p25 T99 G12 wtp9 G15 d0 (weaken_subst_evar _ empty H105)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal3 substTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G12) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G13 p25 T99 G12 wtp9)))) eq_refl eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (subst_evar_Typing G14 s6 T97 jm37 (appendEnv G13 (appendEnv empty G12)) t33 (weakenTy T102 (appendHvl H0 (bindPat p25))) jm30 (appendEnv G15 (appendEnv empty G12)) (weakenTrace d0 (domainEnv (appendEnv empty G12))) (weaken_subst_evar _ (appendEnv empty G12) H105))) (substhvl_tm_wfTy _ _ H98 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H105)))))
    | (T_Sub T99 T102 t31 jm31 jm32) => (fun (G15 : Env) (d0 : (Trace tm)) (H105 : (subst_evar G14 T97 s6 d0 G13 G15)) =>
      (T_Sub G15 T99 T102 (substTm (weakenTrace d0 H0) s6 t31) (subst_evar_Typing G14 s6 T97 jm37 G13 t31 T99 jm31 G15 d0 (weaken_subst_evar _ empty H105)) (subst_evar_Sub G14 s6 T97 jm37 G13 T99 T102 jm32 G15 d0 (weaken_subst_evar _ empty H105))))
  end.
Fixpoint subst_etvar_Typing (G14 : Env) (S22 : Ty) (T98 : Ty) (jm37 : (Sub G14 S22 T98)) (G13 : Env) (t : Tm) (T : Ty) (jm38 : (Typing G13 t T)) :
(forall (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) ,
  (Typing G15 (tsubstTm d0 S22 t) (tsubstTy d0 S22 T))) :=
  match jm38 in (Typing _ t T) return (forall (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) ,
    (Typing G15 (tsubstTm d0 S22 t) (tsubstTy d0 S22 T))) with
    | (T_Var T99 y1 lk2 H78 H79) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (T_Var G15 (tsubstTy (weakenTrace d0 H0) S22 T99) y1 (subst_etvar_lookup_evar T98 (Sub_wf_0 G14 S22 T98 jm37) H106 T99 lk2) (substhvl_ty_wfTy (Sub_wf_0 G14 S22 T98 jm37) _ _ H78 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H106))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H106)) H79)))
    | (T_Abs T100 T103 t31 jm33 H80 H81) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (T_Abs G15 (tsubstTy (weakenTrace d0 H0) S22 T100) (tsubstTy (weakenTrace d0 H0) S22 T103) (tsubstTm (weakenTrace d0 (HS tm H0)) S22 t31) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d0 S22 T103)) (subst_etvar_Typing G14 S22 T98 jm37 (evar G13 T100) t31 (weakenTy T103 (HS tm H0)) jm33 (appendEnv G15 (tsubstEnv d0 S22 (evar empty T100))) (weakenTrace d0 (HS tm H0)) (weaken_subst_etvar _ (evar empty T100) H106))) (substhvl_ty_wfTy (Sub_wf_0 G14 S22 T98 jm37) _ _ H80 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H106))) (substhvl_ty_wfTy (Sub_wf_0 G14 S22 T98 jm37) _ _ H81 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H106)))))
    | (T_App T101 T102 t32 t33 jm34 jm35) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (T_App G15 (tsubstTy (weakenTrace d0 H0) S22 T101) (tsubstTy (weakenTrace d0 H0) S22 T102) (tsubstTm (weakenTrace d0 H0) S22 t32) (tsubstTm (weakenTrace d0 H0) S22 t33) (subst_etvar_Typing G14 S22 T98 jm37 G13 t32 (tarr T101 T102) jm34 G15 d0 (weaken_subst_etvar _ empty H106)) (subst_etvar_Typing G14 S22 T98 jm37 G13 t33 T101 jm35 G15 d0 (weaken_subst_etvar _ empty H106))))
    | (T_Tabs T100 T103 t31 jm36 H87) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (T_Tabs G15 (tsubstTy (weakenTrace d0 H0) S22 T100) (tsubstTy (weakenTrace d0 (HS ty H0)) S22 T103) (tsubstTm (weakenTrace d0 (HS ty H0)) S22 t31) (subst_etvar_Typing G14 S22 T98 jm37 (etvar G13 T100) t31 T103 jm36 (appendEnv G15 (tsubstEnv d0 S22 (etvar empty T100))) (weakenTrace d0 (HS ty H0)) (weaken_subst_etvar _ (etvar empty T100) H106)) (substhvl_ty_wfTy (Sub_wf_0 G14 S22 T98 jm37) _ _ H87 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H106)))))
    | (T_Tapp T101 T102 T103 t32 jm25 jm26) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (Typing_cast G15 _ _ G15 (tsubstTm d0 S22 (tapp t32 T103)) (tsubstTy d0 S22 (tsubstTy X0 T103 T102)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T102 d0 S22 T103)) (T_Tapp G15 (tsubstTy (weakenTrace d0 H0) S22 T101) (tsubstTy (weakenTrace d0 (HS ty H0)) S22 T102) (tsubstTy (weakenTrace d0 H0) S22 T103) (tsubstTm (weakenTrace d0 H0) S22 t32) (subst_etvar_Typing G14 S22 T98 jm37 G13 t32 (tall T101 T102) jm25 G15 d0 (weaken_subst_etvar _ empty H106)) (subst_etvar_Sub G14 S22 T98 jm37 G13 T103 T101 jm26 G15 d0 (weaken_subst_etvar _ empty H106)))))
    | (T_Prod T100 T103 t32 t33 jm27 jm28) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (T_Prod G15 (tsubstTy (weakenTrace d0 H0) S22 T100) (tsubstTy (weakenTrace d0 H0) S22 T103) (tsubstTm (weakenTrace d0 H0) S22 t32) (tsubstTm (weakenTrace d0 H0) S22 t33) (subst_etvar_Typing G14 S22 T98 jm37 G13 t32 T100 jm27 G15 d0 (weaken_subst_etvar _ empty H106)) (subst_etvar_Typing G14 S22 T98 jm37 G13 t33 T103 jm28 G15 d0 (weaken_subst_etvar _ empty H106))))
    | (T_Let T100 T103 p25 t32 t33 G12 jm29 wtp9 jm30 H99) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (T_Let G15 (tsubstTy (weakenTrace d0 H0) S22 T100) (tsubstTy (weakenTrace d0 H0) S22 T103) (tsubstPat (weakenTrace d0 H0) S22 p25) (tsubstTm (weakenTrace d0 H0) S22 t32) (tsubstTm (weakenTrace d0 (appendHvl H0 (bindPat p25))) S22 t33) (tsubstEnv (weakenTrace d0 H0) S22 G12) (subst_etvar_Typing G14 S22 T98 jm37 G13 t32 T100 jm29 G15 d0 (weaken_subst_etvar _ empty H106)) (subst_etvar_PTyping G14 S22 T98 jm37 G13 p25 T100 G12 wtp9 G15 d0 (weaken_subst_etvar _ empty H106)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tsubstEnv_appendEnv d0 S22 empty G12)) (f_equal3 tsubstTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G12) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G13 p25 T100 G12 wtp9)))) eq_refl eq_refl) (eq_trans (f_equal3 tsubstTy (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G12) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G13 p25 T100 G12 wtp9)))) eq_refl eq_refl) (eq_trans (eq_sym (weakenTy_tsubstTy (appendHvl H0 (bindPat p25)) d0 S22 T103)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))))) (subst_etvar_Typing G14 S22 T98 jm37 (appendEnv G13 (appendEnv empty G12)) t33 (weakenTy T103 (appendHvl H0 (bindPat p25))) jm30 (appendEnv G15 (tsubstEnv d0 S22 (appendEnv empty G12))) (weakenTrace d0 (domainEnv (appendEnv empty G12))) (weaken_subst_etvar _ (appendEnv empty G12) H106))) (substhvl_ty_wfTy (Sub_wf_0 G14 S22 T98 jm37) _ _ H99 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H106)))))
    | (T_Sub T100 T103 t31 jm31 jm32) => (fun (G15 : Env) (d0 : (Trace ty)) (H106 : (subst_etvar G14 T98 S22 d0 G13 G15)) =>
      (T_Sub G15 (tsubstTy (weakenTrace d0 H0) S22 T100) (tsubstTy (weakenTrace d0 H0) S22 T103) (tsubstTm (weakenTrace d0 H0) S22 t31) (subst_etvar_Typing G14 S22 T98 jm37 G13 t31 T100 jm31 G15 d0 (weaken_subst_etvar _ empty H106)) (subst_etvar_Sub G14 S22 T98 jm37 G13 T100 T103 jm32 G15 d0 (weaken_subst_etvar _ empty H106))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.