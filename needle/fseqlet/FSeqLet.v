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
  
  Fixpoint weakenIndextm (x15 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x15
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x15 k))
        | _ => (weakenIndextm x15 k)
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
    (forall (x15 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x15 k) k0) = (weakenIndextm x15 (appendHvl k k0)))).
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
  
  Inductive Decls : Set :=
    | dnil 
    | dcons (t : Tm) (d : Decls)
  with Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | lett (d : Decls) (t : Tm).
  Scheme ind_Decls := Induction for Decls Sort Prop
  with ind_Tm := Induction for Tm Sort Prop.
  Combined Scheme ind_Decls_Tm from ind_Decls, ind_Tm.
End Terms.

Section Functions.
  Fixpoint bind (d10 : Decls) {struct d10} :
  Hvl :=
    match d10 with
      | (dnil) => H0
      | (dcons t d) => (appendHvl (HS tm H0) (bind d))
    end.
  Scheme ind_bind_Decls := Induction for Decls Sort Prop.
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
  Fixpoint shiftIndex (c : (Cutoff tm)) (x15 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x15)
      | (CS c) => match x15 with
        | (I0) => I0
        | (IS x15) => (IS (shiftIndex c x15))
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
      | (tarr T28 T29) => (tarr (tshiftTy c T28) (tshiftTy c T29))
      | (tall T30) => (tall (tshiftTy (CS c) T30))
    end.
  Fixpoint shiftDecls (c : (Cutoff tm)) (d11 : Decls) {struct d11} :
  Decls :=
    match d11 with
      | (dnil) => (dnil)
      | (dcons t22 d12) => (dcons (shiftTm c t22) (shiftDecls (CS c) d12))
    end
  with shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x15) => (var (shiftIndex c x15))
      | (abs T28 t22) => (abs T28 (shiftTm (CS c) t22))
      | (app t23 t24) => (app (shiftTm c t23) (shiftTm c t24))
      | (tabs t25) => (tabs (shiftTm c t25))
      | (tapp t26 T29) => (tapp (shiftTm c t26) T29)
      | (lett d11 t27) => (lett (shiftDecls c d11) (shiftTm (weakenCutofftm c (appendHvl H0 (bind d11))) t27))
    end.
  Fixpoint tshiftDecls (c : (Cutoff ty)) (d11 : Decls) {struct d11} :
  Decls :=
    match d11 with
      | (dnil) => (dnil)
      | (dcons t22 d12) => (dcons (tshiftTm c t22) (tshiftDecls c d12))
    end
  with tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x15) => (var x15)
      | (abs T28 t22) => (abs (tshiftTy c T28) (tshiftTm c t22))
      | (app t23 t24) => (app (tshiftTm c t23) (tshiftTm c t24))
      | (tabs t25) => (tabs (tshiftTm (CS c) t25))
      | (tapp t26 T29) => (tapp (tshiftTm c t26) (tshiftTy c T29))
      | (lett d11 t27) => (lett (tshiftDecls c d11) (tshiftTm (weakenCutoffty c (appendHvl H0 (bind d11))) t27))
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
  Fixpoint weakenDecls (d11 : Decls) (k : Hvl) {struct k} :
  Decls :=
    match k with
      | (H0) => d11
      | (HS tm k) => (shiftDecls C0 (weakenDecls d11 k))
      | (HS ty k) => (tshiftDecls C0 (weakenDecls d11 k))
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
        (T28 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x15 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x15
      | (HS b k) => (XS b (weakenTrace x15 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x15 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x15 k) k0) = (weakenTrace x15 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d11 : (Trace tm)) (s : Tm) (x15 : (Index tm)) {struct d11} :
  Tm :=
    match d11 with
      | (X0) => match x15 with
        | (I0) => s
        | (IS x15) => (var x15)
      end
      | (XS tm d11) => match x15 with
        | (I0) => (var I0)
        | (IS x15) => (shiftTm C0 (substIndex d11 s x15))
      end
      | (XS ty d11) => (tshiftTm C0 (substIndex d11 s x15))
    end.
  Fixpoint tsubstIndex (d11 : (Trace ty)) (S0 : Ty) (X12 : (Index ty)) {struct d11} :
  Ty :=
    match d11 with
      | (X0) => match X12 with
        | (I0) => S0
        | (IS X12) => (tvar X12)
      end
      | (XS tm d11) => (tsubstIndex d11 S0 X12)
      | (XS ty d11) => match X12 with
        | (I0) => (tvar I0)
        | (IS X12) => (tshiftTy C0 (tsubstIndex d11 S0 X12))
      end
    end.
  Fixpoint tsubstTy (d11 : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (tvar X12) => (tsubstIndex d11 S0 X12)
      | (tarr T28 T29) => (tarr (tsubstTy d11 S0 T28) (tsubstTy d11 S0 T29))
      | (tall T30) => (tall (tsubstTy (weakenTrace d11 (HS ty H0)) S0 T30))
    end.
  Fixpoint substDecls (d11 : (Trace tm)) (s : Tm) (d12 : Decls) {struct d12} :
  Decls :=
    match d12 with
      | (dnil) => (dnil)
      | (dcons t22 d13) => (dcons (substTm d11 s t22) (substDecls (weakenTrace d11 (HS tm H0)) s d13))
    end
  with substTm (d11 : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x15) => (substIndex d11 s x15)
      | (abs T28 t22) => (abs T28 (substTm (weakenTrace d11 (HS tm H0)) s t22))
      | (app t23 t24) => (app (substTm d11 s t23) (substTm d11 s t24))
      | (tabs t25) => (tabs (substTm (weakenTrace d11 (HS ty H0)) s t25))
      | (tapp t26 T29) => (tapp (substTm d11 s t26) T29)
      | (lett d12 t27) => (lett (substDecls d11 s d12) (substTm (weakenTrace d11 (appendHvl H0 (bind d12))) s t27))
    end.
  Fixpoint tsubstDecls (d11 : (Trace ty)) (S0 : Ty) (d12 : Decls) {struct d12} :
  Decls :=
    match d12 with
      | (dnil) => (dnil)
      | (dcons t22 d13) => (dcons (tsubstTm d11 S0 t22) (tsubstDecls (weakenTrace d11 (HS tm H0)) S0 d13))
    end
  with tsubstTm (d11 : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x15) => (var x15)
      | (abs T28 t22) => (abs (tsubstTy d11 S0 T28) (tsubstTm (weakenTrace d11 (HS tm H0)) S0 t22))
      | (app t23 t24) => (app (tsubstTm d11 S0 t23) (tsubstTm d11 S0 t24))
      | (tabs t25) => (tabs (tsubstTm (weakenTrace d11 (HS ty H0)) S0 t25))
      | (tapp t26 T29) => (tapp (tsubstTm d11 S0 t26) (tsubstTy d11 S0 T29))
      | (lett d12 t27) => (lett (tsubstDecls d11 S0 d12) (tsubstTm (weakenTrace d11 (appendHvl H0 (bind d12))) S0 t27))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftDecls C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftDecls C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_shift_bind  :
  (forall (d11 : Decls) ,
    (forall (c : (Cutoff tm)) ,
      ((bind (shiftDecls c d11)) = (bind d11)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_tshift_bind  :
  (forall (d12 : Decls) ,
    (forall (c0 : (Cutoff ty)) ,
      ((bind (tshiftDecls c0 d12)) = (bind d12)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_shift_bind stability_tshift_bind : interaction.
 Hint Rewrite stability_shift_bind stability_tshift_bind : stability_shift.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (d13 : Decls) ,
    ((bind (weakenDecls d13 k)) = (bind d13))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Lemma stability_subst_bind  :
  (forall (d13 : Decls) ,
    (forall (d14 : (Trace tm)) (s : Tm) ,
      ((bind (substDecls d14 s d13)) = (bind d13)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_tsubst_bind  :
  (forall (d15 : Decls) ,
    (forall (d16 : (Trace ty)) (S0 : Ty) ,
      ((bind (tsubstDecls d16 S0 d15)) = (bind d15)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_subst_bind stability_tsubst_bind : interaction.
 Hint Rewrite stability_subst_bind stability_tsubst_bind : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s0 : Tm) :
    (forall (k : Hvl) (x15 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s0 (shiftIndex (weakenCutofftm C0 k) x15)) = (var x15))).
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
      | (tarr T29 T30) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T29 k S1) (tsubst0_tshift0_Ty_reflection_ind T30 k S1))
      | (tall T28) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T28 (HS ty k) S1)))
    end.
  Fixpoint subst0_shift0_Decls_reflection_ind (d17 : Decls) (k : Hvl) (s0 : Tm) {struct d17} :
  ((substDecls (weakenTrace X0 k) s0 (shiftDecls (weakenCutofftm C0 k) d17)) = d17) :=
    match d17 return ((substDecls (weakenTrace X0 k) s0 (shiftDecls (weakenCutofftm C0 k) d17)) = d17) with
      | (dnil) => eq_refl
      | (dcons t22 d18) => (f_equal2 dcons (subst0_shift0_Tm_reflection_ind t22 k s0) (eq_trans (f_equal3 substDecls (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Decls_reflection_ind d18 (HS tm k) s0)))
    end
  with subst0_shift0_Tm_reflection_ind (s1 : Tm) (k : Hvl) (s0 : Tm) {struct s1} :
  ((substTm (weakenTrace X0 k) s0 (shiftTm (weakenCutofftm C0 k) s1)) = s1) :=
    match s1 return ((substTm (weakenTrace X0 k) s0 (shiftTm (weakenCutofftm C0 k) s1)) = s1) with
      | (var x16) => (substIndex0_shiftIndex0_reflection_ind s0 k x16)
      | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t23 (HS tm k) s0)))
      | (app t24 t25) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t24 k s0) (subst0_shift0_Tm_reflection_ind t25 k s0))
      | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t23 (HS ty k) s0)))
      | (tapp t23 T28) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t23 k s0) eq_refl)
      | (lett d19 t23) => (f_equal2 lett (subst0_shift0_Decls_reflection_ind d19 k s0) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_bind _ _))) (weakenTrace_append tm X0 k (appendHvl H0 (bind d19)))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bind d19))) eq_refl)) (subst0_shift0_Tm_reflection_ind t23 (appendHvl k (appendHvl H0 (bind d19))) s0)))
    end.
  Fixpoint tsubst0_tshift0_Decls_reflection_ind (d17 : Decls) (k : Hvl) (S1 : Ty) {struct d17} :
  ((tsubstDecls (weakenTrace X0 k) S1 (tshiftDecls (weakenCutoffty C0 k) d17)) = d17) :=
    match d17 return ((tsubstDecls (weakenTrace X0 k) S1 (tshiftDecls (weakenCutoffty C0 k) d17)) = d17) with
      | (dnil) => eq_refl
      | (dcons t22 d18) => (f_equal2 dcons (tsubst0_tshift0_Tm_reflection_ind t22 k S1) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Decls_reflection_ind d18 (HS tm k) S1)))
    end
  with tsubst0_tshift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (S1 : Ty) {struct s0} :
  ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffty C0 k) s0)) = s0) :=
    match s0 return ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffty C0 k) s0)) = s0) with
      | (var x16) => eq_refl
      | (abs T28 t23) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T28 k S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t23 (HS tm k) S1)))
      | (app t24 t25) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t24 k S1) (tsubst0_tshift0_Tm_reflection_ind t25 k S1))
      | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t23 (HS ty k) S1)))
      | (tapp t23 T28) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t23 k S1) (tsubst0_tshift0_Ty_reflection_ind T28 k S1))
      | (lett d19 t23) => (f_equal2 lett (tsubst0_tshift0_Decls_reflection_ind d19 k S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bind d19)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bind d19))) eq_refl)) (tsubst0_tshift0_Tm_reflection_ind t23 (appendHvl k (appendHvl H0 (bind d19))) S1)))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S2 : Ty) : (forall (S1 : Ty) ,
    ((tsubstTy X0 S1 (tshiftTy C0 S2)) = S2)) := (tsubst0_tshift0_Ty_reflection_ind S2 H0).
  Definition substDecls0_shiftDecls0_reflection (d17 : Decls) : (forall (s0 : Tm) ,
    ((substDecls X0 s0 (shiftDecls C0 d17)) = d17)) := (subst0_shift0_Decls_reflection_ind d17 H0).
  Definition substTm0_shiftTm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((substTm X0 s0 (shiftTm C0 s1)) = s1)) := (subst0_shift0_Tm_reflection_ind s1 H0).
  Definition tsubstDecls0_tshiftDecls0_reflection (d17 : Decls) : (forall (S1 : Ty) ,
    ((tsubstDecls X0 S1 (tshiftDecls C0 d17)) = d17)) := (tsubst0_tshift0_Decls_reflection_ind d17 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s0 : Tm) : (forall (S1 : Ty) ,
    ((tsubstTm X0 S1 (tshiftTm C0 s0)) = s0)) := (tsubst0_tshift0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c1 : (Cutoff tm)) (x15 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c1) k) (shiftIndex (weakenCutofftm C0 k) x15)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c1 k) x15)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c1 : (Cutoff ty)) (X12 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c1) k) (tshiftIndex (weakenCutoffty C0 k) X12)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c1 k) X12)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff ty)) {struct S1} :
    ((tshiftTy (weakenCutoffty (CS c1) k) (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c1 k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffty (CS c1) k) (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c1 k) S1))) with
        | (tvar X12) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c1 X12))
        | (tarr T29 T30) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T29 k c1) (tshift_tshift0_Ty_comm_ind T30 k c1))
        | (tall T28) => (f_equal tall (tshift_tshift0_Ty_comm_ind T28 (HS ty k) c1))
      end.
    Fixpoint shift_shift0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff tm)) {struct d17} :
    ((shiftDecls (weakenCutofftm (CS c1) k) (shiftDecls (weakenCutofftm C0 k) d17)) = (shiftDecls (weakenCutofftm C0 k) (shiftDecls (weakenCutofftm c1 k) d17))) :=
      match d17 return ((shiftDecls (weakenCutofftm (CS c1) k) (shiftDecls (weakenCutofftm C0 k) d17)) = (shiftDecls (weakenCutofftm C0 k) (shiftDecls (weakenCutofftm c1 k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (shift_shift0_Tm_comm_ind t22 k c1) (shift_shift0_Decls_comm_ind d18 (HS tm k) c1))
      end
    with shift_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff tm)) {struct s0} :
    ((shiftTm (weakenCutofftm (CS c1) k) (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c1 k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm (CS c1) k) (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c1 k) s0))) with
        | (var x16) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c1 x16))
        | (abs T28 t23) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t23 (HS tm k) c1))
        | (app t24 t25) => (f_equal2 app (shift_shift0_Tm_comm_ind t24 k c1) (shift_shift0_Tm_comm_ind t25 k c1))
        | (tabs t23) => (f_equal tabs (shift_shift0_Tm_comm_ind t23 (HS ty k) c1))
        | (tapp t23 T28) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t23 k c1) eq_refl)
        | (lett d19 t23) => (f_equal2 lett (shift_shift0_Decls_comm_ind d19 k c1) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_bind _ _))) (weakenCutofftm_append (CS c1) k (appendHvl H0 (bind d19)))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bind d19))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_bind _ _))))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c1 k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
    Fixpoint shift_tshift0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff tm)) {struct d17} :
    ((shiftDecls (weakenCutofftm c1 k) (tshiftDecls (weakenCutoffty C0 k) d17)) = (tshiftDecls (weakenCutoffty C0 k) (shiftDecls (weakenCutofftm c1 k) d17))) :=
      match d17 return ((shiftDecls (weakenCutofftm c1 k) (tshiftDecls (weakenCutoffty C0 k) d17)) = (tshiftDecls (weakenCutoffty C0 k) (shiftDecls (weakenCutofftm c1 k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (shift_tshift0_Tm_comm_ind t22 k c1) (shift_tshift0_Decls_comm_ind d18 (HS tm k) c1))
      end
    with shift_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff tm)) {struct s0} :
    ((shiftTm (weakenCutofftm c1 k) (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c1 k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c1 k) (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c1 k) s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t23 (HS tm k) c1))
        | (app t24 t25) => (f_equal2 app (shift_tshift0_Tm_comm_ind t24 k c1) (shift_tshift0_Tm_comm_ind t25 k c1))
        | (tabs t23) => (f_equal tabs (shift_tshift0_Tm_comm_ind t23 (HS ty k) c1))
        | (tapp t23 T28) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t23 k c1) eq_refl)
        | (lett d19 t23) => (f_equal2 lett (shift_tshift0_Decls_comm_ind d19 k c1) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenCutofftm_append c1 k (appendHvl H0 (bind d19)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bind d19))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_bind _ _))))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c1 k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
    Fixpoint tshift_shift0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff ty)) {struct d17} :
    ((tshiftDecls (weakenCutoffty c1 k) (shiftDecls (weakenCutofftm C0 k) d17)) = (shiftDecls (weakenCutofftm C0 k) (tshiftDecls (weakenCutoffty c1 k) d17))) :=
      match d17 return ((tshiftDecls (weakenCutoffty c1 k) (shiftDecls (weakenCutofftm C0 k) d17)) = (shiftDecls (weakenCutofftm C0 k) (tshiftDecls (weakenCutoffty c1 k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (tshift_shift0_Tm_comm_ind t22 k c1) (tshift_shift0_Decls_comm_ind d18 (HS tm k) c1))
      end
    with tshift_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff ty)) {struct s0} :
    ((tshiftTm (weakenCutoffty c1 k) (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c1 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c1 k) (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c1 k) s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t23 (HS tm k) c1))
        | (app t24 t25) => (f_equal2 app (tshift_shift0_Tm_comm_ind t24 k c1) (tshift_shift0_Tm_comm_ind t25 k c1))
        | (tabs t23) => (f_equal tabs (tshift_shift0_Tm_comm_ind t23 (HS ty k) c1))
        | (tapp t23 T28) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t23 k c1) eq_refl)
        | (lett d19 t23) => (f_equal2 lett (tshift_shift0_Decls_comm_ind d19 k c1) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_bind _ _))) (weakenCutoffty_append c1 k (appendHvl H0 (bind d19)))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bind d19))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c1 k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
    Fixpoint tshift_tshift0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff ty)) {struct d17} :
    ((tshiftDecls (weakenCutoffty (CS c1) k) (tshiftDecls (weakenCutoffty C0 k) d17)) = (tshiftDecls (weakenCutoffty C0 k) (tshiftDecls (weakenCutoffty c1 k) d17))) :=
      match d17 return ((tshiftDecls (weakenCutoffty (CS c1) k) (tshiftDecls (weakenCutoffty C0 k) d17)) = (tshiftDecls (weakenCutoffty C0 k) (tshiftDecls (weakenCutoffty c1 k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (tshift_tshift0_Tm_comm_ind t22 k c1) (tshift_tshift0_Decls_comm_ind d18 (HS tm k) c1))
      end
    with tshift_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff ty)) {struct s0} :
    ((tshiftTm (weakenCutoffty (CS c1) k) (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c1 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty (CS c1) k) (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c1 k) s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T28 k c1) (tshift_tshift0_Tm_comm_ind t23 (HS tm k) c1))
        | (app t24 t25) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t24 k c1) (tshift_tshift0_Tm_comm_ind t25 k c1))
        | (tabs t23) => (f_equal tabs (tshift_tshift0_Tm_comm_ind t23 (HS ty k) c1))
        | (tapp t23 T28) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t23 k c1) (tshift_tshift0_Ty_comm_ind T28 k c1))
        | (lett d19 t23) => (f_equal2 lett (tshift_tshift0_Decls_comm_ind d19 k c1) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenCutoffty_append (CS c1) k (appendHvl H0 (bind d19)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bind d19))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c1 k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S1 : Ty) : (forall (c1 : (Cutoff ty)) ,
      ((tshiftTy (CS c1) (tshiftTy C0 S1)) = (tshiftTy C0 (tshiftTy c1 S1)))) := (tshift_tshift0_Ty_comm_ind S1 H0).
    Definition shift_shift0_Decls_comm (d17 : Decls) : (forall (c1 : (Cutoff tm)) ,
      ((shiftDecls (CS c1) (shiftDecls C0 d17)) = (shiftDecls C0 (shiftDecls c1 d17)))) := (shift_shift0_Decls_comm_ind d17 H0).
    Definition shift_shift0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff tm)) ,
      ((shiftTm (CS c1) (shiftTm C0 s0)) = (shiftTm C0 (shiftTm c1 s0)))) := (shift_shift0_Tm_comm_ind s0 H0).
    Definition shift_tshift0_Decls_comm (d17 : Decls) : (forall (c1 : (Cutoff tm)) ,
      ((shiftDecls c1 (tshiftDecls C0 d17)) = (tshiftDecls C0 (shiftDecls c1 d17)))) := (shift_tshift0_Decls_comm_ind d17 H0).
    Definition shift_tshift0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff tm)) ,
      ((shiftTm c1 (tshiftTm C0 s0)) = (tshiftTm C0 (shiftTm c1 s0)))) := (shift_tshift0_Tm_comm_ind s0 H0).
    Definition tshift_shift0_Decls_comm (d17 : Decls) : (forall (c1 : (Cutoff ty)) ,
      ((tshiftDecls c1 (shiftDecls C0 d17)) = (shiftDecls C0 (tshiftDecls c1 d17)))) := (tshift_shift0_Decls_comm_ind d17 H0).
    Definition tshift_shift0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff ty)) ,
      ((tshiftTm c1 (shiftTm C0 s0)) = (shiftTm C0 (tshiftTm c1 s0)))) := (tshift_shift0_Tm_comm_ind s0 H0).
    Definition tshift_tshift0_Decls_comm (d17 : Decls) : (forall (c1 : (Cutoff ty)) ,
      ((tshiftDecls (CS c1) (tshiftDecls C0 d17)) = (tshiftDecls C0 (tshiftDecls c1 d17)))) := (tshift_tshift0_Decls_comm_ind d17 H0).
    Definition tshift_tshift0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff ty)) ,
      ((tshiftTm (CS c1) (tshiftTm C0 s0)) = (tshiftTm C0 (tshiftTm c1 s0)))) := (tshift_tshift0_Tm_comm_ind s0 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Decls_comm shift_tshift0_Decls_comm tshift_shift0_Decls_comm tshift_tshift0_Decls_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Decls_comm shift_tshift0_Decls_comm tshift_shift0_Decls_comm tshift_tshift0_Decls_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c1 : (Cutoff ty)) (S1 : Ty) ,
      ((weakenTy (tshiftTy c1 S1) k) = (tshiftTy (weakenCutoffty c1 k) (weakenTy S1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenDecls_shiftDecls  :
    (forall (k : Hvl) (c1 : (Cutoff tm)) (d17 : Decls) ,
      ((weakenDecls (shiftDecls c1 d17) k) = (shiftDecls (weakenCutofftm c1 k) (weakenDecls d17 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c1 : (Cutoff tm)) (s0 : Tm) ,
      ((weakenTm (shiftTm c1 s0) k) = (shiftTm (weakenCutofftm c1 k) (weakenTm s0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenDecls_tshiftDecls  :
    (forall (k : Hvl) (c1 : (Cutoff ty)) (d17 : Decls) ,
      ((weakenDecls (tshiftDecls c1 d17) k) = (tshiftDecls (weakenCutoffty c1 k) (weakenDecls d17 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c1 : (Cutoff ty)) (s0 : Tm) ,
      ((weakenTm (tshiftTm c1 s0) k) = (tshiftTm (weakenCutoffty c1 k) (weakenTm s0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c1 : (Cutoff tm)) (s0 : Tm) :
      (forall (k : Hvl) (x15 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c1 k) (substIndex (weakenTrace X0 k) s0 x15)) = (substIndex (weakenTrace X0 k) (shiftTm c1 s0) (shiftIndex (weakenCutofftm (CS c1) k) x15)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c1 : (Cutoff ty)) (s0 : Tm) :
      (forall (k : Hvl) (x15 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c1 k) (substIndex (weakenTrace X0 k) s0 x15)) = (substIndex (weakenTrace X0 k) (tshiftTm c1 s0) x15))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c1 : (Cutoff ty)) (S1 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c1 k) (tsubstIndex (weakenTrace X0 k) S1 X12)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c1 S1) (tshiftIndex (weakenCutoffty (CS c1) k) X12)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c1 : (Cutoff ty)) (S1 : Ty) {struct S2} :
    ((tshiftTy (weakenCutoffty c1 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c1 S1) (tshiftTy (weakenCutoffty (CS c1) k) S2))) :=
      match S2 return ((tshiftTy (weakenCutoffty c1 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c1 S1) (tshiftTy (weakenCutoffty (CS c1) k) S2))) with
        | (tvar X12) => (tshiftTy_tsubstIndex0_comm_ind c1 S1 k X12)
        | (tarr T29 T30) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T29 k c1 S1) (tshift_tsubst0_Ty_comm_ind T30 k c1 S1))
        | (tall T28) => (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T28 (HS ty k) c1 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_subst0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff tm)) (s0 : Tm) {struct d17} :
    ((shiftDecls (weakenCutofftm c1 k) (substDecls (weakenTrace X0 k) s0 d17)) = (substDecls (weakenTrace X0 k) (shiftTm c1 s0) (shiftDecls (weakenCutofftm (CS c1) k) d17))) :=
      match d17 return ((shiftDecls (weakenCutofftm c1 k) (substDecls (weakenTrace X0 k) s0 d17)) = (substDecls (weakenTrace X0 k) (shiftTm c1 s0) (shiftDecls (weakenCutofftm (CS c1) k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (shift_subst0_Tm_comm_ind t22 k c1 s0) (eq_trans (f_equal2 shiftDecls eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Decls_comm_ind d18 (HS tm k) c1 s0) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
      end
    with shift_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (c1 : (Cutoff tm)) (s0 : Tm) {struct s1} :
    ((shiftTm (weakenCutofftm c1 k) (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (shiftTm c1 s0) (shiftTm (weakenCutofftm (CS c1) k) s1))) :=
      match s1 return ((shiftTm (weakenCutofftm c1 k) (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (shiftTm c1 s0) (shiftTm (weakenCutofftm (CS c1) k) s1))) with
        | (var x16) => (shiftTm_substIndex0_comm_ind c1 s0 k x16)
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t23 (HS tm k) c1 s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t24 t25) => (f_equal2 app (shift_subst0_Tm_comm_ind t24 k c1 s0) (shift_subst0_Tm_comm_ind t25 k c1 s0))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t23 (HS ty k) c1 s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t23 T28) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t23 k c1 s0) eq_refl)
        | (lett d19 t23) => (f_equal2 lett (shift_subst0_Decls_comm_ind d19 k c1 s0) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0)))) (weakenCutofftm_append c1 k (appendHvl H0 (bind d19)))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bind d19))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1 s0) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_bind _ _))))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c1) k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
    Fixpoint shift_tsubst0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff tm)) (S1 : Ty) {struct d17} :
    ((shiftDecls (weakenCutofftm c1 k) (tsubstDecls (weakenTrace X0 k) S1 d17)) = (tsubstDecls (weakenTrace X0 k) S1 (shiftDecls (weakenCutofftm c1 k) d17))) :=
      match d17 return ((shiftDecls (weakenCutofftm c1 k) (tsubstDecls (weakenTrace X0 k) S1 d17)) = (tsubstDecls (weakenTrace X0 k) S1 (shiftDecls (weakenCutofftm c1 k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (shift_tsubst0_Tm_comm_ind t22 k c1 S1) (eq_trans (f_equal2 shiftDecls eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Decls_comm_ind d18 (HS tm k) c1 S1) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
      end
    with shift_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff tm)) (S1 : Ty) {struct s0} :
    ((shiftTm (weakenCutofftm c1 k) (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutofftm c1 k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c1 k) (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutofftm c1 k) s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t23 (HS tm k) c1 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t24 t25) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t24 k c1 S1) (shift_tsubst0_Tm_comm_ind t25 k c1 S1))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t23 (HS ty k) c1 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t23 T28) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t23 k c1 S1) eq_refl)
        | (lett d19 t23) => (f_equal2 lett (shift_tsubst0_Decls_comm_ind d19 k c1 S1) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenCutofftm_append c1 k (appendHvl H0 (bind d19)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bind d19))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1 S1) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_bind _ _))))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c1 k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
    Fixpoint tshift_subst0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff ty)) (s0 : Tm) {struct d17} :
    ((tshiftDecls (weakenCutoffty c1 k) (substDecls (weakenTrace X0 k) s0 d17)) = (substDecls (weakenTrace X0 k) (tshiftTm c1 s0) (tshiftDecls (weakenCutoffty c1 k) d17))) :=
      match d17 return ((tshiftDecls (weakenCutoffty c1 k) (substDecls (weakenTrace X0 k) s0 d17)) = (substDecls (weakenTrace X0 k) (tshiftTm c1 s0) (tshiftDecls (weakenCutoffty c1 k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (tshift_subst0_Tm_comm_ind t22 k c1 s0) (eq_trans (f_equal2 tshiftDecls eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Decls_comm_ind d18 (HS tm k) c1 s0) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
      end
    with tshift_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (c1 : (Cutoff ty)) (s0 : Tm) {struct s1} :
    ((tshiftTm (weakenCutoffty c1 k) (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (tshiftTm c1 s0) (tshiftTm (weakenCutoffty c1 k) s1))) :=
      match s1 return ((tshiftTm (weakenCutoffty c1 k) (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (tshiftTm c1 s0) (tshiftTm (weakenCutoffty c1 k) s1))) with
        | (var x16) => (tshiftTm_substIndex0_comm_ind c1 s0 k x16)
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t23 (HS tm k) c1 s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t24 t25) => (f_equal2 app (tshift_subst0_Tm_comm_ind t24 k c1 s0) (tshift_subst0_Tm_comm_ind t25 k c1 s0))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t23 (HS ty k) c1 s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t23 T28) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t23 k c1 s0) eq_refl)
        | (lett d19 t23) => (f_equal2 lett (tshift_subst0_Decls_comm_ind d19 k c1 s0) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0)))) (weakenCutoffty_append c1 k (appendHvl H0 (bind d19)))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bind d19))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1 s0) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c1 k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
    Fixpoint tshift_tsubst0_Decls_comm_ind (d17 : Decls) (k : Hvl) (c1 : (Cutoff ty)) (S1 : Ty) {struct d17} :
    ((tshiftDecls (weakenCutoffty c1 k) (tsubstDecls (weakenTrace X0 k) S1 d17)) = (tsubstDecls (weakenTrace X0 k) (tshiftTy c1 S1) (tshiftDecls (weakenCutoffty (CS c1) k) d17))) :=
      match d17 return ((tshiftDecls (weakenCutoffty c1 k) (tsubstDecls (weakenTrace X0 k) S1 d17)) = (tsubstDecls (weakenTrace X0 k) (tshiftTy c1 S1) (tshiftDecls (weakenCutoffty (CS c1) k) d17))) with
        | (dnil) => eq_refl
        | (dcons t22 d18) => (f_equal2 dcons (tshift_tsubst0_Tm_comm_ind t22 k c1 S1) (eq_trans (f_equal2 tshiftDecls eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Decls_comm_ind d18 (HS tm k) c1 S1) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
      end
    with tshift_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff ty)) (S1 : Ty) {struct s0} :
    ((tshiftTm (weakenCutoffty c1 k) (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c1 S1) (tshiftTm (weakenCutoffty (CS c1) k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c1 k) (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c1 S1) (tshiftTm (weakenCutoffty (CS c1) k) s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T28 k c1 S1) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t23 (HS tm k) c1 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t24 t25) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t24 k c1 S1) (tshift_tsubst0_Tm_comm_ind t25 k c1 S1))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t23 (HS ty k) c1 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t23 T28) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t23 k c1 S1) (tshift_tsubst0_Ty_comm_ind T28 k c1 S1))
        | (lett d19 t23) => (f_equal2 lett (tshift_tsubst0_Decls_comm_ind d19 k c1 S1) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenCutoffty_append c1 k (appendHvl H0 (bind d19)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bind d19))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d19))) c1 S1) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bind d19)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c1) k (appendHvl H0 (bind d19)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S2 : Ty) : (forall (c1 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftTy c1 (tsubstTy X0 S1 S2)) = (tsubstTy X0 (tshiftTy c1 S1) (tshiftTy (CS c1) S2)))) := (tshift_tsubst0_Ty_comm_ind S2 H0).
    Definition shiftDecls_substDecls0_comm (d17 : Decls) : (forall (c1 : (Cutoff tm)) (s0 : Tm) ,
      ((shiftDecls c1 (substDecls X0 s0 d17)) = (substDecls X0 (shiftTm c1 s0) (shiftDecls (CS c1) d17)))) := (shift_subst0_Decls_comm_ind d17 H0).
    Definition shiftTm_substTm0_comm (s1 : Tm) : (forall (c1 : (Cutoff tm)) (s0 : Tm) ,
      ((shiftTm c1 (substTm X0 s0 s1)) = (substTm X0 (shiftTm c1 s0) (shiftTm (CS c1) s1)))) := (shift_subst0_Tm_comm_ind s1 H0).
    Definition shiftDecls_tsubstDecls0_comm (d17 : Decls) : (forall (c1 : (Cutoff tm)) (S1 : Ty) ,
      ((shiftDecls c1 (tsubstDecls X0 S1 d17)) = (tsubstDecls X0 S1 (shiftDecls c1 d17)))) := (shift_tsubst0_Decls_comm_ind d17 H0).
    Definition shiftTm_tsubstTm0_comm (s0 : Tm) : (forall (c1 : (Cutoff tm)) (S1 : Ty) ,
      ((shiftTm c1 (tsubstTm X0 S1 s0)) = (tsubstTm X0 S1 (shiftTm c1 s0)))) := (shift_tsubst0_Tm_comm_ind s0 H0).
    Definition tshiftDecls_substDecls0_comm (d17 : Decls) : (forall (c1 : (Cutoff ty)) (s0 : Tm) ,
      ((tshiftDecls c1 (substDecls X0 s0 d17)) = (substDecls X0 (tshiftTm c1 s0) (tshiftDecls c1 d17)))) := (tshift_subst0_Decls_comm_ind d17 H0).
    Definition tshiftTm_substTm0_comm (s1 : Tm) : (forall (c1 : (Cutoff ty)) (s0 : Tm) ,
      ((tshiftTm c1 (substTm X0 s0 s1)) = (substTm X0 (tshiftTm c1 s0) (tshiftTm c1 s1)))) := (tshift_subst0_Tm_comm_ind s1 H0).
    Definition tshiftDecls_tsubstDecls0_comm (d17 : Decls) : (forall (c1 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftDecls c1 (tsubstDecls X0 S1 d17)) = (tsubstDecls X0 (tshiftTy c1 S1) (tshiftDecls (CS c1) d17)))) := (tshift_tsubst0_Decls_comm_ind d17 H0).
    Definition tshiftTm_tsubstTm0_comm (s0 : Tm) : (forall (c1 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftTm c1 (tsubstTm X0 S1 s0)) = (tsubstTm X0 (tshiftTy c1 S1) (tshiftTm (CS c1) s0)))) := (tshift_tsubst0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d17 : (Trace tm)) (s0 : Tm) :
      (forall (k : Hvl) (x15 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d17) k) s0 (shiftIndex (weakenCutofftm C0 k) x15)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d17 k) s0 x15)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d17 : (Trace tm)) (s0 : Tm) :
      (forall (k : Hvl) (x15 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d17) k) s0 x15) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d17 k) s0 x15)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d17 : (Trace ty)) (S1 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d17) k) S1 X12) = (tsubstIndex (weakenTrace d17 k) S1 X12))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d17 : (Trace ty)) (S1 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d17) k) S1 (tshiftIndex (weakenCutoffty C0 k) X12)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d17 k) S1 X12)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS ty d17) k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d17 k) S1 S2))) :=
      match S2 return ((tsubstTy (weakenTrace (XS ty d17) k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d17 k) S1 S2))) with
        | (tvar X12) => (tsubstIndex_tshiftTy0_comm_ind d17 S1 k X12)
        | (tarr T29 T30) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T29 k d17 S1) (tsubst_tshift0_Ty_comm_ind T30 k d17 S1))
        | (tall T28) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d17) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T28 (HS ty k) d17 S1) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d17 k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) {struct d18} :
    ((substDecls (weakenTrace (XS tm d17) k) s0 (shiftDecls (weakenCutofftm C0 k) d18)) = (shiftDecls (weakenCutofftm C0 k) (substDecls (weakenTrace d17 k) s0 d18))) :=
      match d18 return ((substDecls (weakenTrace (XS tm d17) k) s0 (shiftDecls (weakenCutofftm C0 k) d18)) = (shiftDecls (weakenCutofftm C0 k) (substDecls (weakenTrace d17 k) s0 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (subst_shift0_Tm_comm_ind t22 k d17 s0) (eq_trans (f_equal3 substDecls (weakenTrace_append tm (XS tm d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Decls_comm_ind d19 (HS tm k) d17 s0) (f_equal2 shiftDecls eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm d17 k (HS tm H0))) eq_refl eq_refl)))))
      end
    with subst_shift0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace (XS tm d17) k) s0 (shiftTm (weakenCutofftm C0 k) s1)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d17 k) s0 s1))) :=
      match s1 return ((substTm (weakenTrace (XS tm d17) k) s0 (shiftTm (weakenCutofftm C0 k) s1)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d17 k) s0 s1))) with
        | (var x16) => (substIndex_shiftTm0_comm_ind d17 s0 k x16)
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t23 (HS tm k) d17 s0) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d17 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (subst_shift0_Tm_comm_ind t24 k d17 s0) (subst_shift0_Tm_comm_ind t25 k d17 s0))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d17) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t23 (HS ty k) d17 s0) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d17 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t23 k d17 s0) eq_refl)
        | (lett d20 t23) => (f_equal2 lett (subst_shift0_Decls_comm_ind d20 k d17 s0) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_bind _ _))) (weakenTrace_append tm (XS tm d17) k (appendHvl H0 (bind d20)))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bind d20))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 s0) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0))))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d17 k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) {struct d18} :
    ((substDecls (weakenTrace (XS ty d17) k) s0 (tshiftDecls (weakenCutoffty C0 k) d18)) = (tshiftDecls (weakenCutoffty C0 k) (substDecls (weakenTrace d17 k) s0 d18))) :=
      match d18 return ((substDecls (weakenTrace (XS ty d17) k) s0 (tshiftDecls (weakenCutoffty C0 k) d18)) = (tshiftDecls (weakenCutoffty C0 k) (substDecls (weakenTrace d17 k) s0 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (subst_tshift0_Tm_comm_ind t22 k d17 s0) (eq_trans (f_equal3 substDecls (weakenTrace_append tm (XS ty d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Decls_comm_ind d19 (HS tm k) d17 s0) (f_equal2 tshiftDecls eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm d17 k (HS tm H0))) eq_refl eq_refl)))))
      end
    with subst_tshift0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace (XS ty d17) k) s0 (tshiftTm (weakenCutoffty C0 k) s1)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d17 k) s0 s1))) :=
      match s1 return ((substTm (weakenTrace (XS ty d17) k) s0 (tshiftTm (weakenCutoffty C0 k) s1)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d17 k) s0 s1))) with
        | (var x16) => (substIndex_tshiftTm0_comm_ind d17 s0 k x16)
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t23 (HS tm k) d17 s0) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d17 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (subst_tshift0_Tm_comm_ind t24 k d17 s0) (subst_tshift0_Tm_comm_ind t25 k d17 s0))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d17) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t23 (HS ty k) d17 s0) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d17 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t23 k d17 s0) eq_refl)
        | (lett d20 t23) => (f_equal2 lett (subst_tshift0_Decls_comm_ind d20 k d17 s0) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append tm (XS ty d17) k (appendHvl H0 (bind d20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bind d20))) eq_refl)) (eq_trans (subst_tshift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 s0) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0))))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d17 k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct d18} :
    ((tsubstDecls (weakenTrace d17 k) S1 (shiftDecls (weakenCutofftm C0 k) d18)) = (shiftDecls (weakenCutofftm C0 k) (tsubstDecls (weakenTrace d17 k) S1 d18))) :=
      match d18 return ((tsubstDecls (weakenTrace d17 k) S1 (shiftDecls (weakenCutofftm C0 k) d18)) = (shiftDecls (weakenCutofftm C0 k) (tsubstDecls (weakenTrace d17 k) S1 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (tsubst_shift0_Tm_comm_ind t22 k d17 S1) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty d17 k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Decls_comm_ind d19 (HS tm k) d17 S1) (f_equal2 shiftDecls eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl)))))
      end
    with tsubst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct s0} :
    ((tsubstTm (weakenTrace d17 k) S1 (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d17 k) S1 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d17 k) S1 (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d17 k) S1 s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d17 k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t23 (HS tm k) d17 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t24 k d17 S1) (tsubst_shift0_Tm_comm_ind t25 k d17 S1))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d17 k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t23 (HS ty k) d17 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t23 k d17 S1) eq_refl)
        | (lett d20 t23) => (f_equal2 lett (tsubst_shift0_Decls_comm_ind d20 k d17 S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_bind _ _))) (weakenTrace_append ty d17 k (appendHvl H0 (bind d20)))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bind d20))) eq_refl)) (eq_trans (tsubst_shift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 S1) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct d18} :
    ((tsubstDecls (weakenTrace (XS ty d17) k) S1 (tshiftDecls (weakenCutoffty C0 k) d18)) = (tshiftDecls (weakenCutoffty C0 k) (tsubstDecls (weakenTrace d17 k) S1 d18))) :=
      match d18 return ((tsubstDecls (weakenTrace (XS ty d17) k) S1 (tshiftDecls (weakenCutoffty C0 k) d18)) = (tshiftDecls (weakenCutoffty C0 k) (tsubstDecls (weakenTrace d17 k) S1 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (tsubst_tshift0_Tm_comm_ind t22 k d17 S1) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty (XS ty d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Decls_comm_ind d19 (HS tm k) d17 S1) (f_equal2 tshiftDecls eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl)))))
      end
    with tsubst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct s0} :
    ((tsubstTm (weakenTrace (XS ty d17) k) S1 (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d17 k) S1 s0))) :=
      match s0 return ((tsubstTm (weakenTrace (XS ty d17) k) S1 (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d17 k) S1 s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T28 k d17 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t23 (HS tm k) d17 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t24 k d17 S1) (tsubst_tshift0_Tm_comm_ind t25 k d17 S1))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d17) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t23 (HS ty k) d17 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t23 k d17 S1) (tsubst_tshift0_Ty_comm_ind T28 k d17 S1))
        | (lett d20 t23) => (f_equal2 lett (tsubst_tshift0_Decls_comm_ind d20 k d17 S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append ty (XS ty d17) k (appendHvl H0 (bind d20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bind d20))) eq_refl)) (eq_trans (tsubst_tshift0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 S1) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S2 : Ty) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTy (XS ty d17) S1 (tshiftTy C0 S2)) = (tshiftTy C0 (tsubstTy d17 S1 S2)))) := (tsubst_tshift0_Ty_comm_ind S2 H0).
    Definition substDecls_shiftDecls0_comm (d18 : Decls) : (forall (d17 : (Trace tm)) (s0 : Tm) ,
      ((substDecls (XS tm d17) s0 (shiftDecls C0 d18)) = (shiftDecls C0 (substDecls d17 s0 d18)))) := (subst_shift0_Decls_comm_ind d18 H0).
    Definition substTm_shiftTm0_comm (s1 : Tm) : (forall (d17 : (Trace tm)) (s0 : Tm) ,
      ((substTm (XS tm d17) s0 (shiftTm C0 s1)) = (shiftTm C0 (substTm d17 s0 s1)))) := (subst_shift0_Tm_comm_ind s1 H0).
    Definition substDecls_tshiftDecls0_comm (d18 : Decls) : (forall (d17 : (Trace tm)) (s0 : Tm) ,
      ((substDecls (XS ty d17) s0 (tshiftDecls C0 d18)) = (tshiftDecls C0 (substDecls d17 s0 d18)))) := (subst_tshift0_Decls_comm_ind d18 H0).
    Definition substTm_tshiftTm0_comm (s1 : Tm) : (forall (d17 : (Trace tm)) (s0 : Tm) ,
      ((substTm (XS ty d17) s0 (tshiftTm C0 s1)) = (tshiftTm C0 (substTm d17 s0 s1)))) := (subst_tshift0_Tm_comm_ind s1 H0).
    Definition tsubstDecls_shiftDecls0_comm (d18 : Decls) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstDecls d17 S1 (shiftDecls C0 d18)) = (shiftDecls C0 (tsubstDecls d17 S1 d18)))) := (tsubst_shift0_Decls_comm_ind d18 H0).
    Definition tsubstTm_shiftTm0_comm (s0 : Tm) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm d17 S1 (shiftTm C0 s0)) = (shiftTm C0 (tsubstTm d17 S1 s0)))) := (tsubst_shift0_Tm_comm_ind s0 H0).
    Definition tsubstDecls_tshiftDecls0_comm (d18 : Decls) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstDecls (XS ty d17) S1 (tshiftDecls C0 d18)) = (tshiftDecls C0 (tsubstDecls d17 S1 d18)))) := (tsubst_tshift0_Decls_comm_ind d18 H0).
    Definition tsubstTm_tshiftTm0_comm (s0 : Tm) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm (XS ty d17) S1 (tshiftTm C0 s0)) = (tshiftTm C0 (tsubstTm d17 S1 s0)))) := (tsubst_tshift0_Tm_comm_ind s0 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S2 : Ty) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS tm d17) k) S1 S2) = (tsubstTy (weakenTrace d17 k) S1 S2)) :=
      match S2 return ((tsubstTy (weakenTrace (XS tm d17) k) S1 S2) = (tsubstTy (weakenTrace d17 k) S1 S2)) with
        | (tvar X12) => (tsubstIndex_shiftTy0_comm_ind d17 S1 k X12)
        | (tarr T29 T30) => (f_equal2 tarr (tsubst_tm_Ty_ind T29 k d17 S1) (tsubst_tm_Ty_ind T30 k d17 S1))
        | (tall T28) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d17) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T28 (HS ty k) d17 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d17 k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Decls_ind (d18 : Decls) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct d18} :
    ((tsubstDecls (weakenTrace (XS tm d17) k) S1 d18) = (tsubstDecls (weakenTrace d17 k) S1 d18)) :=
      match d18 return ((tsubstDecls (weakenTrace (XS tm d17) k) S1 d18) = (tsubstDecls (weakenTrace d17 k) S1 d18)) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (tsubst_tm_Tm_ind t22 k d17 S1) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty (XS tm d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Decls_ind d19 (HS tm k) d17 S1) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl))))
      end
    with tsubst_tm_Tm_ind (s0 : Tm) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) {struct s0} :
    ((tsubstTm (weakenTrace (XS tm d17) k) S1 s0) = (tsubstTm (weakenTrace d17 k) S1 s0)) :=
      match s0 return ((tsubstTm (weakenTrace (XS tm d17) k) S1 s0) = (tsubstTm (weakenTrace d17 k) S1 s0)) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs (tsubst_tm_Ty_ind T28 k d17 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d17) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t23 (HS tm k) d17 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl))))
        | (app t24 t25) => (f_equal2 app (tsubst_tm_Tm_ind t24 k d17 S1) (tsubst_tm_Tm_ind t25 k d17 S1))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d17) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t23 (HS ty k) d17 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t23 T28) => (f_equal2 tapp (tsubst_tm_Tm_ind t23 k d17 S1) (tsubst_tm_Ty_ind T28 k d17 S1))
        | (lett d20 t23) => (f_equal2 lett (tsubst_tm_Decls_ind d20 k d17 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d17) k (appendHvl H0 (bind d20))) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (appendHvl H0 (bind d20)))) eq_refl eq_refl))))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S2 : Ty) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTy (XS tm d17) S1 S2) = (tsubstTy d17 S1 S2))) := (tsubst_tm_Ty_ind S2 H0).
    Definition tsubstDecls_tm (d18 : Decls) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstDecls (XS tm d17) S1 d18) = (tsubstDecls d17 S1 d18))) := (tsubst_tm_Decls_ind d18 H0).
    Definition tsubstTm_tm (s0 : Tm) : (forall (d17 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm (XS tm d17) S1 s0) = (tsubstTm d17 S1 s0))) := (tsubst_tm_Tm_ind s0 H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substDecls0_shiftDecls0_reflection tsubstDecls0_tshiftDecls0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite substDecls0_shiftDecls0_reflection tsubstDecls0_tshiftDecls0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite substDecls_shiftDecls0_comm substDecls_tshiftDecls0_comm tsubstDecls_shiftDecls0_comm tsubstDecls_tshiftDecls0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite substDecls_shiftDecls0_comm substDecls_tshiftDecls0_comm tsubstDecls_shiftDecls0_comm tsubstDecls_tshiftDecls0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstDecls_tm tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstDecls_tm tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite shiftDecls_substDecls0_comm shiftDecls_tsubstDecls0_comm tshiftDecls_substDecls0_comm tshiftDecls_tsubstDecls0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite shiftDecls_substDecls0_comm shiftDecls_tsubstDecls0_comm tshiftDecls_substDecls0_comm tshiftDecls_tsubstDecls0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d17 : (Trace tm)) (s0 : Tm) (s1 : Tm) :
      (forall (k : Hvl) (x15 : (Index tm)) ,
        ((substTm (weakenTrace d17 k) s0 (substIndex (weakenTrace X0 k) s1 x15)) = (substTm (weakenTrace X0 k) (substTm d17 s0 s1) (substIndex (weakenTrace (XS tm d17) k) s0 x15)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d17 : (Trace ty)) (S1 : Ty) (s0 : Tm) :
      (forall (k : Hvl) (x15 : (Index tm)) ,
        ((tsubstTm (weakenTrace d17 k) S1 (substIndex (weakenTrace X0 k) s0 x15)) = (substIndex (weakenTrace X0 k) (tsubstTm d17 S1 s0) x15))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) :
      (forall (k : Hvl) (X12 : (Index ty)) ,
        ((tsubstTy (weakenTrace d17 k) S1 (tsubstIndex (weakenTrace X0 k) S2 X12)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d17 S1 S2) (tsubstIndex (weakenTrace (XS ty d17) k) S1 X12)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d17 : (Trace tm)) (s0 : Tm) (S1 : Ty) :
      (forall (k : Hvl) (x15 : (Index tm)) ,
        ((substIndex (weakenTrace d17 k) s0 x15) = (tsubstTm (weakenTrace X0 k) S1 (substIndex (weakenTrace (XS ty d17) k) s0 x15)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S3 : Ty) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct S3} :
    ((tsubstTy (weakenTrace d17 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d17 S1 S2) (tsubstTy (weakenTrace (XS ty d17) k) S1 S3))) :=
      match S3 return ((tsubstTy (weakenTrace d17 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d17 S1 S2) (tsubstTy (weakenTrace (XS ty d17) k) S1 S3))) with
        | (tvar X12) => (tsubstTy_tsubstIndex0_commright_ind d17 S1 S2 k X12)
        | (tarr T29 T30) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T29 k d17 S1 S2) (tsubst_tsubst0_Ty_comm_ind T30 k d17 S1 S2))
        | (tall T28) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d17 k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T28 (HS ty k) d17 S1 S2) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d17) k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) (s1 : Tm) {struct d18} :
    ((substDecls (weakenTrace d17 k) s0 (substDecls (weakenTrace X0 k) s1 d18)) = (substDecls (weakenTrace X0 k) (substTm d17 s0 s1) (substDecls (weakenTrace (XS tm d17) k) s0 d18))) :=
      match d18 return ((substDecls (weakenTrace d17 k) s0 (substDecls (weakenTrace X0 k) s1 d18)) = (substDecls (weakenTrace X0 k) (substTm d17 s0 s1) (substDecls (weakenTrace (XS tm d17) k) s0 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (subst_subst0_Tm_comm_ind t22 k d17 s0 s1) (eq_trans (f_equal3 substDecls (weakenTrace_append tm d17 k (HS tm H0)) eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Decls_comm_ind d19 (HS tm k) d17 s0 s1) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm (XS tm d17) k (HS tm H0))) eq_refl eq_refl)))))
      end
    with subst_subst0_Tm_comm_ind (s2 : Tm) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) (s1 : Tm) {struct s2} :
    ((substTm (weakenTrace d17 k) s0 (substTm (weakenTrace X0 k) s1 s2)) = (substTm (weakenTrace X0 k) (substTm d17 s0 s1) (substTm (weakenTrace (XS tm d17) k) s0 s2))) :=
      match s2 return ((substTm (weakenTrace d17 k) s0 (substTm (weakenTrace X0 k) s1 s2)) = (substTm (weakenTrace X0 k) (substTm d17 s0 s1) (substTm (weakenTrace (XS tm d17) k) s0 s2))) with
        | (var x16) => (substTm_substIndex0_commright_ind d17 s0 s1 k x16)
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d17 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t23 (HS tm k) d17 s0 s1) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d17) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (subst_subst0_Tm_comm_ind t24 k d17 s0 s1) (subst_subst0_Tm_comm_ind t25 k d17 s0 s1))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d17 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t23 (HS ty k) d17 s0 s1) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d17) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t23 k d17 s0 s1) eq_refl)
        | (lett d20 t23) => (f_equal2 lett (subst_subst0_Decls_comm_ind d20 k d17 s0 s1) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0)))) (weakenTrace_append tm d17 k (appendHvl H0 (bind d20)))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bind d20))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 s0 s1) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d17) k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) (S1 : Ty) {struct d18} :
    ((substDecls (weakenTrace d17 k) s0 (tsubstDecls (weakenTrace X0 k) S1 d18)) = (tsubstDecls (weakenTrace X0 k) S1 (substDecls (weakenTrace (XS ty d17) k) s0 d18))) :=
      match d18 return ((substDecls (weakenTrace d17 k) s0 (tsubstDecls (weakenTrace X0 k) S1 d18)) = (tsubstDecls (weakenTrace X0 k) S1 (substDecls (weakenTrace (XS ty d17) k) s0 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (subst_tsubst0_Tm_comm_ind t22 k d17 s0 S1) (eq_trans (f_equal3 substDecls (weakenTrace_append tm d17 k (HS tm H0)) eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Decls_comm_ind d19 (HS tm k) d17 s0 S1) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm (XS ty d17) k (HS tm H0))) eq_refl eq_refl)))))
      end
    with subst_tsubst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) (S1 : Ty) {struct s1} :
    ((substTm (weakenTrace d17 k) s0 (tsubstTm (weakenTrace X0 k) S1 s1)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS ty d17) k) s0 s1))) :=
      match s1 return ((substTm (weakenTrace d17 k) s0 (tsubstTm (weakenTrace X0 k) S1 s1)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS ty d17) k) s0 s1))) with
        | (var x16) => (substTy_tsubstIndex0_commleft_ind d17 s0 S1 k x16)
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d17 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t23 (HS tm k) d17 s0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d17) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t24 k d17 s0 S1) (subst_tsubst0_Tm_comm_ind t25 k d17 s0 S1))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d17 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t23 (HS ty k) d17 s0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d17) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t23 k d17 s0 S1) eq_refl)
        | (lett d20 t23) => (f_equal2 lett (subst_tsubst0_Decls_comm_ind d20 k d17 s0 S1) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenTrace_append tm d17 k (appendHvl H0 (bind d20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bind d20))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 s0 S1) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d17) k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (s0 : Tm) {struct d18} :
    ((tsubstDecls (weakenTrace d17 k) S1 (substDecls (weakenTrace X0 k) s0 d18)) = (substDecls (weakenTrace X0 k) (tsubstTm d17 S1 s0) (tsubstDecls (weakenTrace d17 k) S1 d18))) :=
      match d18 return ((tsubstDecls (weakenTrace d17 k) S1 (substDecls (weakenTrace X0 k) s0 d18)) = (substDecls (weakenTrace X0 k) (tsubstTm d17 S1 s0) (tsubstDecls (weakenTrace d17 k) S1 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (tsubst_subst0_Tm_comm_ind t22 k d17 S1 s0) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty d17 k (HS tm H0)) eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Decls_comm_ind d19 (HS tm k) d17 S1 s0) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl)))))
      end
    with tsubst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (s0 : Tm) {struct s1} :
    ((tsubstTm (weakenTrace d17 k) S1 (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (tsubstTm d17 S1 s0) (tsubstTm (weakenTrace d17 k) S1 s1))) :=
      match s1 return ((tsubstTm (weakenTrace d17 k) S1 (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (tsubstTm d17 S1 s0) (tsubstTm (weakenTrace d17 k) S1 s1))) with
        | (var x16) => (tsubstTm_substIndex0_commright_ind d17 S1 s0 k x16)
        | (abs T28 t23) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d17 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t23 (HS tm k) d17 S1 s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t24 k d17 S1 s0) (tsubst_subst0_Tm_comm_ind t25 k d17 S1 s0))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d17 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t23 (HS ty k) d17 S1 s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t23 k d17 S1 s0) eq_refl)
        | (lett d20 t23) => (f_equal2 lett (tsubst_subst0_Decls_comm_ind d20 k d17 S1 s0) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0)))) (weakenTrace_append ty d17 k (appendHvl H0 (bind d20)))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bind d20))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 S1 s0) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d17 k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Decls_comm_ind (d18 : Decls) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct d18} :
    ((tsubstDecls (weakenTrace d17 k) S1 (tsubstDecls (weakenTrace X0 k) S2 d18)) = (tsubstDecls (weakenTrace X0 k) (tsubstTy d17 S1 S2) (tsubstDecls (weakenTrace (XS ty d17) k) S1 d18))) :=
      match d18 return ((tsubstDecls (weakenTrace d17 k) S1 (tsubstDecls (weakenTrace X0 k) S2 d18)) = (tsubstDecls (weakenTrace X0 k) (tsubstTy d17 S1 S2) (tsubstDecls (weakenTrace (XS ty d17) k) S1 d18))) with
        | (dnil) => eq_refl
        | (dcons t22 d19) => (f_equal2 dcons (tsubst_tsubst0_Tm_comm_ind t22 k d17 S1 S2) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty d17 k (HS tm H0)) eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Decls_comm_ind d19 (HS tm k) d17 S1 S2) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty (XS ty d17) k (HS tm H0))) eq_refl eq_refl)))))
      end
    with tsubst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct s0} :
    ((tsubstTm (weakenTrace d17 k) S1 (tsubstTm (weakenTrace X0 k) S2 s0)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d17 S1 S2) (tsubstTm (weakenTrace (XS ty d17) k) S1 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d17 k) S1 (tsubstTm (weakenTrace X0 k) S2 s0)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d17 S1 S2) (tsubstTm (weakenTrace (XS ty d17) k) S1 s0))) with
        | (var x16) => eq_refl
        | (abs T28 t23) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T28 k d17 S1 S2) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d17 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t23 (HS tm k) d17 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d17) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t24 t25) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t24 k d17 S1 S2) (tsubst_tsubst0_Tm_comm_ind t25 k d17 S1 S2))
        | (tabs t23) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d17 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t23 (HS ty k) d17 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d17) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t23 T28) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t23 k d17 S1 S2) (tsubst_tsubst0_Ty_comm_ind T28 k d17 S1 S2))
        | (lett d20 t23) => (f_equal2 lett (tsubst_tsubst0_Decls_comm_ind d20 k d17 S1 S2) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenTrace_append ty d17 k (appendHvl H0 (bind d20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bind d20))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind d20))) d17 S1 S2) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bind d20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d17) k (appendHvl H0 (bind d20)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S3 : Ty) : (forall (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTy d17 S1 (tsubstTy X0 S2 S3)) = (tsubstTy X0 (tsubstTy d17 S1 S2) (tsubstTy (XS ty d17) S1 S3)))) := (tsubst_tsubst0_Ty_comm_ind S3 H0).
    Definition substDecls_substDecls0_comm (d18 : Decls) : (forall (d17 : (Trace tm)) (s0 : Tm) (s1 : Tm) ,
      ((substDecls d17 s0 (substDecls X0 s1 d18)) = (substDecls X0 (substTm d17 s0 s1) (substDecls (XS tm d17) s0 d18)))) := (subst_subst0_Decls_comm_ind d18 H0).
    Definition substTm_substTm0_comm (s2 : Tm) : (forall (d17 : (Trace tm)) (s0 : Tm) (s1 : Tm) ,
      ((substTm d17 s0 (substTm X0 s1 s2)) = (substTm X0 (substTm d17 s0 s1) (substTm (XS tm d17) s0 s2)))) := (subst_subst0_Tm_comm_ind s2 H0).
    Definition substDecls_tsubstDecls0_comm (d18 : Decls) : (forall (d17 : (Trace tm)) (s0 : Tm) (S1 : Ty) ,
      ((substDecls d17 s0 (tsubstDecls X0 S1 d18)) = (tsubstDecls X0 S1 (substDecls (XS ty d17) s0 d18)))) := (subst_tsubst0_Decls_comm_ind d18 H0).
    Definition substTm_tsubstTm0_comm (s1 : Tm) : (forall (d17 : (Trace tm)) (s0 : Tm) (S1 : Ty) ,
      ((substTm d17 s0 (tsubstTm X0 S1 s1)) = (tsubstTm X0 S1 (substTm (XS ty d17) s0 s1)))) := (subst_tsubst0_Tm_comm_ind s1 H0).
    Definition tsubstDecls_substDecls0_comm (d18 : Decls) : (forall (d17 : (Trace ty)) (S1 : Ty) (s0 : Tm) ,
      ((tsubstDecls d17 S1 (substDecls X0 s0 d18)) = (substDecls X0 (tsubstTm d17 S1 s0) (tsubstDecls d17 S1 d18)))) := (tsubst_subst0_Decls_comm_ind d18 H0).
    Definition tsubstTm_substTm0_comm (s1 : Tm) : (forall (d17 : (Trace ty)) (S1 : Ty) (s0 : Tm) ,
      ((tsubstTm d17 S1 (substTm X0 s0 s1)) = (substTm X0 (tsubstTm d17 S1 s0) (tsubstTm d17 S1 s1)))) := (tsubst_subst0_Tm_comm_ind s1 H0).
    Definition tsubstDecls_tsubstDecls0_comm (d18 : Decls) : (forall (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstDecls d17 S1 (tsubstDecls X0 S2 d18)) = (tsubstDecls X0 (tsubstTy d17 S1 S2) (tsubstDecls (XS ty d17) S1 d18)))) := (tsubst_tsubst0_Decls_comm_ind d18 H0).
    Definition tsubstTm_tsubstTm0_comm (s0 : Tm) : (forall (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTm d17 S1 (tsubstTm X0 S2 s0)) = (tsubstTm X0 (tsubstTy d17 S1 S2) (tsubstTm (XS ty d17) S1 s0)))) := (tsubst_tsubst0_Tm_comm_ind s0 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
        ((weakenTy (tsubstTy d17 S1 S2) k) = (tsubstTy (weakenTrace d17 k) S1 (weakenTy S2 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenDecls_substDecls  :
      (forall (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) (d18 : Decls) ,
        ((weakenDecls (substDecls d17 s0 d18) k) = (substDecls (weakenTrace d17 k) s0 (weakenDecls d18 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d17 : (Trace tm)) (s0 : Tm) (s1 : Tm) ,
        ((weakenTm (substTm d17 s0 s1) k) = (substTm (weakenTrace d17 k) s0 (weakenTm s1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenDecls_tsubstDecls  :
      (forall (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (d18 : Decls) ,
        ((weakenDecls (tsubstDecls d17 S1 d18) k) = (tsubstDecls (weakenTrace d17 k) S1 (weakenDecls d18 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d17 : (Trace ty)) (S1 : Ty) (s0 : Tm) ,
        ((weakenTm (tsubstTm d17 S1 s0) k) = (tsubstTm (weakenTrace d17 k) S1 (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite substDecls_substDecls0_comm tsubstDecls_tsubstDecls0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite substDecls_substDecls0_comm tsubstDecls_tsubstDecls0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenDecls_shiftDecls weakenDecls_tshiftDecls weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenDecls_substDecls weakenDecls_tsubstDecls weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
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
    | wfTy_tarr {T28 : Ty}
        (wf : (wfTy k T28)) {T29 : Ty}
        (wf0 : (wfTy k T29)) :
        (wfTy k (tarr T28 T29))
    | wfTy_tall {T30 : Ty}
        (wf : (wfTy (HS ty k) T30)) :
        (wfTy k (tall T30)).
  Inductive wfDecls (k : Hvl) : Decls -> Prop :=
    | wfDecls_dnil :
        (wfDecls k (dnil))
    | wfDecls_dcons {t22 : Tm}
        (wf : (wfTm k t22))
        {d17 : Decls}
        (wf0 : (wfDecls (HS tm k) d17))
        : (wfDecls k (dcons t22 d17))
  with wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x15 : (Index tm))
        (wfi : (wfindex k x15)) :
        (wfTm k (var x15))
    | wfTm_abs {T28 : Ty}
        (wf : (wfTy k T28)) {t22 : Tm}
        (wf0 : (wfTm (HS tm k) t22)) :
        (wfTm k (abs T28 t22))
    | wfTm_app {t23 : Tm}
        (wf : (wfTm k t23)) {t24 : Tm}
        (wf0 : (wfTm k t24)) :
        (wfTm k (app t23 t24))
    | wfTm_tabs {t25 : Tm}
        (wf : (wfTm (HS ty k) t25)) :
        (wfTm k (tabs t25))
    | wfTm_tapp {t26 : Tm}
        (wf : (wfTm k t26)) {T29 : Ty}
        (wf0 : (wfTy k T29)) :
        (wfTm k (tapp t26 T29))
    | wfTm_lett {d17 : Decls}
        (wf : (wfDecls k d17))
        {t27 : Tm}
        (wf0 : (wfTm (appendHvl k (appendHvl H0 (bind d17))) t27))
        : (wfTm k (lett d17 t27)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H18 : (wfTy k (tvar X))) : (wfindex k X) := match H18 in (wfTy _ S1) return match S1 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T1) := match H19 in (wfTy _ S2) return match S2 return Prop with
    | (tarr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T2) := match H19 in (wfTy _ S2) return match S2 return Prop with
    | (tarr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k1 : Hvl) (T : Ty) (H20 : (wfTy k1 (tall T))) : (wfTy (HS ty k1) T) := match H20 in (wfTy _ S3) return match S3 return Prop with
    | (tall T) => (wfTy (HS ty k1) T)
    | _ => True
  end with
    | (wfTy_tall T H4) => H4
    | _ => I
  end.
  Definition inversion_wfDecls_dcons_1 (k3 : Hvl) (t : Tm) (d : Decls) (H22 : (wfDecls k3 (dcons t d))) : (wfTm k3 t) := match H22 in (wfDecls _ d18) return match d18 return Prop with
    | (dcons t d) => (wfTm k3 t)
    | _ => True
  end with
    | (wfDecls_dcons t H5 d H6) => H5
    | _ => I
  end.
  Definition inversion_wfDecls_dcons_2 (k3 : Hvl) (t : Tm) (d : Decls) (H22 : (wfDecls k3 (dcons t d))) : (wfDecls (HS tm k3) d) := match H22 in (wfDecls _ d18) return match d18 return Prop with
    | (dcons t d) => (wfDecls (HS tm k3) d)
    | _ => True
  end with
    | (wfDecls_dcons t H5 d H6) => H6
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k4 : Hvl) (x : (Index tm)) (H23 : (wfTm k4 (var x))) : (wfindex k4 x) := match H23 in (wfTm _ s0) return match s0 return Prop with
    | (var x) => (wfindex k4 x)
    | _ => True
  end with
    | (wfTm_var x H7) => H7
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k5 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k5 (abs T t))) : (wfTy k5 T) := match H24 in (wfTm _ s1) return match s1 return Prop with
    | (abs T t) => (wfTy k5 T)
    | _ => True
  end with
    | (wfTm_abs T H8 t H9) => H8
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k5 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k5 (abs T t))) : (wfTm (HS tm k5) t) := match H24 in (wfTm _ s1) return match s1 return Prop with
    | (abs T t) => (wfTm (HS tm k5) t)
    | _ => True
  end with
    | (wfTm_abs T H8 t H9) => H9
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k6 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k6 (app t1 t2))) : (wfTm k6 t1) := match H25 in (wfTm _ s2) return match s2 return Prop with
    | (app t1 t2) => (wfTm k6 t1)
    | _ => True
  end with
    | (wfTm_app t1 H10 t2 H11) => H10
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k6 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k6 (app t1 t2))) : (wfTm k6 t2) := match H25 in (wfTm _ s2) return match s2 return Prop with
    | (app t1 t2) => (wfTm k6 t2)
    | _ => True
  end with
    | (wfTm_app t1 H10 t2 H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k7 : Hvl) (t : Tm) (H26 : (wfTm k7 (tabs t))) : (wfTm (HS ty k7) t) := match H26 in (wfTm _ s3) return match s3 return Prop with
    | (tabs t) => (wfTm (HS ty k7) t)
    | _ => True
  end with
    | (wfTm_tabs t H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k8 : Hvl) (t : Tm) (T : Ty) (H27 : (wfTm k8 (tapp t T))) : (wfTm k8 t) := match H27 in (wfTm _ s4) return match s4 return Prop with
    | (tapp t T) => (wfTm k8 t)
    | _ => True
  end with
    | (wfTm_tapp t H13 T H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k8 : Hvl) (t : Tm) (T : Ty) (H27 : (wfTm k8 (tapp t T))) : (wfTy k8 T) := match H27 in (wfTm _ s4) return match s4 return Prop with
    | (tapp t T) => (wfTy k8 T)
    | _ => True
  end with
    | (wfTm_tapp t H13 T H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_lett_0 (k9 : Hvl) (d : Decls) (t : Tm) (H28 : (wfTm k9 (lett d t))) : (wfDecls k9 d) := match H28 in (wfTm _ s5) return match s5 return Prop with
    | (lett d t) => (wfDecls k9 d)
    | _ => True
  end with
    | (wfTm_lett d H15 t H16) => H15
    | _ => I
  end.
  Definition inversion_wfTm_lett_1 (k9 : Hvl) (d : Decls) (t : Tm) (H28 : (wfTm k9 (lett d t))) : (wfTm (appendHvl k9 (appendHvl H0 (bind d))) t) := match H28 in (wfTm _ s5) return match s5 return Prop with
    | (lett d t) => (wfTm (appendHvl k9 (appendHvl H0 (bind d))) t)
    | _ => True
  end with
    | (wfTm_lett d H15 t H16) => H16
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfDecls := Induction for wfDecls Sort Prop
  with ind_wfTm := Induction for wfTm Sort Prop.
  Combined Scheme ind_wfDecls_Tm from ind_wfDecls, ind_wfTm.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c1 : (Cutoff tm)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k10 : Hvl)
        :
        (shifthvl_tm C0 k10 (HS tm k10))
    | shifthvl_tm_there_tm
        (c1 : (Cutoff tm)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_tm c1 k10 k11) -> (shifthvl_tm (CS c1) (HS tm k10) (HS tm k11))
    | shifthvl_tm_there_ty
        (c1 : (Cutoff tm)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_tm c1 k10 k11) -> (shifthvl_tm c1 (HS ty k10) (HS ty k11)).
  Inductive shifthvl_ty : (forall (c1 : (Cutoff ty)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k10 : Hvl)
        :
        (shifthvl_ty C0 k10 (HS ty k10))
    | shifthvl_ty_there_tm
        (c1 : (Cutoff ty)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_ty c1 k10 k11) -> (shifthvl_ty c1 (HS tm k10) (HS tm k11))
    | shifthvl_ty_there_ty
        (c1 : (Cutoff ty)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_ty c1 k10 k11) -> (shifthvl_ty (CS c1) (HS ty k10) (HS ty k11)).
  Lemma weaken_shifthvl_tm  :
    (forall (k10 : Hvl) {c1 : (Cutoff tm)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_tm c1 k11 k12) -> (shifthvl_tm (weakenCutofftm c1 k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k10 : Hvl) {c1 : (Cutoff ty)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_ty c1 k11 k12) -> (shifthvl_ty (weakenCutoffty c1 k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c1 : (Cutoff tm)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) (x15 : (Index tm)) ,
      (wfindex k10 x15) -> (wfindex k11 (shiftIndex c1 x15))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c1 : (Cutoff tm)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) (X12 : (Index ty)) ,
      (wfindex k10 X12) -> (wfindex k11 X12)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c1 : (Cutoff ty)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) (x15 : (Index tm)) ,
      (wfindex k10 x15) -> (wfindex k11 x15)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c1 : (Cutoff ty)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) (X12 : (Index ty)) ,
      (wfindex k10 X12) -> (wfindex k11 (tshiftIndex c1 X12))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k10 : Hvl) ,
    (forall (S4 : Ty) (wf : (wfTy k10 S4)) ,
      (forall (c1 : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c1 k10 k11) -> (wfTy k11 S4)))) := (ind_wfTy (fun (k10 : Hvl) (S4 : Ty) (wf : (wfTy k10 S4)) =>
    (forall (c1 : (Cutoff tm)) (k11 : Hvl) ,
      (shifthvl_tm c1 k10 k11) -> (wfTy k11 S4))) (fun (k10 : Hvl) (X12 : (Index ty)) (wfi : (wfindex k10 X12)) (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTy_tvar k11 _ (shift_wfindex_ty c1 k10 k11 ins X12 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTy_tarr k11 (IHT1 c1 k11 (weaken_shifthvl_tm H0 ins)) (IHT2 c1 k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS ty k10) T)) IHT (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTy_tall k11 (IHT c1 (HS ty k11) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k10 : Hvl) ,
    (forall (S4 : Ty) (wf : (wfTy k10 S4)) ,
      (forall (c1 : (Cutoff ty)) (k11 : Hvl) ,
        (shifthvl_ty c1 k10 k11) -> (wfTy k11 (tshiftTy c1 S4))))) := (ind_wfTy (fun (k10 : Hvl) (S4 : Ty) (wf : (wfTy k10 S4)) =>
    (forall (c1 : (Cutoff ty)) (k11 : Hvl) ,
      (shifthvl_ty c1 k10 k11) -> (wfTy k11 (tshiftTy c1 S4)))) (fun (k10 : Hvl) (X12 : (Index ty)) (wfi : (wfindex k10 X12)) (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTy_tvar k11 _ (tshift_wfindex_ty c1 k10 k11 ins X12 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTy_tarr k11 (IHT1 c1 k11 (weaken_shifthvl_ty H0 ins)) (IHT2 c1 k11 (weaken_shifthvl_ty H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS ty k10) T)) IHT (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTy_tall k11 (IHT (CS c1) (HS ty k11) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfDecls_Tm : (forall (k10 : Hvl) ,
    (forall (d19 : Decls) (wf : (wfDecls k10 d19)) ,
      (forall (c1 : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c1 k10 k11) -> (wfDecls k11 (shiftDecls c1 d19)))) /\
    (forall (s6 : Tm) (wf : (wfTm k10 s6)) ,
      (forall (c1 : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c1 k10 k11) -> (wfTm k11 (shiftTm c1 s6))))) := (ind_wfDecls_Tm (fun (k10 : Hvl) (d19 : Decls) (wf : (wfDecls k10 d19)) =>
    (forall (c1 : (Cutoff tm)) (k11 : Hvl) ,
      (shifthvl_tm c1 k10 k11) -> (wfDecls k11 (shiftDecls c1 d19)))) (fun (k10 : Hvl) (s6 : Tm) (wf : (wfTm k10 s6)) =>
    (forall (c1 : (Cutoff tm)) (k11 : Hvl) ,
      (shifthvl_tm c1 k10 k11) -> (wfTm k11 (shiftTm c1 s6)))) (fun (k10 : Hvl) (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfDecls_dnil k11)) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (d : Decls) (wf0 : (wfDecls (HS tm k10) d)) IHd (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfDecls_dcons k11 (IHt c1 k11 (weaken_shifthvl_tm H0 ins)) (IHd (CS c1) (HS tm k11) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k10 : Hvl) (x15 : (Index tm)) (wfi : (wfindex k10 x15)) (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTm_var k11 _ (shift_wfindex_tm c1 k10 k11 ins x15 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS tm k10) t)) IHt (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTm_abs k11 (shift_wfTy k10 T wf c1 k11 (weaken_shifthvl_tm H0 ins)) (IHt (CS c1) (HS tm k11) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTm_app k11 (IHt1 c1 k11 (weaken_shifthvl_tm H0 ins)) (IHt2 c1 k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm (HS ty k10) t)) IHt (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTm_tabs k11 (IHt c1 (HS ty k11) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (T : Ty) (wf0 : (wfTy k10 T)) (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTm_tapp k11 (IHt c1 k11 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k10 T wf0 c1 k11 (weaken_shifthvl_tm H0 ins)))) (fun (k10 : Hvl) (d : Decls) (wf : (wfDecls k10 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k10 (appendHvl H0 (bind d))) t)) IHt (c1 : (Cutoff tm)) (k11 : Hvl) (ins : (shifthvl_tm c1 k10 k11)) =>
    (wfTm_lett k11 (IHd c1 k11 (weaken_shifthvl_tm H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k11) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_bind _ _)))) eq_refl (IHt (weakenCutofftm c1 (appendHvl H0 (bind d))) (appendHvl k11 (appendHvl H0 (bind d))) (weaken_shifthvl_tm (appendHvl H0 (bind d)) ins)))))).
  Lemma shift_wfDecls (k10 : Hvl) :
    (forall (d19 : Decls) (wf : (wfDecls k10 d19)) ,
      (forall (c1 : (Cutoff tm)) (k11 : Hvl) ,
        (shifthvl_tm c1 k10 k11) -> (wfDecls k11 (shiftDecls c1 d19)))).
  Proof.
    pose proof ((shift_wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfTm (k10 : Hvl) :
    (forall (s6 : Tm) (wf0 : (wfTm k10 s6)) ,
      (forall (c2 : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c2 k10 k12) -> (wfTm k12 (shiftTm c2 s6)))).
  Proof.
    pose proof ((shift_wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfDecls_Tm : (forall (k10 : Hvl) ,
    (forall (d19 : Decls) (wf : (wfDecls k10 d19)) ,
      (forall (c1 : (Cutoff ty)) (k11 : Hvl) ,
        (shifthvl_ty c1 k10 k11) -> (wfDecls k11 (tshiftDecls c1 d19)))) /\
    (forall (s6 : Tm) (wf : (wfTm k10 s6)) ,
      (forall (c1 : (Cutoff ty)) (k11 : Hvl) ,
        (shifthvl_ty c1 k10 k11) -> (wfTm k11 (tshiftTm c1 s6))))) := (ind_wfDecls_Tm (fun (k10 : Hvl) (d19 : Decls) (wf : (wfDecls k10 d19)) =>
    (forall (c1 : (Cutoff ty)) (k11 : Hvl) ,
      (shifthvl_ty c1 k10 k11) -> (wfDecls k11 (tshiftDecls c1 d19)))) (fun (k10 : Hvl) (s6 : Tm) (wf : (wfTm k10 s6)) =>
    (forall (c1 : (Cutoff ty)) (k11 : Hvl) ,
      (shifthvl_ty c1 k10 k11) -> (wfTm k11 (tshiftTm c1 s6)))) (fun (k10 : Hvl) (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfDecls_dnil k11)) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (d : Decls) (wf0 : (wfDecls (HS tm k10) d)) IHd (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfDecls_dcons k11 (IHt c1 k11 (weaken_shifthvl_ty H0 ins)) (IHd c1 (HS tm k11) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k10 : Hvl) (x15 : (Index tm)) (wfi : (wfindex k10 x15)) (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTm_var k11 _ (tshift_wfindex_tm c1 k10 k11 ins x15 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS tm k10) t)) IHt (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTm_abs k11 (tshift_wfTy k10 T wf c1 k11 (weaken_shifthvl_ty H0 ins)) (IHt c1 (HS tm k11) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTm_app k11 (IHt1 c1 k11 (weaken_shifthvl_ty H0 ins)) (IHt2 c1 k11 (weaken_shifthvl_ty H0 ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm (HS ty k10) t)) IHt (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTm_tabs k11 (IHt (CS c1) (HS ty k11) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (T : Ty) (wf0 : (wfTy k10 T)) (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTm_tapp k11 (IHt c1 k11 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k10 T wf0 c1 k11 (weaken_shifthvl_ty H0 ins)))) (fun (k10 : Hvl) (d : Decls) (wf : (wfDecls k10 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k10 (appendHvl H0 (bind d))) t)) IHt (c1 : (Cutoff ty)) (k11 : Hvl) (ins : (shifthvl_ty c1 k10 k11)) =>
    (wfTm_lett k11 (IHd c1 k11 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k11) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _)))) eq_refl (IHt (weakenCutoffty c1 (appendHvl H0 (bind d))) (appendHvl k11 (appendHvl H0 (bind d))) (weaken_shifthvl_ty (appendHvl H0 (bind d)) ins)))))).
  Lemma tshift_wfDecls (k10 : Hvl) :
    (forall (d19 : Decls) (wf : (wfDecls k10 d19)) ,
      (forall (c1 : (Cutoff ty)) (k11 : Hvl) ,
        (shifthvl_ty c1 k10 k11) -> (wfDecls k11 (tshiftDecls c1 d19)))).
  Proof.
    pose proof ((tshift_wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfTm (k10 : Hvl) :
    (forall (s6 : Tm) (wf0 : (wfTm k10 s6)) ,
      (forall (c2 : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c2 k10 k12) -> (wfTm k12 (tshiftTm c2 s6)))).
  Proof.
    pose proof ((tshift_wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
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
  Fixpoint weaken_wfDecls (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (d19 : Decls) (wf : (wfDecls k11 d19)) ,
    (wfDecls (appendHvl k11 k10) (weakenDecls d19 k10))) :=
    match k10 return (forall (k11 : Hvl) (d19 : Decls) (wf : (wfDecls k11 d19)) ,
      (wfDecls (appendHvl k11 k10) (weakenDecls d19 k10))) with
      | (H0) => (fun (k11 : Hvl) (d19 : Decls) (wf : (wfDecls k11 d19)) =>
        wf)
      | (HS tm k10) => (fun (k11 : Hvl) (d19 : Decls) (wf : (wfDecls k11 d19)) =>
        (shift_wfDecls (appendHvl k11 k10) (weakenDecls d19 k10) (weaken_wfDecls k10 k11 d19 wf) C0 (HS tm (appendHvl k11 k10)) (shifthvl_tm_here (appendHvl k11 k10))))
      | (HS ty k10) => (fun (k11 : Hvl) (d19 : Decls) (wf : (wfDecls k11 d19)) =>
        (tshift_wfDecls (appendHvl k11 k10) (weakenDecls d19 k10) (weaken_wfDecls k10 k11 d19 wf) C0 (HS ty (appendHvl k11 k10)) (shifthvl_ty_here (appendHvl k11 k10))))
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
  (forall (k12 : Hvl) (S5 : Ty) (k13 : Hvl) (S6 : Ty) ,
    (k12 = k13) -> (S5 = S6) -> (wfTy k12 S5) -> (wfTy k13 S6)).
Proof.
  congruence .
Qed.
Lemma wfDecls_cast  :
  (forall (k12 : Hvl) (d19 : Decls) (k13 : Hvl) (d20 : Decls) ,
    (k12 = k13) -> (d19 = d20) -> (wfDecls k12 d19) -> (wfDecls k13 d20)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k12 : Hvl) (s6 : Tm) (k13 : Hvl) (s7 : Tm) ,
    (k12 = k13) -> (s6 = s7) -> (wfTm k12 s6) -> (wfTm k13 s7)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k10 : Hvl) : (forall (d19 : (Trace tm)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k10 X0 (HS tm k10) k10)
    | substhvl_tm_there_tm
        {d19 : (Trace tm)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_tm k10 d19 k11 k12) -> (substhvl_tm k10 (XS tm d19) (HS tm k11) (HS tm k12))
    | substhvl_tm_there_ty
        {d19 : (Trace tm)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_tm k10 d19 k11 k12) -> (substhvl_tm k10 (XS ty d19) (HS ty k11) (HS ty k12)).
  Inductive substhvl_ty (k10 : Hvl) : (forall (d19 : (Trace ty)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k10 X0 (HS ty k10) k10)
    | substhvl_ty_there_tm
        {d19 : (Trace ty)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_ty k10 d19 k11 k12) -> (substhvl_ty k10 (XS tm d19) (HS tm k11) (HS tm k12))
    | substhvl_ty_there_ty
        {d19 : (Trace ty)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_ty k10 d19 k11 k12) -> (substhvl_ty k10 (XS ty d19) (HS ty k11) (HS ty k12)).
  Lemma weaken_substhvl_tm  :
    (forall {k11 : Hvl} (k10 : Hvl) {d19 : (Trace tm)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_tm k11 d19 k12 k13) -> (substhvl_tm k11 (weakenTrace d19 k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k11 : Hvl} (k10 : Hvl) {d19 : (Trace ty)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_ty k11 d19 k12 k13) -> (substhvl_ty k11 (weakenTrace d19 k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k12 : Hvl} {s6 : Tm} (wft : (wfTm k12 s6)) :
    (forall {d19 : (Trace tm)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_tm k12 d19 k13 k14) -> (forall {x15 : (Index tm)} ,
        (wfindex k13 x15) -> (wfTm k14 (substIndex d19 s6 x15)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k12 : Hvl} {S5 : Ty} (wft : (wfTy k12 S5)) :
    (forall {d19 : (Trace ty)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_ty k12 d19 k13 k14) -> (forall {X12 : (Index ty)} ,
        (wfindex k13 X12) -> (wfTy k14 (tsubstIndex d19 S5 X12)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k12 : Hvl} :
    (forall {d19 : (Trace tm)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_tm k12 d19 k13 k14) -> (forall {X12 : (Index ty)} ,
        (wfindex k13 X12) -> (wfindex k14 X12))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k12 : Hvl} :
    (forall {d19 : (Trace ty)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_ty k12 d19 k13 k14) -> (forall {x15 : (Index tm)} ,
        (wfindex k13 x15) -> (wfindex k14 x15))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k12 : Hvl} : (forall (k13 : Hvl) ,
    (forall (S5 : Ty) (wf0 : (wfTy k13 S5)) ,
      (forall {d19 : (Trace tm)} {k14 : Hvl} ,
        (substhvl_tm k12 d19 k13 k14) -> (wfTy k14 S5)))) := (ind_wfTy (fun (k13 : Hvl) (S5 : Ty) (wf0 : (wfTy k13 S5)) =>
    (forall {d19 : (Trace tm)} {k14 : Hvl} ,
      (substhvl_tm k12 d19 k13 k14) -> (wfTy k14 S5))) (fun (k13 : Hvl) {X12 : (Index ty)} (wfi : (wfindex k13 X12)) {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTy_tvar k14 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k13 : Hvl) (T1 : Ty) (wf0 : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k13 T2)) IHT2 {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTy_tarr k14 (IHT1 (weakenTrace d19 H0) k14 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d19 H0) k14 (weaken_substhvl_tm H0 del)))) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k13) T)) IHT {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTy_tall k14 (IHT (weakenTrace d19 (HS ty H0)) (HS ty k14) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) : (forall (k13 : Hvl) ,
    (forall (S6 : Ty) (wf0 : (wfTy k13 S6)) ,
      (forall {d19 : (Trace ty)} {k14 : Hvl} ,
        (substhvl_ty k12 d19 k13 k14) -> (wfTy k14 (tsubstTy d19 S5 S6))))) := (ind_wfTy (fun (k13 : Hvl) (S6 : Ty) (wf0 : (wfTy k13 S6)) =>
    (forall {d19 : (Trace ty)} {k14 : Hvl} ,
      (substhvl_ty k12 d19 k13 k14) -> (wfTy k14 (tsubstTy d19 S5 S6)))) (fun (k13 : Hvl) {X12 : (Index ty)} (wfi : (wfindex k13 X12)) {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k13 : Hvl) (T1 : Ty) (wf0 : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k13 T2)) IHT2 {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTy_tarr k14 (IHT1 (weakenTrace d19 H0) k14 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d19 H0) k14 (weaken_substhvl_ty H0 del)))) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k13) T)) IHT {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTy_tall k14 (IHT (weakenTrace d19 (HS ty H0)) (HS ty k14) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfDecls_Tm {k12 : Hvl} {s6 : Tm} (wf : (wfTm k12 s6)) : (forall (k13 : Hvl) ,
    (forall (d19 : Decls) (wf0 : (wfDecls k13 d19)) ,
      (forall {d20 : (Trace tm)} {k14 : Hvl} ,
        (substhvl_tm k12 d20 k13 k14) -> (wfDecls k14 (substDecls d20 s6 d19)))) /\
    (forall (s7 : Tm) (wf0 : (wfTm k13 s7)) ,
      (forall {d19 : (Trace tm)} {k14 : Hvl} ,
        (substhvl_tm k12 d19 k13 k14) -> (wfTm k14 (substTm d19 s6 s7))))) := (ind_wfDecls_Tm (fun (k13 : Hvl) (d19 : Decls) (wf0 : (wfDecls k13 d19)) =>
    (forall {d20 : (Trace tm)} {k14 : Hvl} ,
      (substhvl_tm k12 d20 k13 k14) -> (wfDecls k14 (substDecls d20 s6 d19)))) (fun (k13 : Hvl) (s7 : Tm) (wf0 : (wfTm k13 s7)) =>
    (forall {d19 : (Trace tm)} {k14 : Hvl} ,
      (substhvl_tm k12 d19 k13 k14) -> (wfTm k14 (substTm d19 s6 s7)))) (fun (k13 : Hvl) {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfDecls_dnil k14)) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (d : Decls) (wf1 : (wfDecls (HS tm k13) d)) IHd {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfDecls_dcons k14 (IHt (weakenTrace d19 H0) k14 (weaken_substhvl_tm H0 del)) (IHd (weakenTrace d19 (HS tm H0)) (HS tm k14) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k13 : Hvl) {x15 : (Index tm)} (wfi : (wfindex k13 x15)) {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy k13 T)) (t : Tm) (wf1 : (wfTm (HS tm k13) t)) IHt {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTm_abs k14 (substhvl_tm_wfTy k13 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d19 (HS tm H0)) (HS tm k14) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k13 : Hvl) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k13 t2)) IHt2 {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTm_app k14 (IHt1 (weakenTrace d19 H0) k14 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d19 H0) k14 (weaken_substhvl_tm H0 del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k13) t)) IHt {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTm_tabs k14 (IHt (weakenTrace d19 (HS ty H0)) (HS ty k14) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (T : Ty) (wf1 : (wfTy k13 T)) {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTm_tapp k14 (IHt (weakenTrace d19 H0) k14 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k13 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k13 : Hvl) (d : Decls) (wf0 : (wfDecls k13 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bind d))) t)) IHt {d19 : (Trace tm)} {k14 : Hvl} (del : (substhvl_tm k12 d19 k13 k14)) =>
    (wfTm_lett k14 (IHd (weakenTrace d19 H0) k14 (weaken_substhvl_tm H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0)))) eq_refl (IHt (weakenTrace d19 (appendHvl H0 (bind d))) (appendHvl k14 (appendHvl H0 (bind d))) (weaken_substhvl_tm (appendHvl H0 (bind d)) del)))))).
  Lemma substhvl_tm_wfDecls {k12 : Hvl} {s6 : Tm} (wf : (wfTm k12 s6)) (k13 : Hvl) (d19 : Decls) (wf0 : (wfDecls k13 d19)) :
    (forall {d20 : (Trace tm)} {k14 : Hvl} ,
      (substhvl_tm k12 d20 k13 k14) -> (wfDecls k14 (substDecls d20 s6 d19))).
  Proof.
    apply ((substhvl_tm_wfDecls_Tm wf k13)).
    auto .
  Qed.
  Lemma substhvl_tm_wfTm {k12 : Hvl} {s6 : Tm} (wf : (wfTm k12 s6)) (k13 : Hvl) (s7 : Tm) (wf1 : (wfTm k13 s7)) :
    (forall {d21 : (Trace tm)} {k15 : Hvl} ,
      (substhvl_tm k12 d21 k13 k15) -> (wfTm k15 (substTm d21 s6 s7))).
  Proof.
    apply ((substhvl_tm_wfDecls_Tm wf k13)).
    auto .
  Qed.
  Definition substhvl_ty_wfDecls_Tm {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) : (forall (k13 : Hvl) ,
    (forall (d19 : Decls) (wf0 : (wfDecls k13 d19)) ,
      (forall {d20 : (Trace ty)} {k14 : Hvl} ,
        (substhvl_ty k12 d20 k13 k14) -> (wfDecls k14 (tsubstDecls d20 S5 d19)))) /\
    (forall (s6 : Tm) (wf0 : (wfTm k13 s6)) ,
      (forall {d19 : (Trace ty)} {k14 : Hvl} ,
        (substhvl_ty k12 d19 k13 k14) -> (wfTm k14 (tsubstTm d19 S5 s6))))) := (ind_wfDecls_Tm (fun (k13 : Hvl) (d19 : Decls) (wf0 : (wfDecls k13 d19)) =>
    (forall {d20 : (Trace ty)} {k14 : Hvl} ,
      (substhvl_ty k12 d20 k13 k14) -> (wfDecls k14 (tsubstDecls d20 S5 d19)))) (fun (k13 : Hvl) (s6 : Tm) (wf0 : (wfTm k13 s6)) =>
    (forall {d19 : (Trace ty)} {k14 : Hvl} ,
      (substhvl_ty k12 d19 k13 k14) -> (wfTm k14 (tsubstTm d19 S5 s6)))) (fun (k13 : Hvl) {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfDecls_dnil k14)) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (d : Decls) (wf1 : (wfDecls (HS tm k13) d)) IHd {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfDecls_dcons k14 (IHt (weakenTrace d19 H0) k14 (weaken_substhvl_ty H0 del)) (IHd (weakenTrace d19 (HS tm H0)) (HS tm k14) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k13 : Hvl) {x15 : (Index tm)} (wfi : (wfindex k13 x15)) {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTm_var k14 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy k13 T)) (t : Tm) (wf1 : (wfTm (HS tm k13) t)) IHt {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTm_abs k14 (substhvl_ty_wfTy wf k13 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d19 (HS tm H0)) (HS tm k14) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k13 : Hvl) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k13 t2)) IHt2 {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTm_app k14 (IHt1 (weakenTrace d19 H0) k14 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d19 H0) k14 (weaken_substhvl_ty H0 del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k13) t)) IHt {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTm_tabs k14 (IHt (weakenTrace d19 (HS ty H0)) (HS ty k14) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (T : Ty) (wf1 : (wfTy k13 T)) {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTm_tapp k14 (IHt (weakenTrace d19 H0) k14 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k13 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k13 : Hvl) (d : Decls) (wf0 : (wfDecls k13 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bind d))) t)) IHt {d19 : (Trace ty)} {k14 : Hvl} (del : (substhvl_ty k12 d19 k13 k14)) =>
    (wfTm_lett k14 (IHd (weakenTrace d19 H0) k14 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))) eq_refl (IHt (weakenTrace d19 (appendHvl H0 (bind d))) (appendHvl k14 (appendHvl H0 (bind d))) (weaken_substhvl_ty (appendHvl H0 (bind d)) del)))))).
  Lemma substhvl_ty_wfDecls {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) (k13 : Hvl) (d19 : Decls) (wf0 : (wfDecls k13 d19)) :
    (forall {d20 : (Trace ty)} {k14 : Hvl} ,
      (substhvl_ty k12 d20 k13 k14) -> (wfDecls k14 (tsubstDecls d20 S5 d19))).
  Proof.
    apply ((substhvl_ty_wfDecls_Tm wf k13)).
    auto .
  Qed.
  Lemma substhvl_ty_wfTm {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) (k13 : Hvl) (s6 : Tm) (wf1 : (wfTm k13 s6)) :
    (forall {d21 : (Trace ty)} {k15 : Hvl} ,
      (substhvl_ty k12 d21 k13 k15) -> (wfTm k15 (tsubstTm d21 S5 s6))).
  Proof.
    apply ((substhvl_ty_wfDecls_Tm wf k13)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Fixpoint subhvl_tm (k12 : Hvl) {struct k12} :
Prop :=
  match k12 with
    | (H0) => True
    | (HS a k12) => match a with
      | (tm) => (subhvl_tm k12)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k12 : Hvl) (k13 : Hvl) ,
    (subhvl_tm k12) -> (subhvl_tm k13) -> (subhvl_tm (appendHvl k12 k13))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k11 : Hvl) (k10 : Hvl) (S4 : Ty) ,
    (subhvl_tm k11) -> (wfTy (appendHvl k10 k11) (weakenTy S4 k11)) -> (wfTy k10 S4)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H32 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H32
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | etvar (G1 : Env)
    | evar (G1 : Env) (T : Ty).
  Fixpoint appendEnv (G1 : Env) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => G1
      | (etvar G3) => (etvar (appendEnv G1 G3))
      | (evar G3 T) => (evar (appendEnv G1 G3) T)
    end.
  Fixpoint domainEnv (G1 : Env) :
  Hvl :=
    match G1 with
      | (empty) => H0
      | (etvar G2) => (HS ty (domainEnv G2))
      | (evar G2 T) => (HS tm (domainEnv G2))
    end.
  Lemma appendEnv_assoc  :
    (forall (G1 : Env) (G2 : Env) (G3 : Env) ,
      ((appendEnv G1 (appendEnv G2 G3)) = (appendEnv (appendEnv G1 G2) G3))).
  Proof.
    needleGenericAppendEnvAssoc .
  Qed.
  Lemma domainEnv_appendEnv  :
    (forall (G1 : Env) (G2 : Env) ,
      ((domainEnv (appendEnv G1 G2)) = (appendHvl (domainEnv G1) (domainEnv G2)))).
  Proof.
    needleGenericDomainEnvAppendEnv .
  Qed.
  Fixpoint tshiftEnv (c1 : (Cutoff ty)) (G1 : Env) :
  Env :=
    match G1 with
      | (empty) => empty
      | (etvar G2) => (etvar (tshiftEnv c1 G2))
      | (evar G2 T) => (evar (tshiftEnv c1 G2) (tshiftTy (weakenCutoffty c1 (domainEnv G2)) T))
    end.
  Fixpoint shiftEnv (c1 : (Cutoff tm)) (G1 : Env) :
  Env :=
    match G1 with
      | (empty) => empty
      | (etvar G2) => (etvar (shiftEnv c1 G2))
      | (evar G2 T) => (evar (shiftEnv c1 G2) T)
    end.
  Fixpoint weakenEnv (G1 : Env) (k12 : Hvl) {struct k12} :
  Env :=
    match k12 with
      | (H0) => G1
      | (HS tm k12) => (weakenEnv G1 k12)
      | (HS ty k12) => (tshiftEnv C0 (weakenEnv G1 k12))
    end.
  Fixpoint tsubstEnv (d19 : (Trace ty)) (S5 : Ty) (G1 : Env) :
  Env :=
    match G1 with
      | (empty) => empty
      | (etvar G2) => (etvar (tsubstEnv d19 S5 G2))
      | (evar G2 T) => (evar (tsubstEnv d19 S5 G2) (tsubstTy (weakenTrace d19 (domainEnv G2)) S5 T))
    end.
  Fixpoint substEnv (d19 : (Trace tm)) (s6 : Tm) (G1 : Env) :
  Env :=
    match G1 with
      | (empty) => empty
      | (etvar G2) => (etvar (substEnv d19 s6 G2))
      | (evar G2 T) => (evar (substEnv d19 s6 G2) T)
    end.
  Lemma domainEnv_tshiftEnv  :
    (forall (c1 : (Cutoff ty)) (G1 : Env) ,
      ((domainEnv (tshiftEnv c1 G1)) = (domainEnv G1))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_shiftEnv  :
    (forall (c1 : (Cutoff tm)) (G1 : Env) ,
      ((domainEnv (shiftEnv c1 G1)) = (domainEnv G1))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d19 : (Trace ty)) (S5 : Ty) (G1 : Env) ,
      ((domainEnv (tsubstEnv d19 S5 G1)) = (domainEnv G1))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d19 : (Trace tm)) (s6 : Tm) (G1 : Env) ,
      ((domainEnv (substEnv d19 s6 G1)) = (domainEnv G1))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma tshiftEnv_appendEnv  :
      (forall (c1 : (Cutoff ty)) (G1 : Env) (G2 : Env) ,
        ((tshiftEnv c1 (appendEnv G1 G2)) = (appendEnv (tshiftEnv c1 G1) (tshiftEnv (weakenCutoffty c1 (domainEnv G1)) G2)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma shiftEnv_appendEnv  :
      (forall (c1 : (Cutoff tm)) (G1 : Env) (G2 : Env) ,
        ((shiftEnv c1 (appendEnv G1 G2)) = (appendEnv (shiftEnv c1 G1) (shiftEnv (weakenCutofftm c1 (domainEnv G1)) G2)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma tsubstEnv_appendEnv  :
      (forall (d19 : (Trace ty)) (S5 : Ty) (G1 : Env) (G2 : Env) ,
        ((tsubstEnv d19 S5 (appendEnv G1 G2)) = (appendEnv (tsubstEnv d19 S5 G1) (tsubstEnv (weakenTrace d19 (domainEnv G1)) S5 G2)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma substEnv_appendEnv  :
      (forall (d19 : (Trace tm)) (s6 : Tm) (G1 : Env) (G2 : Env) ,
        ((substEnv d19 s6 (appendEnv G1 G2)) = (appendEnv (substEnv d19 s6 G1) (substEnv (weakenTrace d19 (domainEnv G1)) s6 G2)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S5 : Ty) (k12 : Hvl) (k13 : Hvl) ,
      ((weakenTy (weakenTy S5 k12) k13) = (weakenTy S5 (appendHvl k12 k13)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenDecls_append  :
    (forall (d19 : Decls) (k12 : Hvl) (k13 : Hvl) ,
      ((weakenDecls (weakenDecls d19 k12) k13) = (weakenDecls d19 (appendHvl k12 k13)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s6 : Tm) (k12 : Hvl) (k13 : Hvl) ,
      ((weakenTm (weakenTm s6 k12) k13) = (weakenTm s6 (appendHvl k12 k13)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G1 : Env}
          : (lookup_etvar (etvar G1) I0)
      | lookup_etvar_there_etvar
          {G1 : Env} {X12 : (Index ty)} :
          (lookup_etvar G1 X12) -> (lookup_etvar (etvar G1) (IS X12))
      | lookup_etvar_there_evar
          {G1 : Env} {X12 : (Index ty)}
          (T28 : Ty) :
          (lookup_etvar G1 X12) -> (lookup_etvar (evar G1 T28) X12).
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G1 : Env}
          (T28 : Ty) :
          (wfTy (domainEnv G1) T28) -> (lookup_evar (evar G1 T28) I0 T28)
      | lookup_evar_there_etvar
          {G1 : Env} {x15 : (Index tm)}
          (T29 : Ty) :
          (lookup_evar G1 x15 T29) -> (lookup_evar (etvar G1) x15 (tshiftTy C0 T29))
      | lookup_evar_there_evar
          {G1 : Env} {x15 : (Index tm)}
          (T29 : Ty) (T30 : Ty) :
          (lookup_evar G1 x15 T29) -> (lookup_evar (evar G1 T30) (IS x15) T29).
    Lemma lookup_evar_inversion_here  :
      (forall (G1 : Env) (T29 : Ty) (T30 : Ty) ,
        (lookup_evar (evar G1 T29) I0 T30) -> (T29 = T30)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G1 : Env} {x15 : (Index tm)} ,
        (forall (T29 : Ty) ,
          (lookup_evar G1 x15 T29) -> (forall (T30 : Ty) ,
            (lookup_evar G1 x15 T30) -> (T29 = T30)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G1 : Env} {x15 : (Index tm)} (T29 : Ty) ,
        (lookup_evar G1 x15 T29) -> (wfTy (domainEnv G1) T29)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G1 : Env} (G2 : Env) {X12 : (Index ty)} ,
        (lookup_etvar G1 X12) -> (lookup_etvar (appendEnv G1 G2) (weakenIndexty X12 (domainEnv G2)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G1 : Env} (G2 : Env) {x15 : (Index tm)} (T29 : Ty) ,
        (lookup_evar G1 x15 T29) -> (lookup_evar (appendEnv G1 G2) (weakenIndextm x15 (domainEnv G2)) (weakenTy T29 (domainEnv G2)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G1 : Env} {X12 : (Index ty)} ,
        (lookup_etvar G1 X12) -> (wfindex (domainEnv G1) X12)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G1 : Env} {x15 : (Index tm)} (T31 : Ty) ,
        (lookup_evar G1 x15 T31) -> (wfindex (domainEnv G1) x15)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G1 : Env}
        : (shift_etvar C0 G1 (etvar G1))
    | shiftetvar_there_etvar
        {c1 : (Cutoff ty)} {G1 : Env}
        {G2 : Env} :
        (shift_etvar c1 G1 G2) -> (shift_etvar (CS c1) (etvar G1) (etvar G2))
    | shiftetvar_there_evar
        {c1 : (Cutoff ty)} {G1 : Env}
        {G2 : Env} {T : Ty} :
        (shift_etvar c1 G1 G2) -> (shift_etvar c1 (evar G1 T) (evar G2 (tshiftTy c1 T))).
  Lemma weaken_shift_etvar  :
    (forall (G1 : Env) {c1 : (Cutoff ty)} {G2 : Env} {G3 : Env} ,
      (shift_etvar c1 G2 G3) -> (shift_etvar (weakenCutoffty c1 (domainEnv G1)) (appendEnv G2 G1) (appendEnv G3 (tshiftEnv c1 G1)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G1 : Env}
        {T29 : Ty} :
        (shift_evar C0 G1 (evar G1 T29))
    | shiftevar_there_etvar
        {c1 : (Cutoff tm)} {G1 : Env}
        {G2 : Env} :
        (shift_evar c1 G1 G2) -> (shift_evar c1 (etvar G1) (etvar G2))
    | shiftevar_there_evar
        {c1 : (Cutoff tm)} {G1 : Env}
        {G2 : Env} {T : Ty} :
        (shift_evar c1 G1 G2) -> (shift_evar (CS c1) (evar G1 T) (evar G2 T)).
  Lemma weaken_shift_evar  :
    (forall (G1 : Env) {c1 : (Cutoff tm)} {G2 : Env} {G3 : Env} ,
      (shift_evar c1 G2 G3) -> (shift_evar (weakenCutofftm c1 (domainEnv G1)) (appendEnv G2 G1) (appendEnv G3 G1))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c1 : (Cutoff ty)} {G1 : Env} {G2 : Env} ,
      (shift_etvar c1 G1 G2) -> (shifthvl_ty c1 (domainEnv G1) (domainEnv G2))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c1 : (Cutoff tm)} {G1 : Env} {G2 : Env} ,
      (shift_evar c1 G1 G2) -> (shifthvl_tm c1 (domainEnv G1) (domainEnv G2))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_etvar (G1 : Env) (S5 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G1 S5 X0 (etvar G1) G1)
    | subst_etvar_there_etvar
        {d19 : (Trace ty)} {G2 : Env}
        {G3 : Env} :
        (subst_etvar G1 S5 d19 G2 G3) -> (subst_etvar G1 S5 (XS ty d19) (etvar G2) (etvar G3))
    | subst_etvar_there_evar
        {d19 : (Trace ty)} {G2 : Env}
        {G3 : Env} (T29 : Ty) :
        (subst_etvar G1 S5 d19 G2 G3) -> (subst_etvar G1 S5 (XS tm d19) (evar G2 T29) (evar G3 (tsubstTy d19 S5 T29))).
  Lemma weaken_subst_etvar {G1 : Env} {S5 : Ty} :
    (forall (G2 : Env) {d19 : (Trace ty)} {G3 : Env} {G4 : Env} ,
      (subst_etvar G1 S5 d19 G3 G4) -> (subst_etvar G1 S5 (weakenTrace d19 (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 (tsubstEnv d19 S5 G2)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_evar (G1 : Env) (T29 : Ty) (s6 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G1 T29 s6 X0 (evar G1 T29) G1)
    | subst_evar_there_etvar
        {d19 : (Trace tm)} {G2 : Env}
        {G3 : Env} :
        (subst_evar G1 T29 s6 d19 G2 G3) -> (subst_evar G1 T29 s6 (XS ty d19) (etvar G2) (etvar G3))
    | subst_evar_there_evar
        {d19 : (Trace tm)} {G2 : Env}
        {G3 : Env} (T30 : Ty) :
        (subst_evar G1 T29 s6 d19 G2 G3) -> (subst_evar G1 T29 s6 (XS tm d19) (evar G2 T30) (evar G3 T30)).
  Lemma weaken_subst_evar {G1 : Env} (T29 : Ty) {s6 : Tm} :
    (forall (G2 : Env) {d19 : (Trace tm)} {G3 : Env} {G4 : Env} ,
      (subst_evar G1 T29 s6 d19 G3 G4) -> (subst_evar G1 T29 s6 (weakenTrace d19 (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 G2))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_etvar_substhvl_ty {G1 : Env} {S5 : Ty} :
    (forall {d19 : (Trace ty)} {G2 : Env} {G3 : Env} ,
      (subst_etvar G1 S5 d19 G2 G3) -> (substhvl_ty (domainEnv G1) d19 (domainEnv G2) (domainEnv G3))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_evar_substhvl_tm {G1 : Env} {s6 : Tm} (T29 : Ty) :
    (forall {d19 : (Trace tm)} {G2 : Env} {G3 : Env} ,
      (subst_evar G1 T29 s6 d19 G2 G3) -> (substhvl_tm (domainEnv G1) d19 (domainEnv G2) (domainEnv G3))).
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
Lemma weaken_lookup_etvar_here  :
  (forall {G1 : Env} (G2 : Env) ,
    (lookup_etvar (appendEnv (etvar G1) G2) (weakenIndexty I0 (domainEnv G2)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_evar_here  :
  (forall {G1 : Env} (G2 : Env) {T29 : Ty} (wf : (wfTy (domainEnv G1) T29)) ,
    (lookup_evar (appendEnv (evar G1 T29) G2) (weakenIndextm I0 (domainEnv G2)) (weakenTy T29 (domainEnv G2)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfDecls wfTm wfTy : infra.
 Hint Constructors wfDecls wfTm wfTy : wf.
 Hint Extern 10 ((wfDecls _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H32 : (wfTy _ (tvar _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (tarr _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (tall _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Extern 2 ((wfDecls _ _)) => match goal with
  | H32 : (wfDecls _ (dnil)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfDecls _ (dcons _ _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H32 : (wfTm _ (var _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (abs _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (app _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (tabs _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (tapp _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (lett _ _)) |- _ => inversion H32; subst; clear H32
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
Lemma shift_etvar_lookup_etvar  :
  (forall {c1 : (Cutoff ty)} {G1 : Env} {G2 : Env} (ins : (shift_etvar c1 G1 G2)) {X12 : (Index ty)} ,
    (lookup_etvar G1 X12) -> (lookup_etvar G2 (tshiftIndex c1 X12))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c1 : (Cutoff ty)} {G1 : Env} {G2 : Env} (ins : (shift_etvar c1 G1 G2)) {x15 : (Index tm)} {T29 : Ty} ,
    (lookup_evar G1 x15 T29) -> (lookup_evar G2 x15 (tshiftTy c1 T29))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c1 : (Cutoff tm)} {G1 : Env} {G2 : Env} (ins : (shift_evar c1 G1 G2)) {X12 : (Index ty)} ,
    (lookup_etvar G1 X12) -> (lookup_etvar G2 X12)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_evar  :
  (forall {c1 : (Cutoff tm)} {G1 : Env} {G2 : Env} (ins : (shift_evar c1 G1 G2)) {x15 : (Index tm)} {T29 : Ty} ,
    (lookup_evar G1 x15 T29) -> (lookup_evar G2 (shiftIndex c1 x15) T29)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_etvar_lookup_evar {G1 : Env} {S5 : Ty} (wf : (wfTy (domainEnv G1) S5)) :
  (forall {d19 : (Trace ty)} {G2 : Env} {G3 : Env} (sub : (subst_etvar G1 S5 d19 G2 G3)) {x15 : (Index tm)} (T30 : Ty) ,
    (lookup_evar G2 x15 T30) -> (lookup_evar G3 x15 (tsubstTy d19 S5 T30))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_evar_lookup_etvar {G1 : Env} (T30 : Ty) {s6 : Tm} :
  (forall {d19 : (Trace tm)} {G2 : Env} {G3 : Env} (sub : (subst_evar G1 T30 s6 d19 G2 G3)) {X12 : (Index ty)} ,
    (lookup_etvar G2 X12) -> (lookup_etvar G3 X12)).
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
    | (tarr T28 T29) => (plus 1 (plus (size_Ty T28) (size_Ty T29)))
    | (tall T30) => (plus 1 (size_Ty T30))
  end.
Fixpoint size_Decls (d11 : Decls) {struct d11} :
nat :=
  match d11 with
    | (dnil) => 1
    | (dcons t22 d12) => (plus 1 (plus (size_Tm t22) (size_Decls d12)))
  end
with size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x15) => 1
    | (abs T28 t22) => (plus 1 (plus (size_Ty T28) (size_Tm t22)))
    | (app t23 t24) => (plus 1 (plus (size_Tm t23) (size_Tm t24)))
    | (tabs t25) => (plus 1 (size_Tm t25))
    | (tapp t26 T29) => (plus 1 (plus (size_Tm t26) (size_Ty T29)))
    | (lett d11 t27) => (plus 1 (plus (size_Decls d11) (size_Tm t27)))
  end.
Fixpoint tshift_size_Ty (S1 : Ty) (c1 : (Cutoff ty)) {struct S1} :
((size_Ty (tshiftTy c1 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (tshiftTy c1 S1)) = (size_Ty S1)) with
    | (tvar _) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c1) (tshift_size_Ty T2 c1)))
    | (tall T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c1)))
  end.
Fixpoint shift_size_Decls (d17 : Decls) (c1 : (Cutoff tm)) {struct d17} :
((size_Decls (shiftDecls c1 d17)) = (size_Decls d17)) :=
  match d17 return ((size_Decls (shiftDecls c1 d17)) = (size_Decls d17)) with
    | (dnil) => eq_refl
    | (dcons t d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c1) (shift_size_Decls d (CS c1))))
  end
with shift_size_Tm (s0 : Tm) (c1 : (Cutoff tm)) {struct s0} :
((size_Tm (shiftTm c1 s0)) = (size_Tm s0)) :=
  match s0 return ((size_Tm (shiftTm c1 s0)) = (size_Tm s0)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c1))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c1) (shift_size_Tm t2 c1)))
    | (tabs t) => (f_equal2 plus eq_refl (shift_size_Tm t c1))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c1) eq_refl))
    | (lett d t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Decls d c1) (shift_size_Tm t (weakenCutofftm c1 (appendHvl H0 (bind d))))))
  end.
Fixpoint tshift_size_Decls (d17 : Decls) (c1 : (Cutoff ty)) {struct d17} :
((size_Decls (tshiftDecls c1 d17)) = (size_Decls d17)) :=
  match d17 return ((size_Decls (tshiftDecls c1 d17)) = (size_Decls d17)) with
    | (dnil) => eq_refl
    | (dcons t d) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c1) (tshift_size_Decls d c1)))
  end
with tshift_size_Tm (s0 : Tm) (c1 : (Cutoff ty)) {struct s0} :
((size_Tm (tshiftTm c1 s0)) = (size_Tm s0)) :=
  match s0 return ((size_Tm (tshiftTm c1 s0)) = (size_Tm s0)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c1) (tshift_size_Tm t c1)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c1) (tshift_size_Tm t2 c1)))
    | (tabs t) => (f_equal2 plus eq_refl (tshift_size_Tm t (CS c1)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c1) (tshift_size_Ty T c1)))
    | (lett d t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Decls d c1) (tshift_size_Tm t (weakenCutoffty c1 (appendHvl H0 (bind d))))))
  end.
 Hint Rewrite shift_size_Decls tshift_size_Decls shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Decls tshift_size_Decls shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Decls  :
  (forall (k : Hvl) (d17 : Decls) ,
    ((size_Decls (weakenDecls d17 k)) = (size_Decls d17))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k : Hvl) (s0 : Tm) ,
    ((size_Tm (weakenTm s0 k)) = (size_Tm s0))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k : Hvl) (S1 : Ty) ,
    ((size_Ty (weakenTy S1 k)) = (size_Ty S1))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Decls weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Decls weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive DTyping (G1 : Env) : Decls -> Env -> Prop :=
  | T_DNil :
      (DTyping G1 (dnil) empty)
  | T_DCons (T : Ty) (d : Decls)
      (t : Tm) (G0 : Env)
      (jm5 : (Typing G1 t T))
      (wd : (DTyping (evar G1 T) d G0))
      :
      (DTyping G1 (dcons t d) (appendEnv (evar empty T) G0))
with Typing (G1 : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index tm))
      (lk : (lookup_evar G1 x T))
      (H20 : (wfTy (domainEnv G1) T))
      (H21 : (wfindex (domainEnv G1) x))
      : (Typing G1 (var x) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G1 T1) t (weakenTy T2 (HS tm H0))))
      (H22 : (wfTy (domainEnv G1) T1))
      (H23 : (wfTy (domainEnv G1) T2))
      :
      (Typing G1 (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm0 : (Typing G1 t1 (tarr T11 T12)))
      (jm1 : (Typing G1 t2 T11)) :
      (Typing G1 (app t1 t2) T12)
  | T_Tabs (T : Ty) (t : Tm)
      (jm2 : (Typing (etvar G1) t T))
      : (Typing G1 (tabs t) (tall T))
  | T_Tapp (T12 : Ty) (T2 : Ty)
      (t1 : Tm)
      (jm3 : (Typing G1 t1 (tall T12)))
      (H32 : (wfTy (domainEnv G1) T2))
      :
      (Typing G1 (tapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Let (T : Ty) (d : Decls)
      (t : Tm) (G : Env)
      (wd : (DTyping G1 d G))
      (jm4 : (Typing (appendEnv G1 (appendEnv empty G)) t (weakenTy T (appendHvl H0 (bind d)))))
      (H34 : (wfTy (domainEnv G1) T))
      : (Typing G1 (lett d t) T).
Fixpoint domain_DTyping_bind (G2 : Env) (d20 : Decls) (G3 : Env) (wd4 : (DTyping G2 d20 G3)) :
((domainEnv G3) = (bind d20)) :=
  match wd4 in (DTyping _ d20 G3) return ((domainEnv G3) = (bind d20)) with
    | (T_DNil) => (eq_refl H0)
    | (T_DCons T31 d19 t22 G1 jm6 wd3) => (eq_trans (domainEnv_appendEnv (evar empty T31) G1) (f_equal2 appendHvl (eq_refl (HS tm H0)) (domain_DTyping_bind (evar G2 T31) d19 G1 wd3)))
  end.
Lemma DTyping_cast  :
  (forall (G1 : Env) (d19 : Decls) (G3 : Env) (G2 : Env) (d20 : Decls) (G4 : Env) ,
    (G1 = G2) -> (d19 = d20) -> (G3 = G4) -> (DTyping G1 d19 G3) -> (DTyping G2 d20 G4)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G1 : Env) (t22 : Tm) (T31 : Ty) (G2 : Env) (t23 : Tm) (T32 : Ty) ,
    (G1 = G2) -> (t22 = t23) -> (T31 = T32) -> (Typing G1 t22 T31) -> (Typing G2 t23 T32)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_DTyping (G7 : Env) (d21 : Decls) (G8 : Env) (wd5 : (DTyping G7 d21 G8)) :
(forall (c1 : (Cutoff tm)) (G9 : Env) (H42 : (shift_evar c1 G7 G9)) ,
  (DTyping G9 (shiftDecls c1 d21) G8)) :=
  match wd5 in (DTyping _ d21 G8) return (forall (c1 : (Cutoff tm)) (G9 : Env) (H42 : (shift_evar c1 G7 G9)) ,
    (DTyping G9 (shiftDecls c1 d21) G8)) with
    | (T_DNil) => (fun (c1 : (Cutoff tm)) (G9 : Env) (H42 : (shift_evar c1 G7 G9)) =>
      (T_DNil G9))
    | (T_DCons T34 d20 t23 G6 jm7 wd4) => (fun (c1 : (Cutoff tm)) (G9 : Env) (H42 : (shift_evar c1 G7 G9)) =>
      (DTyping_cast G9 _ _ G9 (shiftDecls c1 (dcons t23 d20)) _ eq_refl eq_refl (eq_sym eq_refl) (T_DCons G9 T34 (shiftDecls (CS c1) d20) (shiftTm c1 t23) G6 (shift_evar_Typing G7 t23 T34 jm7 c1 G9 (weaken_shift_evar empty H42)) (shift_evar_DTyping (evar G7 T34) d20 G6 wd4 (CS c1) (evar G9 T34) (weaken_shift_evar (evar empty T34) H42)))))
  end
with shift_evar_Typing (G7 : Env) (t26 : Tm) (T39 : Ty) (jm13 : (Typing G7 t26 T39)) :
(forall (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) ,
  (Typing G8 (shiftTm c1 t26) T39)) :=
  match jm13 in (Typing _ t26 T39) return (forall (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) ,
    (Typing G8 (shiftTm c1 t26) T39)) with
    | (T_Var T34 x17 lk0 H38 H39) => (fun (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) =>
      (T_Var G8 T34 (shiftIndex c1 x17) (shift_evar_lookup_evar H57 lk0) (shift_wfTy _ _ H38 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H57))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H57)) _ H39)))
    | (T_Abs T35 T38 t23 jm7 H40 H41) => (fun (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) =>
      (T_Abs G8 T35 T38 (shiftTm (CS c1) t23) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G7 T35) t23 (weakenTy T38 (HS tm H0)) jm7 (CS c1) (evar G8 T35) (weaken_shift_evar (evar empty T35) H57))) (shift_wfTy _ _ H40 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H57))) (shift_wfTy _ _ H41 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H57)))))
    | (T_App T36 T37 t24 t25 jm8 jm9) => (fun (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) =>
      (T_App G8 T36 T37 (shiftTm c1 t24) (shiftTm c1 t25) (shift_evar_Typing G7 t24 (tarr T36 T37) jm8 c1 G8 (weaken_shift_evar empty H57)) (shift_evar_Typing G7 t25 T36 jm9 c1 G8 (weaken_shift_evar empty H57))))
    | (T_Tabs T34 t23 jm10) => (fun (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) =>
      (T_Tabs G8 T34 (shiftTm c1 t23) (shift_evar_Typing (etvar G7) t23 T34 jm10 c1 (etvar G8) (weaken_shift_evar (etvar empty) H57))))
    | (T_Tapp T37 T38 t24 jm11 H50) => (fun (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) =>
      (T_Tapp G8 T37 T38 (shiftTm c1 t24) (shift_evar_Typing G7 t24 (tall T37) jm11 c1 G8 (weaken_shift_evar empty H57)) (shift_wfTy _ _ H50 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H57)))))
    | (T_Let T34 d20 t23 G6 wd4 jm12 H52) => (fun (c1 : (Cutoff tm)) (G8 : Env) (H57 : (shift_evar c1 G7 G8)) =>
      (T_Let G8 T34 (shiftDecls c1 d20) (shiftTm (weakenCutofftm c1 (appendHvl H0 (bind d20))) t23) G6 (shift_evar_DTyping G7 d20 G6 wd4 c1 G8 (weaken_shift_evar empty H57)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal2 shiftTm (f_equal2 weakenCutofftm eq_refl (eq_trans (domainEnv_appendEnv empty G6) (f_equal2 appendHvl (eq_refl H0) (domain_DTyping_bind G7 d20 G6 wd4)))) eq_refl) (eq_trans eq_refl (eq_trans (eq_sym eq_refl) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_bind _ _)))))) (shift_evar_Typing (appendEnv G7 (appendEnv empty G6)) t23 (weakenTy T34 (appendHvl H0 (bind d20))) jm12 (weakenCutofftm c1 (domainEnv (appendEnv empty G6))) (appendEnv G8 (appendEnv empty G6)) (weaken_shift_evar (appendEnv empty G6) H57))) (shift_wfTy _ _ H52 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H57)))))
  end.
Fixpoint shift_etvar_DTyping (G7 : Env) (d21 : Decls) (G8 : Env) (wd5 : (DTyping G7 d21 G8)) :
(forall (c1 : (Cutoff ty)) (G9 : Env) (H42 : (shift_etvar c1 G7 G9)) ,
  (DTyping G9 (tshiftDecls c1 d21) (tshiftEnv c1 G8))) :=
  match wd5 in (DTyping _ d21 G8) return (forall (c1 : (Cutoff ty)) (G9 : Env) (H42 : (shift_etvar c1 G7 G9)) ,
    (DTyping G9 (tshiftDecls c1 d21) (tshiftEnv c1 G8))) with
    | (T_DNil) => (fun (c1 : (Cutoff ty)) (G9 : Env) (H42 : (shift_etvar c1 G7 G9)) =>
      (T_DNil G9))
    | (T_DCons T34 d20 t23 G6 jm7 wd4) => (fun (c1 : (Cutoff ty)) (G9 : Env) (H42 : (shift_etvar c1 G7 G9)) =>
      (DTyping_cast G9 _ _ G9 (tshiftDecls c1 (dcons t23 d20)) _ eq_refl eq_refl (eq_sym (tshiftEnv_appendEnv c1 (evar empty T34) G6)) (T_DCons G9 (tshiftTy c1 T34) (tshiftDecls c1 d20) (tshiftTm c1 t23) (tshiftEnv c1 G6) (shift_etvar_Typing G7 t23 T34 jm7 c1 G9 (weaken_shift_etvar empty H42)) (shift_etvar_DTyping (evar G7 T34) d20 G6 wd4 c1 (evar G9 (tshiftTy c1 T34)) (weaken_shift_etvar (evar empty T34) H42)))))
  end
with shift_etvar_Typing (G7 : Env) (t26 : Tm) (T39 : Ty) (jm13 : (Typing G7 t26 T39)) :
(forall (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) ,
  (Typing G8 (tshiftTm c1 t26) (tshiftTy c1 T39))) :=
  match jm13 in (Typing _ t26 T39) return (forall (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) ,
    (Typing G8 (tshiftTm c1 t26) (tshiftTy c1 T39))) with
    | (T_Var T34 x17 lk0 H38 H39) => (fun (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) =>
      (T_Var G8 (tshiftTy c1 T34) x17 (shift_etvar_lookup_evar H57 lk0) (tshift_wfTy _ _ H38 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H57))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H57)) _ H39)))
    | (T_Abs T35 T38 t23 jm7 H40 H41) => (fun (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) =>
      (T_Abs G8 (tshiftTy c1 T35) (tshiftTy c1 T38) (tshiftTm c1 t23) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c1 T38)) (shift_etvar_Typing (evar G7 T35) t23 (weakenTy T38 (HS tm H0)) jm7 c1 (evar G8 (tshiftTy c1 T35)) (weaken_shift_etvar (evar empty T35) H57))) (tshift_wfTy _ _ H40 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H57))) (tshift_wfTy _ _ H41 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H57)))))
    | (T_App T36 T37 t24 t25 jm8 jm9) => (fun (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) =>
      (T_App G8 (tshiftTy c1 T36) (tshiftTy c1 T37) (tshiftTm c1 t24) (tshiftTm c1 t25) (shift_etvar_Typing G7 t24 (tarr T36 T37) jm8 c1 G8 (weaken_shift_etvar empty H57)) (shift_etvar_Typing G7 t25 T36 jm9 c1 G8 (weaken_shift_etvar empty H57))))
    | (T_Tabs T34 t23 jm10) => (fun (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) =>
      (T_Tabs G8 (tshiftTy (CS c1) T34) (tshiftTm (CS c1) t23) (shift_etvar_Typing (etvar G7) t23 T34 jm10 (CS c1) (etvar G8) (weaken_shift_etvar (etvar empty) H57))))
    | (T_Tapp T37 T38 t24 jm11 H50) => (fun (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) =>
      (Typing_cast G8 _ _ G8 (tshiftTm c1 (tapp t24 T38)) (tshiftTy c1 (tsubstTy X0 T38 T37)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T37 c1 T38)) (T_Tapp G8 (tshiftTy (CS c1) T37) (tshiftTy c1 T38) (tshiftTm c1 t24) (shift_etvar_Typing G7 t24 (tall T37) jm11 c1 G8 (weaken_shift_etvar empty H57)) (tshift_wfTy _ _ H50 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H57))))))
    | (T_Let T34 d20 t23 G6 wd4 jm12 H52) => (fun (c1 : (Cutoff ty)) (G8 : Env) (H57 : (shift_etvar c1 G7 G8)) =>
      (T_Let G8 (tshiftTy c1 T34) (tshiftDecls c1 d20) (tshiftTm (weakenCutoffty c1 (appendHvl H0 (bind d20))) t23) (tshiftEnv c1 G6) (shift_etvar_DTyping G7 d20 G6 wd4 c1 G8 (weaken_shift_etvar empty H57)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tshiftEnv_appendEnv c1 empty G6)) (f_equal2 tshiftTm (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G6) (f_equal2 appendHvl (eq_refl H0) (domain_DTyping_bind G7 d20 G6 wd4)))) eq_refl) (eq_trans (f_equal2 tshiftTy (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G6) (f_equal2 appendHvl (eq_refl H0) (domain_DTyping_bind G7 d20 G6 wd4)))) eq_refl) (eq_trans (eq_sym (weakenTy_tshiftTy (appendHvl H0 (bind d20)) c1 T34)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _)))))) (shift_etvar_Typing (appendEnv G7 (appendEnv empty G6)) t23 (weakenTy T34 (appendHvl H0 (bind d20))) jm12 (weakenCutoffty c1 (domainEnv (appendEnv empty G6))) (appendEnv G8 (tshiftEnv c1 (appendEnv empty G6))) (weaken_shift_etvar (appendEnv empty G6) H57))) (tshift_wfTy _ _ H52 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H57)))))
  end.
 Hint Resolve shift_evar_DTyping shift_etvar_DTyping shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_DTyping shift_etvar_DTyping shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_DTyping (G1 : Env) :
(forall (G2 : Env) (d19 : Decls) (G3 : Env) (wd3 : (DTyping G2 d19 G3)) ,
  (DTyping (appendEnv G2 G1) (weakenDecls d19 (domainEnv G1)) (weakenEnv G3 (domainEnv G1)))) :=
  match G1 return (forall (G2 : Env) (d19 : Decls) (G3 : Env) (wd3 : (DTyping G2 d19 G3)) ,
    (DTyping (appendEnv G2 G1) (weakenDecls d19 (domainEnv G1)) (weakenEnv G3 (domainEnv G1)))) with
    | (empty) => (fun (G2 : Env) (d19 : Decls) (G3 : Env) (wd3 : (DTyping G2 d19 G3)) =>
      wd3)
    | (etvar G1) => (fun (G2 : Env) (d19 : Decls) (G3 : Env) (wd3 : (DTyping G2 d19 G3)) =>
      (shift_etvar_DTyping (appendEnv G2 G1) (weakenDecls d19 (domainEnv G1)) (weakenEnv G3 (domainEnv G1)) (weaken_DTyping G1 G2 d19 G3 wd3) C0 (etvar (appendEnv G2 G1)) shift_etvar_here))
    | (evar G1 T31) => (fun (G2 : Env) (d19 : Decls) (G3 : Env) (wd3 : (DTyping G2 d19 G3)) =>
      (shift_evar_DTyping (appendEnv G2 G1) (weakenDecls d19 (domainEnv G1)) (weakenEnv G3 (domainEnv G1)) (weaken_DTyping G1 G2 d19 G3 wd3) C0 (evar (appendEnv G2 G1) T31) shift_evar_here))
  end.
Fixpoint weaken_Typing (G4 : Env) :
(forall (G5 : Env) (t22 : Tm) (T32 : Ty) (jm6 : (Typing G5 t22 T32)) ,
  (Typing (appendEnv G5 G4) (weakenTm t22 (domainEnv G4)) (weakenTy T32 (domainEnv G4)))) :=
  match G4 return (forall (G5 : Env) (t22 : Tm) (T32 : Ty) (jm6 : (Typing G5 t22 T32)) ,
    (Typing (appendEnv G5 G4) (weakenTm t22 (domainEnv G4)) (weakenTy T32 (domainEnv G4)))) with
    | (empty) => (fun (G5 : Env) (t22 : Tm) (T32 : Ty) (jm6 : (Typing G5 t22 T32)) =>
      jm6)
    | (etvar G4) => (fun (G5 : Env) (t22 : Tm) (T32 : Ty) (jm6 : (Typing G5 t22 T32)) =>
      (shift_etvar_Typing (appendEnv G5 G4) (weakenTm t22 (domainEnv G4)) (weakenTy T32 (domainEnv G4)) (weaken_Typing G4 G5 t22 T32 jm6) C0 (etvar (appendEnv G5 G4)) shift_etvar_here))
    | (evar G4 T33) => (fun (G5 : Env) (t22 : Tm) (T32 : Ty) (jm6 : (Typing G5 t22 T32)) =>
      (shift_evar_Typing (appendEnv G5 G4) (weakenTm t22 (domainEnv G4)) (weakenTy T32 (domainEnv G4)) (weaken_Typing G4 G5 t22 T32 jm6) C0 (evar (appendEnv G5 G4) T33) shift_evar_here))
  end.
Fixpoint DTyping_wf_0 (G1 : Env) (d20 : Decls) (G6 : Env) (wd4 : (DTyping G1 d20 G6)) {struct wd4} :
(wfDecls (domainEnv G1) d20) :=
  match wd4 in (DTyping _ d20 G6) return (wfDecls (domainEnv G1) d20) with
    | (T_DNil) => (wfDecls_dnil (domainEnv G1))
    | (T_DCons T d t G0 jm5 wd) => (wfDecls_dcons (domainEnv G1) (Typing_wf_0 G1 t T jm5) (DTyping_wf_0 (evar G1 T) d G0 wd))
  end
with Typing_wf_0 (G1 : Env) (t23 : Tm) (T34 : Ty) (jm7 : (Typing G1 t23 T34)) {struct jm7} :
(wfTm (domainEnv G1) t23) :=
  match jm7 in (Typing _ t23 T34) return (wfTm (domainEnv G1) t23) with
    | (T_Var T x lk0 H20 H21) => (wfTm_var (domainEnv G1) _ H21)
    | (T_Abs T1 T2 t jm H22 H23) => (wfTm_abs (domainEnv G1) H22 (Typing_wf_0 (evar G1 T1) t (weakenTy T2 (HS tm H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_app (domainEnv G1) (Typing_wf_0 G1 t1 (tarr T11 T12) jm0) (Typing_wf_0 G1 t2 T11 jm1))
    | (T_Tabs T t jm2) => (wfTm_tabs (domainEnv G1) (Typing_wf_0 (etvar G1) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H32) => (wfTm_tapp (domainEnv G1) (Typing_wf_0 G1 t1 (tall T12) jm3) H32)
    | (T_Let T d t G wd jm4 H34) => (wfTm_lett (domainEnv G1) (DTyping_wf_0 G1 d G wd) (wfTm_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G1 (appendEnv empty G)) (f_equal2 appendHvl (eq_refl (domainEnv G1)) (eq_trans (domainEnv_appendEnv empty G) (f_equal2 appendHvl (eq_refl H0) (domain_DTyping_bind G1 d G wd))))) eq_refl (Typing_wf_0 (appendEnv G1 (appendEnv empty G)) t (weakenTy T (appendHvl H0 (bind d))) jm4)))
  end
with Typing_wf_1 (G1 : Env) (t23 : Tm) (T34 : Ty) (jm8 : (Typing G1 t23 T34)) {struct jm8} :
(wfTy (domainEnv G1) T34) :=
  match jm8 in (Typing _ t23 T34) return (wfTy (domainEnv G1) T34) with
    | (T_Var T x lk1 H20 H21) => H20
    | (T_Abs T1 T2 t jm H22 H23) => (wfTy_tarr (domainEnv G1) H22 H23)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_tarr_1 (domainEnv G1) T11 T12 (Typing_wf_1 G1 t1 (tarr T11 T12) jm0))
    | (T_Tabs T t jm2) => (wfTy_tall (domainEnv G1) (Typing_wf_1 (etvar G1) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H32) => (substhvl_ty_wfTy H32 (HS ty (domainEnv G1)) T12 (inversion_wfTy_tall_1 (domainEnv G1) T12 (Typing_wf_1 G1 t1 (tall T12) jm3)) (substhvl_ty_here (domainEnv G1)))
    | (T_Let T d t G wd jm4 H34) => H34
  end.
 Hint Extern 8 => match goal with
  | H41 : (DTyping _ _ _) |- _ => pose proof ((DTyping_wf_0 _ _ _ H41)); clear H41
end : wf.
 Hint Extern 8 => match goal with
  | H42 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H42)); pose proof ((Typing_wf_1 _ _ _ H42)); clear H42
end : wf.
Lemma subst_evar_lookup_evar (G7 : Env) (s6 : Tm) (T35 : Ty) (jm9 : (Typing G7 s6 T35)) :
  (forall (d21 : (Trace tm)) (G8 : Env) (G10 : Env) (sub : (subst_evar G7 T35 s6 d21 G8 G10)) (x17 : (Index tm)) (T36 : Ty) ,
    (lookup_evar G8 x17 T36) -> (Typing G10 (substIndex d21 s6 x17) T36)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Fixpoint subst_etvar_DTyping (G9 : Env) (S5 : Ty) (H46 : (wfTy (domainEnv G9) S5)) (G8 : Env) (d : Decls) (G10 : Env) (wd6 : (DTyping G8 d G10)) :
(forall (G11 : Env) (d22 : (Trace ty)) (H47 : (subst_etvar G9 S5 d22 G8 G11)) ,
  (DTyping G11 (tsubstDecls d22 S5 d) (tsubstEnv d22 S5 G10))) :=
  match wd6 in (DTyping _ d G10) return (forall (G11 : Env) (d22 : (Trace ty)) (H47 : (subst_etvar G9 S5 d22 G8 G11)) ,
    (DTyping G11 (tsubstDecls d22 S5 d) (tsubstEnv d22 S5 G10))) with
    | (T_DNil) => (fun (G11 : Env) (d22 : (Trace ty)) (H47 : (subst_etvar G9 S5 d22 G8 G11)) =>
      (T_DNil G11))
    | (T_DCons T35 d21 t24 G7 jm9 wd5) => (fun (G11 : Env) (d22 : (Trace ty)) (H47 : (subst_etvar G9 S5 d22 G8 G11)) =>
      (DTyping_cast G11 _ _ G11 (tsubstDecls d22 S5 (dcons t24 d21)) _ eq_refl eq_refl (eq_sym (tsubstEnv_appendEnv d22 S5 (evar empty T35) G7)) (T_DCons G11 (tsubstTy (weakenTrace d22 H0) S5 T35) (tsubstDecls (weakenTrace d22 (HS tm H0)) S5 d21) (tsubstTm (weakenTrace d22 H0) S5 t24) (tsubstEnv (weakenTrace d22 (HS tm H0)) S5 G7) (subst_etvar_Typing G9 S5 H46 G8 t24 T35 jm9 G11 d22 (weaken_subst_etvar empty H47)) (subst_etvar_DTyping G9 S5 H46 (evar G8 T35) d21 G7 wd5 (appendEnv G11 (tsubstEnv d22 S5 (evar empty T35))) (weakenTrace d22 (HS tm H0)) (weaken_subst_etvar (evar empty T35) H47)))))
  end
with subst_etvar_Typing (G9 : Env) (S5 : Ty) (H60 : (wfTy (domainEnv G9) S5)) (G8 : Env) (t : Tm) (T : Ty) (jm15 : (Typing G8 t T)) :
(forall (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) ,
  (Typing G10 (tsubstTm d22 S5 t) (tsubstTy d22 S5 T))) :=
  match jm15 in (Typing _ t T) return (forall (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) ,
    (Typing G10 (tsubstTm d22 S5 t) (tsubstTy d22 S5 T))) with
    | (T_Var T35 x17 lk2 H43 H44) => (fun (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) =>
      (T_Var G10 (tsubstTy (weakenTrace d22 H0) S5 T35) x17 (subst_etvar_lookup_evar H60 H61 T35 lk2) (substhvl_ty_wfTy H60 _ _ H43 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61)) H44)))
    | (T_Abs T36 T39 t24 jm9 H45 H46) => (fun (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) =>
      (T_Abs G10 (tsubstTy (weakenTrace d22 H0) S5 T36) (tsubstTy (weakenTrace d22 H0) S5 T39) (tsubstTm (weakenTrace d22 (HS tm H0)) S5 t24) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d22 S5 T39)) (subst_etvar_Typing G9 S5 H60 (evar G8 T36) t24 (weakenTy T39 (HS tm H0)) jm9 (appendEnv G10 (tsubstEnv d22 S5 (evar empty T36))) (weakenTrace d22 (HS tm H0)) (weaken_subst_etvar (evar empty T36) H61))) (substhvl_ty_wfTy H60 _ _ H45 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61))) (substhvl_ty_wfTy H60 _ _ H46 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61)))))
    | (T_App T37 T38 t25 t26 jm10 jm11) => (fun (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) =>
      (T_App G10 (tsubstTy (weakenTrace d22 H0) S5 T37) (tsubstTy (weakenTrace d22 H0) S5 T38) (tsubstTm (weakenTrace d22 H0) S5 t25) (tsubstTm (weakenTrace d22 H0) S5 t26) (subst_etvar_Typing G9 S5 H60 G8 t25 (tarr T37 T38) jm10 G10 d22 (weaken_subst_etvar empty H61)) (subst_etvar_Typing G9 S5 H60 G8 t26 T37 jm11 G10 d22 (weaken_subst_etvar empty H61))))
    | (T_Tabs T35 t24 jm12) => (fun (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) =>
      (T_Tabs G10 (tsubstTy (weakenTrace d22 (HS ty H0)) S5 T35) (tsubstTm (weakenTrace d22 (HS ty H0)) S5 t24) (subst_etvar_Typing G9 S5 H60 (etvar G8) t24 T35 jm12 (appendEnv G10 (tsubstEnv d22 S5 (etvar empty))) (weakenTrace d22 (HS ty H0)) (weaken_subst_etvar (etvar empty) H61))))
    | (T_Tapp T38 T39 t25 jm13 H55) => (fun (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) =>
      (Typing_cast G10 _ _ G10 (tsubstTm d22 S5 (tapp t25 T39)) (tsubstTy d22 S5 (tsubstTy X0 T39 T38)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T38 d22 S5 T39)) (T_Tapp G10 (tsubstTy (weakenTrace d22 (HS ty H0)) S5 T38) (tsubstTy (weakenTrace d22 H0) S5 T39) (tsubstTm (weakenTrace d22 H0) S5 t25) (subst_etvar_Typing G9 S5 H60 G8 t25 (tall T38) jm13 G10 d22 (weaken_subst_etvar empty H61)) (substhvl_ty_wfTy H60 _ _ H55 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61))))))
    | (T_Let T35 d21 t24 G7 wd5 jm14 H57) => (fun (G10 : Env) (d22 : (Trace ty)) (H61 : (subst_etvar G9 S5 d22 G8 G10)) =>
      (T_Let G10 (tsubstTy (weakenTrace d22 H0) S5 T35) (tsubstDecls (weakenTrace d22 H0) S5 d21) (tsubstTm (weakenTrace d22 (appendHvl H0 (bind d21))) S5 t24) (tsubstEnv (weakenTrace d22 H0) S5 G7) (subst_etvar_DTyping G9 S5 H60 G8 d21 G7 wd5 G10 d22 (weaken_subst_etvar empty H61)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tsubstEnv_appendEnv d22 S5 empty G7)) (f_equal3 tsubstTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_DTyping_bind G8 d21 G7 wd5)))) eq_refl eq_refl) (eq_trans (f_equal3 tsubstTy (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_DTyping_bind G8 d21 G7 wd5)))) eq_refl eq_refl) (eq_trans (eq_sym (weakenTy_tsubstTy (appendHvl H0 (bind d21)) d22 S5 T35)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))))) (subst_etvar_Typing G9 S5 H60 (appendEnv G8 (appendEnv empty G7)) t24 (weakenTy T35 (appendHvl H0 (bind d21))) jm14 (appendEnv G10 (tsubstEnv d22 S5 (appendEnv empty G7))) (weakenTrace d22 (domainEnv (appendEnv empty G7))) (weaken_subst_etvar (appendEnv empty G7) H61))) (substhvl_ty_wfTy H60 _ _ H57 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H61)))))
  end.
Fixpoint subst_evar_DTyping (G9 : Env) (s6 : Tm) (T35 : Ty) (jm10 : (Typing G9 s6 T35)) (G8 : Env) (d : Decls) (G10 : Env) (wd6 : (DTyping G8 d G10)) :
(forall (G11 : Env) (d22 : (Trace tm)) (H47 : (subst_evar G9 T35 s6 d22 G8 G11)) ,
  (DTyping G11 (substDecls d22 s6 d) G10)) :=
  match wd6 in (DTyping _ d G10) return (forall (G11 : Env) (d22 : (Trace tm)) (H47 : (subst_evar G9 T35 s6 d22 G8 G11)) ,
    (DTyping G11 (substDecls d22 s6 d) G10)) with
    | (T_DNil) => (fun (G11 : Env) (d22 : (Trace tm)) (H47 : (subst_evar G9 T35 s6 d22 G8 G11)) =>
      (T_DNil G11))
    | (T_DCons T36 d21 t24 G7 jm9 wd5) => (fun (G11 : Env) (d22 : (Trace tm)) (H47 : (subst_evar G9 T35 s6 d22 G8 G11)) =>
      (DTyping_cast G11 _ _ G11 (substDecls d22 s6 (dcons t24 d21)) _ eq_refl eq_refl (eq_sym eq_refl) (T_DCons G11 T36 (substDecls (weakenTrace d22 (HS tm H0)) s6 d21) (substTm (weakenTrace d22 H0) s6 t24) G7 (subst_evar_Typing G9 s6 T35 jm10 G8 t24 T36 jm9 G11 d22 (weaken_subst_evar _ empty H47)) (subst_evar_DTyping G9 s6 T35 jm10 (evar G8 T36) d21 G7 wd5 (appendEnv G11 (evar empty T36)) (weakenTrace d22 (HS tm H0)) (weaken_subst_evar _ (evar empty T36) H47)))))
  end
with subst_evar_Typing (G9 : Env) (s6 : Tm) (T35 : Ty) (jm15 : (Typing G9 s6 T35)) (G8 : Env) (t : Tm) (T : Ty) (jm16 : (Typing G8 t T)) :
(forall (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) ,
  (Typing G10 (substTm d22 s6 t) T)) :=
  match jm16 in (Typing _ t T) return (forall (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) ,
    (Typing G10 (substTm d22 s6 t) T)) with
    | (T_Var T36 x17 lk2 H44 H45) => (fun (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) =>
      (subst_evar_lookup_evar G9 s6 T35 jm15 d22 G8 G10 H61 x17 T36 lk2))
    | (T_Abs T37 T40 t24 jm9 H46 H47) => (fun (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) =>
      (T_Abs G10 T37 T40 (substTm (weakenTrace d22 (HS tm H0)) s6 t24) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G9 s6 T35 jm15 (evar G8 T37) t24 (weakenTy T40 (HS tm H0)) jm9 (appendEnv G10 (evar empty T37)) (weakenTrace d22 (HS tm H0)) (weaken_subst_evar _ (evar empty T37) H61))) (substhvl_tm_wfTy _ _ H46 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H61))) (substhvl_tm_wfTy _ _ H47 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H61)))))
    | (T_App T38 T39 t25 t26 jm10 jm11) => (fun (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) =>
      (T_App G10 T38 T39 (substTm (weakenTrace d22 H0) s6 t25) (substTm (weakenTrace d22 H0) s6 t26) (subst_evar_Typing G9 s6 T35 jm15 G8 t25 (tarr T38 T39) jm10 G10 d22 (weaken_subst_evar _ empty H61)) (subst_evar_Typing G9 s6 T35 jm15 G8 t26 T38 jm11 G10 d22 (weaken_subst_evar _ empty H61))))
    | (T_Tabs T36 t24 jm12) => (fun (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) =>
      (T_Tabs G10 T36 (substTm (weakenTrace d22 (HS ty H0)) s6 t24) (subst_evar_Typing G9 s6 T35 jm15 (etvar G8) t24 T36 jm12 (appendEnv G10 (etvar empty)) (weakenTrace d22 (HS ty H0)) (weaken_subst_evar _ (etvar empty) H61))))
    | (T_Tapp T39 T40 t25 jm13 H56) => (fun (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) =>
      (T_Tapp G10 T39 T40 (substTm (weakenTrace d22 H0) s6 t25) (subst_evar_Typing G9 s6 T35 jm15 G8 t25 (tall T39) jm13 G10 d22 (weaken_subst_evar _ empty H61)) (substhvl_tm_wfTy _ _ H56 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H61)))))
    | (T_Let T36 d21 t24 G7 wd5 jm14 H58) => (fun (G10 : Env) (d22 : (Trace tm)) (H61 : (subst_evar G9 T35 s6 d22 G8 G10)) =>
      (T_Let G10 T36 (substDecls (weakenTrace d22 H0) s6 d21) (substTm (weakenTrace d22 (appendHvl H0 (bind d21))) s6 t24) G7 (subst_evar_DTyping G9 s6 T35 jm15 G8 d21 G7 wd5 G10 d22 (weaken_subst_evar _ empty H61)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal3 substTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_DTyping_bind G8 d21 G7 wd5)))) eq_refl eq_refl) (eq_trans eq_refl (eq_trans (eq_sym eq_refl) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0)))))) (subst_evar_Typing G9 s6 T35 jm15 (appendEnv G8 (appendEnv empty G7)) t24 (weakenTy T36 (appendHvl H0 (bind d21))) jm14 (appendEnv G10 (appendEnv empty G7)) (weakenTrace d22 (domainEnv (appendEnv empty G7))) (weaken_subst_evar _ (appendEnv empty G7) H61))) (substhvl_tm_wfTy _ _ H58 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H61)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenDecls_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.