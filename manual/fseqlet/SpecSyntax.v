Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Ty : Set :=
  | tvar (X : nat)
  | tarr (T1 T2 : Ty)
  | tall (T : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Tm : Set :=
  | var  (x  : nat)
  | abs  (T  : Ty) (t  : Tm)
  | app  (t1 : Tm) (t2 : Tm)
  | tabs (t  : Tm)
  | tapp (t  : Tm) (T  : Ty)
  | lett (ds : Decls) (t : Tm)
with Decls : Set :=
  | dnil
  | dcons (t : Tm) (ds : Decls).

Scheme tm_induction := Induction for Tm Sort Prop
with decls_induction := Induction for Decls Sort Prop.

Combined Scheme tm_decls_induction from tm_induction, decls_induction.

(* Calculates the number of cariables bound in a pattern. *)
Fixpoint bind (ds : Decls) : nat :=
  match ds with
   | dnil       => 0
   | dcons t ds => bind ds + 1
  end.

(******************************************************************************)
(* Representation of contexts, extensions.                                    *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | etvar (Γ : Env)
  | evar  (Γ : Env) (T : Ty).
