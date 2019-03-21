Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Ty : Set :=
  | tvar (X : nat)
  | top
  | tarr (T1 T2 : Ty)
  | tall (T1 : Ty) (T2 : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Tm : Set :=
  | var  (x  : nat)
  | abs  (T  : Ty) (t  : Tm)
  | app  (t1 : Tm) (t2 : Tm)
  | tabs (T  : Ty) (t  : Tm)
  | tapp (t  : Tm) (T  : Ty).

(******************************************************************************)
(* Representation of contexts.                                                *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | evar   (Γ : Env) (T : Ty)
  | etvar  (Γ : Env) (T : Ty).
