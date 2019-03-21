Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Ty : Set :=
  | tunit
  | tarr (T1 T2 : Ty)
  | tprod (T1 T2 : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Pat : Set :=
  | pvar  (T: Ty)
  | pprod (p1 p2: Pat).

Inductive Tm : Set :=
  | var  (x  : nat)
  | tt
  | abs  (T  : Ty) (t  : Tm)
  | app  (t1 : Tm) (t2 : Tm)
  | prod (t1 : Tm) (t2 : Tm)
  | lett (p : Pat) (s : Tm) (t : Tm) .

(* Calculates the number of cariables bound in a pattern. *)
Fixpoint bindPat (p : Pat) : nat :=
  match p with
   | pvar T      => 1
   | pprod p1 p2 => bindPat p2 + bindPat p1
  end.

(******************************************************************************)
(* Representation of contexts, extensions.                                    *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | evar   (Γ : Env) (T : Ty).
