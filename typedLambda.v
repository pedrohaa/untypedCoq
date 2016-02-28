

Inductive typ :=
  | Tnat : typ
  | Tarrow : typ -> typ -> typ.

Inductive term :=
  | Var : nat -> term
  | ConstNat : nat -> term
  | App : term -> term -> term
  | Lambda : typ -> term -> term.
