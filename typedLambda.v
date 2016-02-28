Require Import ssreflect List.

Inductive typ :=
  | Tnat : typ
  | Tarrow : typ -> typ -> typ.

Inductive term :=
  | Var : nat -> term
  | ConstNat : nat -> term
  | App : term -> term -> term
  | Lambda : typ -> term -> term.

Check nth.
Check (list).
Definition context (t: Set) := list (option t).

Fixpoint omap (ty: typ) (oty: option typ) : option typ:=
  match oty with
    | None => None
    | Some t => Some (Tarrow (ty) (t)) 
  end.

Fixpoint type (ctx: list typ) (t: term) : option typ :=
  match t with
    | Var n => nth_error ctx n
    | ConstNat _ => Some Tnat 
    | App t1 t2 => if type ctx t1 is Some (Tarrow t1l t1r) then
                     if type ctx t2 is Some t1l then Some t1r
                     else None
                   else None
    | Lambda ty t => omap ty (type (ty :: ctx) t) 
  end.

(*Inductive well_typed : list typ -> term -> Prop :=
| var_is_well : forall (n: nat) (l: list typ), n < length l -> well_typed l (Var n)
| const_is_well : forall (n:nat) (l: list typ), well_typed l (ConstNat n)
| app_is_well : forall (t u: term) (ty: typ) (l: list typ), well_typed (Lambda ty t) -> well_typed u -> well_typed (App (Lambda ty t) u)
| lambda_is_well : forall (t: term) (ty: typ) (l: list typ), well_typed t -> well_typed (Lambda ty t).*)
