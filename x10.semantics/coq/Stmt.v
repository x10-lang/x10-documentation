(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines the syntax of expressions for TX10 and Resilient X10 *)
Require Export Auxiliary.
Require Export Expr.

Require List.

Section stmt.

Context `{sc:StaticConfig}.

(* statements *)
Inductive stmt :=
  | Skip : stmt
  | Throw : expr -> stmt
  | Bind : var -> expr -> stmt -> stmt
  | Assign : expr -> fname -> expr -> stmt
  | Seq : stmt -> stmt -> stmt
  | At : place -> var -> expr -> stmt -> stmt
  | Async : stmt -> stmt
  | Finish : list val -> stmt-> stmt
  | Catch : stmt -> stmt -> stmt
  | DAt : place -> stmt -> stmt
  | DAsync : stmt -> stmt.

Global Instance subst_stmt : Subst (stmt) var val :=
{ subst := fix substp (s:stmt) (x:var) (v:val) : stmt :=
  match s with
    | Skip => Skip
    | Throw e => Throw e[v//x]
    (* capture avoiding substitution *)
    | Bind x' e s => Bind x' (e [v//x]) (if x == x' then s else substp s x v)
    | Assign e1 f e3 => Assign (e1[v//x]) f (e3[v//x])
    | Seq s1 s2 => Seq (substp s1 x v) (substp s2 x v)
    (* capture avoiding substitution *)
    (* we do not substitute across places *)
    | At p x' e s => At p x' (e[v//x])  (if x == x' then s else substp s x v)
    | Async s => Async (substp s x v)
    | Finish μ s => Finish μ (substp s x v)
    | Catch s t => Catch (substp s x v) (substp t x v)
    (* we do not substitute across places *)
    | DAt p s => DAt p (substp s x v)
    | DAsync s => DAsync (substp s x v)
  end}.

Fixpoint isAsync (s:stmt) : bool :=
  match s with
    | Seq s1 s2 => isAsync s1 && isAsync s2
    | DAsync s => true
    | DAt p s => isAsync s
    | Catch s _ => isAsync s
    | _ => false
  end.

Fixpoint isSync (s:stmt) : bool :=
  match s with
    | Skip => true
    | Throw e => true
    | Assign _ _ _ => true
    | Finish _ _ => true
    | Async _ => true
    | At _ _ _ _ => true
    | Bind _ _ _ => true
    | Catch s _ => isSync s
    | Seq s1 s2 => isSync s1 || isSync s2
    | DAt p s => isSync s
    | _ => false
  end.

Definition subst_stmt_list (s:stmt) (l:list (var*val)) : stmt
  := fold_right (fun xv s' => subst_stmt s' (fst xv) (snd xv)) s l.

End stmt.