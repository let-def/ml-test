module Ident : sig
  type t
  val make : string -> t
  val fresh : t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val to_string : t -> string
end = struct
  type t = string * int
  let k = ref 0

  let make s = incr k; s, !k
  let fresh (s,_) = make s
  let compare (_,k1) (_,k2) = compare k1 k2
  let equal (_,k1) (_,k2) = k1 = k2
  let to_string (s,k) = s ^ "/" ^ string_of_int k
end

module IdentMap = Map.Make (Ident)

type tyvar = Ident.t
type tmvar = Ident.t 
type tag = int

type expr =
  | Tm_var of tmvar
  | Tm_value of value
  | Tm_app of expr * expr
  | Tm_fun of (tmvar * ty) * expr
  | Tm_switch of expr * branches * ty
  | Tm_unpack of expr * tmvar * expr
  | Tm_prim of prim * expr list
  | Tm_tyabs of tyvar * expr
  | Tm_tyapp of expr * ty

and branches =
  | Br_tag of tag * expr * branches
  | Br_any of expr
  | Br_end

and prim =
  | Pr_tagof
  | Pr_makeblock of int * ty
  | Pr_field of int
  | Pr_eq of int
  | Pr_lt of int
  | Pr_shift of int
  | Pr_isint
  | Pr_isout of int * int

and value =
  | Tv_int of int
  | Tv_string of string
  | Tv_block of int * value list
  | Tv_fun of (tmvar * ty) * expr

and ty =
  | Ty_var of tyvar
  | Ty_con of ty_prim
  | Ty_const of ty_const
  | Ty_abs of tyvar * ty
  | Ty_arrow of ty * ty
  | Ty_block of tag * ty list
  | Ty_tagged of tmvar * ty_prim
  | Ty_tag of int * tmvar * ty_prim

and ty_const =
  | Ty_const_int
  | Ty_const_string

and ty_con = 
  { ty_name : Ident.t ; ty_vars : Ident.t list ; ty_ctors : (tag * ty list) list }

and ty_prim = ty_con * ty list

and constr = 
  | Cstr_conj of constr * constr
  | Cstr_equal of ty * ty
  | Cstr_tagmem of Ident.t * tagset
  | Cstr_top

and tagset =
  | Ts_empty
  | Ts_inside of tag * tag
  | Ts_outside of tag * tag

let rec subst_type s = function
  | Ty_var v as t ->
    (try IdentMap.find v s
     with Not_found -> t)
  | Ty_con (v,tys) -> Ty_con (v, List.map (subst_type s) tys)
  | Ty_const _ as t -> t
  | Ty_abs (v,ty) -> 
    (if IdentMap.mem v s then failwith "trying to substitute bound variable");
    subst_type s ty
  | Ty_arrow (targ,tres) -> Ty_arrow (subst_type s targ, subst_type s tres)
  | Ty_block (tag,ts) -> Ty_block (tag, List.map (subst_type s) ts)
  | Ty_tagged (v,_) | Ty_tag (_,v,_) as t  ->
    (if IdentMap.mem v s then failwith "trying to substitute proxy variable");
    t

let subst_prim s = function
  | Pr_makeblock (tag, ty) -> Pr_makeblock (tag, subst_type s ty)
  | Pr_tagof | Pr_field _ | Pr_eq _ | Pr_lt _| Pr_isint | Pr_isout _ | Pr_shift _ as pr -> pr


let rec subst s sty = function
  | Tm_var v as t -> 
    (try IdentMap.find v s
     with Not_found -> t)
  | Tm_value _ as t -> t
  | Tm_fun ((v,ty),t) -> 
    (if IdentMap.mem v s then failwith "trying to substitute bound variable");
    Tm_fun ((v, subst_type sty ty), subst s sty t)
  | Tm_app (t1,t2) -> Tm_app(subst s sty t1, subst s sty t2)
  | Tm_switch (e, br, ty) ->
    Tm_switch (subst s sty e, subst_br s sty br, subst_type sty ty)
  | Tm_unpack (e, v, body) -> 
    (if IdentMap.mem v s then failwith "trying to substitute bound variable");
    Tm_unpack (subst s sty e, v, subst s sty body)
  | Tm_prim (p, es) -> Tm_prim (subst_prim sty p, List.map (subst s sty) es)
  | Tm_tyabs (v, e) ->
    (if IdentMap.mem v sty then failwith "trying to substitute bound type variable");
    Tm_tyabs (v, subst s sty e)
  | Tm_tyapp (e, ty) ->
    Tm_tyapp (subst s sty e, subst_type sty ty)

and subst_br s sty = function
  | Br_tag (t,e,br') -> Br_tag (t, subst s sty e, subst_br s sty br')
  | Br_any e -> Br_any (subst s sty e)
  | Br_end -> Br_end

module Eval =
struct
  exception Value
  exception Runtime

  let is_value = function
    | Tm_value _ -> true
    | _ -> false

  let eval_prim p args = match p, args with
    | Pr_makeblock (tag, _), args ->
      Tm_value (Tv_block (tag, List.map
                            (function Tm_value v -> v | _ -> raise Runtime)
                            args))
    | Pr_field i, [Tm_value (Tv_block (_, vs))] when i < List.length vs ->
      Tm_value (List.nth vs i)

    | Pr_tagof, [Tm_value (Tv_int x | Tv_block (x,_))] ->
      Tm_value (Tv_int x)

    | Pr_isint, [Tm_value (Tv_int _)] -> Tm_value (Tv_int 1)
    | Pr_isint, [_] -> Tm_value (Tv_int 0)

    | Pr_lt i, [Tm_value (Tv_int i')] when i' < i -> Tm_value (Tv_int 1)
    | Pr_lt i, [Tm_value (Tv_int i')]  -> Tm_value (Tv_int 0)

    | Pr_eq i, [Tm_value (Tv_int i')] when i' = i -> Tm_value (Tv_int 1)
    | Pr_eq i, [Tm_value (Tv_int i')]  -> Tm_value (Tv_int 0)

    | Pr_shift k, [Tm_value (Tv_int i)] -> Tm_value (Tv_int (i + k))

    | Pr_isout (k1,k2), [Tm_value (Tv_int i)] when i < k1 || i > k2 ->
      Tm_value (Tv_int 1)
    | Pr_isout (k1,k2), [Tm_value (Tv_int i)]  ->
      Tm_value (Tv_int 0)

    | _, _ -> raise Runtime

  let rec eval_step = function
    | Tm_var _ -> raise Runtime
    | Tm_value _ -> raise Value
    | Tm_fun ((v,t),e) -> Tm_value (Tv_fun ((v,t),e))

    | Tm_app (Tm_value (Tv_fun ((x, _), body)), (Tm_value _ as v2)) ->
      subst IdentMap.(add x v2 empty) IdentMap.empty body
    | Tm_app (Tm_value (Tv_fun _) as v1, e2) ->
      Tm_app (v1, eval_step e2)
    | Tm_app (e1, e2) -> Tm_app (eval_step e1, e2)

    | Tm_switch (Tm_value (Tv_int t | Tv_block (t, _)),br,ty) ->
      let rec branch = function
        | Br_tag (t',body,_) when t = t' -> body
        | Br_tag (_,_,next) -> branch next
        | Br_any body -> body
        | Br_end -> raise Runtime
      in
      branch br
    | Tm_switch (e,br,ty) -> Tm_switch (eval_step e, br, ty)

    | Tm_unpack (Tm_value _ as arg, x, body) ->
      subst IdentMap.(add x arg empty) IdentMap.empty body
    | Tm_unpack (arg, x, body) ->
      Tm_unpack (eval_step arg, x, body)

    | Tm_prim (p, args) when List.for_all is_value args ->
      eval_prim p args

    | Tm_prim (p, args) ->
      let rec eval_args = function
        | x :: xs when is_value x -> x :: eval_args xs
        | x :: xs -> eval_step x :: xs
        | _ -> raise Runtime
      in
      Tm_prim (p, eval_args args)

    | Tm_tyabs (_, body) | Tm_tyapp (body, _) -> body

end

(* TYPER *)

type binding =
  | Tmvar of ty (* Type of term variable *)
  | Tyvar of ty (* Value of type variable *)
  | Tyfree (* Free type variable *)

let ty_bool = {
  ty_name  = Ident.make "bool" ; 
  ty_vars  = [] ;
  ty_ctors = [0, []; 1, []]
}, []

let rec wellformed_ty ctx = function
  | Ty_var v -> 
    (try match IdentMap.find v ctx with
       | Tyvar _ | Tyfree -> ()
       | Tmvar _ -> failwith "wellformed_ty: reference to term variable"
      with Not_found -> failwith "wellformed_ty: unbound variable");
  | Ty_con tprim -> wellformed_ty_prim ctx tprim
  | Ty_const _ -> ()
  | Ty_abs (v,ty) ->
    if IdentMap.mem v ctx then failwith "wellformed_ty: already bound variable";
    wellformed_ty (IdentMap.add v Tyfree ctx) ty
  | Ty_arrow (targ, tres) ->
    wellformed_ty ctx targ;
    wellformed_ty ctx tres
  | Ty_tagged (v,p) | Ty_tag (_,v,p) ->
    (try match IdentMap.find v ctx with
       | Tmvar _ -> ()
       | Tyvar _ | Tyfree -> failwith "wellformed_ty: reference to type variable in tag"
     with Not_found -> failwith "wellformed_ty: unbound variable");
    wellformed_ty_prim ctx p
  | Ty_block (_,t) -> List.iter (wellformed_ty ctx) t

and wellformed_ty_prim ctx (con,targs) =
  (if List.length con.ty_vars <> List.length targs then
     failwith "Invalid type constructor arity");
  List.iter (wellformed_ty ctx) targs

let rec wellformed_tm ctx = function
  | Tm_var v -> 
    (try match IdentMap.find v ctx with
       | Tmvar _ -> ()
       | _ -> failwith "wellformed_tm: expecting term variable"
      with Not_found -> failwith "wellformed_tm: unbound variable");
  | Tm_value _ -> ()
  | Tm_app (f,a) ->
    wellformed_tm ctx f;
    wellformed_tm ctx a
  | Tm_fun ((id,t), body) ->
    wellformed_ty ctx t;
    wellformed_tm (IdentMap.add id (Tmvar t) ctx) body
  | Tm_switch (value, branches, ty) ->
    wellformed_tm ctx value;
    wellformed_br ctx branches;
    wellformed_ty ctx ty
  | Tm_unpack (value, idtm, body) ->
    wellformed_tm ctx value;
    wellformed_tm 
      (IdentMap.add idtm (Tmvar (Ty_tag (0,idtm,ty_bool))) ctx) body
  | Tm_prim (p, args) ->
    List.iter (wellformed_tm ctx) args
  | Tm_tyabs (v, body) ->
    wellformed_tm (IdentMap.add v Tyfree ctx) body
  | Tm_tyapp (expr, ty) ->
    wellformed_tm ctx expr;
    wellformed_ty ctx ty

and wellformed_br ctx = function
  | Br_tag (_,e,br') -> 
    wellformed_tm ctx e;
    wellformed_br ctx br'
  | Br_any e -> wellformed_tm ctx e
  | Br_end -> ()

let rec check_equal_type t1 t2 = match t1, t2 with
  | Ty_var v1, Ty_var v2 when Ident.equal v1 v2 -> ()
  | Ty_con p1, Ty_con p2 -> check_equal_tprim p1 p2
  | Ty_const c1, Ty_const c2 when c1 = c2 -> ()
  | Ty_abs (v1,t1), Ty_abs (v2,t2) when Ident.equal v1 v2 ->
    check_equal_type t1 t2
  | Ty_arrow (ta1,tb1), Ty_arrow (ta2,tb2) ->
    check_equal_type ta1 ta2;
    check_equal_type tb1 tb2
  | Ty_tagged (v1,p1), Ty_tagged (v2,p2) when Ident.equal v1 v2 ->
    check_equal_tprim p1 p2
  | Ty_tag (t1,x1,p1), Ty_tag (t2,x2,p2) when t1 = t2 && Ident.equal x1 x2 ->
    check_equal_tprim p1 p2
  | Ty_block (t1,ts1), Ty_block (t2,ts2) when t1 = t2 ->
    List.iter2 check_equal_type ts1 ts2

  | _ -> failwith "incompatible types"

and check_equal_tprim (p1,args1) (p2,args2) =
  if not (p1 == p2) then failwith "different type constructors";
  List.iter2 check_equal_type args1 args2

let is_equal_type t1 t2 = try check_equal_type t1 t2; true with _ -> false

let rec type_of ctx = function
  | Tm_var v -> 
    (try match IdentMap.find v ctx with
       | Tmvar t -> t
       | _ -> failwith "type_of: expecting term variable"
     with Not_found -> failwith "type_of: unbound variable")
  | Tm_value v -> type_of_value ctx v
  | Tm_app (f,arg) ->
    (match type_of ctx f with
     | Ty_arrow (targ,tres) ->
       check_equal_type targ (type_of ctx arg);
       tres
     | _ -> failwith "expecting function type")
  | Tm_fun ((id,t), body) ->
    let tres = type_of (IdentMap.add id (Tmvar t) ctx) body in
    Ty_arrow (t, tres)
  | Tm_tyabs (tv, body) -> 
    Ty_abs (tv, type_of (IdentMap.add tv Tyfree ctx) body)
  | Tm_tyapp (body,ty) ->
    begin match type_of ctx body with
      | Ty_abs (tv,tres) -> subst_type IdentMap.(add tv ty empty) tres
      | _ -> failwith "expecting type abstraction"
    end
  | Tm_switch (expr, branches, ty) ->
    let texpr = type_of ctx expr in
    type_of_branches ctx ty branches
  | Tm_unpack (expr, idtm, body) ->
    begin match type_of ctx expr with
      | Ty_con p | Ty_tagged (_,p) ->
        type_of IdentMap.(add idtm (Tmvar (Ty_tagged (idtm, p))) ctx) body
      | _ -> failwith "cannot unpack a non-constructor"
    end
  | Tm_prim (p, args) -> failwith "TODO"

and type_of_branches ctx ty = function
  | Br_tag (t,e,br') ->
    check_equal_type (type_of ctx e) ty;
    type_of_branches ctx ty br'
  | Br_any e ->
    check_equal_type (type_of ctx e) ty;
    ty
  | Br_end -> ty

and type_of_value ctx = function
  | Tv_string _ -> Ty_const Ty_const_string
  | Tv_int _ -> Ty_const Ty_const_int
  | Tv_block (t,vs) -> Ty_block (t, List.map (type_of_value ctx) vs)
  | Tv_fun (binding,body) -> type_of ctx (Tm_fun (binding,body))

