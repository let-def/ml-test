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
  | Ty_const_float
  | Ty_const_string

and ty_con = 
  { ty_name : Ident.t ; ty_vars : Ident.t list ; ty_body : ty }
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
  | Tycon of tyvar list * ty (* Type scheme *)
  | Tyfree (* Free type variable *)

let ctx_initial, ty_bool = 
  let ty_bool, _, _ as bool_def = 
    Ident.make "bool", [], 
    Ty_tagged (Tag_cons (0, [], [], [], 
                         Tag_cons (1, [], [], [], Tag_close)))
  in
  let types = [bool_def] in
  let ctx = List.fold_right
      (fun (name, vars, def) ->
         IdentMap.add name (Tycon (vars,def)))
      types IdentMap.empty 
  in 
  ctx, ty_bool

let rec wellformed_ty ctx = function
  | Ty_var v -> 
    (try match IdentMap.find v ctx with
       | Tyvar _ | Tyfree -> ()
       | Tycon _ -> failwith "wellformed_ty: unexpected type constructor"
       | Tmvar _ -> failwith "wellformed_ty: reference to term variable"
      with Not_found -> failwith "wellformed_ty: unbound variable");
  | Ty_con (v,targs) -> 
    (try match IdentMap.find v ctx with
       | Tycon (v,arity) when arity = List.length targs -> ()
       | _ -> failwith "wellformed_ty: reference to term variable"
      with Not_found -> failwith "wellformed_ty: unbound constructor");
     List.iter (wellformed_ty ctx) targs
  | Ty_const _ -> ()
  | Ty_abs (v,ty) ->
    if IdentMap.mem v ctx then failwith "wellformed_ty: already bound variable";
    wellformed_ty (IdentMap.add v Tyfree ctx) ty
  | Ty_arrow (targ, tres) ->
    wellformed_ty ctx targ;
    wellformed_ty ctx tres
  | Ty_tagged _ -> failwith "wellformed_ty: 'tagged' can't appear in syntax"
  | Ty_proxy _ -> failwith "wellformed_ty: 'proxy' can't appear in syntax"

let rec wellformed_tm ctx = function
  | Tm_var v -> 
    (try match IdentMap.find v ctx with
       | Tmvar _ -> ()
       | _ -> failwith "wellformed_tm: expecting term variable"
      with Not_found -> failwith "wellformed_tm: unbound variable");
  | Tm_const cst -> ()
  | Tm_app (f,a) ->
    wellformed_tm ctx f;
    wellformed_tm ctx a
  | Tm_fun ((id,t), body) ->
    wellformed_ty ctx t;
    wellformed_tm (IdentMap.add id (Tmvar t) ctx) body
  | Tm_let (id, value, body) ->
    wellformed_tm ctx value;
    (* Fake type *)
    wellformed_tm (IdentMap.add id (Tmvar (Ty_const Ty_const_int)) ctx) body
  | Tm_letrec (values, body) ->
    let ctx = List.fold_left 
        (fun ctx ((id,ty),_) -> IdentMap.add id (Tmvar ty) ctx)
        ctx values
    in
    List.iter (fun (_,expr) -> wellformed_tm ctx expr) values;
    wellformed_tm ctx body
  | Tm_if (cond, t, e) ->
    wellformed_tm ctx cond;
    wellformed_tm ctx t;
    wellformed_tm ctx e
  | Tm_switch (value, branches, ty) ->
    wellformed_tm ctx value;
    List.iter (wellformed_tm ctx) (List.map snd branches);
    wellformed_ty ctx ty
  | Tm_unpack (value, idtm, idty, body) ->
    wellformed_tm ctx value;
    wellformed_tm (IdentMap.add idtm (Tmvar (Ty_proxy (idty,0)))
                     (IdentMap.add idty Tyfree ctx)) body
  | Tm_prim (p, args) ->
    List.iter (wellformed_tm ctx) args
  | Tm_tyabs (v, body) ->
    wellformed_tm (IdentMap.add v Tyfree ctx) body
  | Tm_tyapp (expr, ty) ->
    wellformed_tm ctx expr;
    wellformed_ty ctx ty

let rec check_equal_type t1 t2 = match t1, t2 with
  | Ty_var v1, Ty_var v2 when Ident.equal v1 v2 -> ()
  | Ty_con (v1,ts1), Ty_con (v2,ts2) when Ident.equal v1 v2 ->
    List.iter2 check_equal_type ts1 ts2
  | Ty_const c1, Ty_const c2 when c1 = c2 -> ()
  | Ty_abs (v1,t1), Ty_abs (v2,t2) when Ident.equal v1 v2 ->
    check_equal_type t1 t2
  | Ty_arrow (ta1,tb1), Ty_arrow (ta2,tb2) ->
    check_equal_type ta1 ta2;
    check_equal_type tb1 tb2
  | Ty_tagged ts1, Ty_tagged ts2 -> check_equal_tagset ts1 ts2
  | Ty_proxy (v1,d1), Ty_proxy (v2,d2) when Ident.equal v1 v2 && d1 = d2 ->
    ()
  | _ -> failwith "incompatible types"

and check_equal_tagset ts1 ts2 = match ts1, ts2 with
  | Tag_cons (tg1,id1,c1,tys1,ts1'), Tag_cons (tg2,id2,c2,tys2,ts2') 
    when tg1 = tg2 && List.for_all2 Ident.equal id1 id2 ->
    List.iter2 check_equal_cstr c1 c2;
    List.iter2 check_equal_type tys1 tys2;
    check_equal_tagset ts1' ts2'
  | Tag_open, Tag_open | Tag_close, Tag_close -> ()
  | _ -> failwith "incompatible tagsets"

and check_equal_cstr c1 c2 = match c1, c2 with
  | Cstr_equal (v1, t1), Cstr_equal (v2, t2) 
  | Cstr_subst (v1, t1), Cstr_subst (v2, t2) when Ident.equal v1 v2 ->
    check_equal_type t1 t2 
  | _ -> failwith "incompatible constraints"

let is_equal_type t1 t2 = try check_equal_type t1 t2; true with _ -> false

let rec subst_type s = function
  | Ty_var v as t ->
    (try IdentMap.find v s
     with Not_found -> t)
  | Ty_con (v,tys) -> 
    (if IdentMap.mem v s then failwith "trying to substitute type constructor");
    Ty_con (v, List.map (subst_type s) tys)
  | Ty_const _ as t -> t
  | Ty_abs (v,ty) -> 
    (if IdentMap.mem v s then failwith "trying to substitute free variable");
    subst_type s ty
  | Ty_arrow (targ,tres) -> Ty_arrow (subst_type s targ, subst_type s tres)
  | Ty_tagged ts -> Ty_tagged (subst_tagset s ts)
  | Ty_proxy (v,_) as t ->
    (if IdentMap.mem v s then failwith "trying to substitute proxy variable");
    t

and subst_tagset s = function
  | Tag_close | Tag_open as t -> t
  | Tag_cons (tg,tv,cstr,tys,ts') ->
    let assert_nosubst v =
      if IdentMap.mem v s then failwith "trying to substitute tagset variable"
    in
    List.iter assert_nosubst tv;
    Tag_cons (tg, tv, List.map (subst_cstr s) cstr, 
              List.map (subst_type s) tys, subst_tagset s ts')

and subst_cstr s = function
  | Cstr_subst (v,t) -> 
    if IdentMap.mem v s then failwith "trying to substitute constraint variable";
    Cstr_subst (v, subst_type s t)
  | Cstr_equal (v,t) -> 
    if IdentMap.mem v s then failwith "trying to substitute constraint variable";
    Cstr_equal (v, subst_type s t)

let rec type_of ctx = function
  | Tm_var v -> 
    (try match IdentMap.find v ctx with
       | Tmvar t -> t
       | _ -> failwith "type_of: expecting term variable"
     with Not_found -> failwith "type_of: unbound variable")
  | Tm_const cst ->
    (match cst with
     | Tm_int _ -> Ty_const_int
     | Tm_float _ -> Ty_const_float
     | Tm_string _ -> Ty_const_string)
  | Tm_app (f,arg) ->
    (match type_of ctx f with
     | Ty_arrow (targ,tres) ->
       check_equal_type targ (type_of ctx arg);
       tres
     | _ -> failwith "expecting function type")
  | Tm_fun ((id,t), body) ->
    let tres = type_of (IdentMap.add id (Tmvar t) ctx) body in
    Ty_arrow (t, tres)
  | Tm_let (id, value, body) ->
    let t = type_of ctx value in
    type_of (IdentMap.add id (Tmvar t) ctx) body
  | Tm_if (cond, t, e) ->
    (match type_of ctx cond with
     | Ty_con (v,[]) when Ident.equal v ty_bool ->
       let tt, te = type_of ctx t, type_of ctx te in
       check_equal_type tt te;
       tt
     | Ty_tagged _ -> failwith "TODO"
     | _ -> failwith "expecting boolean")
  | Tm_switch (value, branches, ty) ->
  | Tm_unpack (value, idtm, idty, body) ->
  | Tm_prim (p, args) ->
  | Tm_tyabs 
  | Tm_tyapp
