open Format


(* normal/neutral terms *)
type nf = Lam of nf
       | Neu of ne
and ne = Var of int
       | App of ne * nf
       | Unit

(* terms *)
type tm = Lam' of tm
        | Var' of int
        | App' of tm * tm
        | Unit'

(* types *)
type nty = U
         | El of nf
         | Pi of nty * nty

type ty = U'
        | El' of tm
        | Pi' of ty * ty


type con = ty list

let rec pp_tm_ k ppf t =
  match t with
  | Unit' -> fprintf ppf "*"
  | Var' x -> fprintf ppf "x%d" (k - x)
  | Lam' s -> fprintf ppf "@[<1>(λx%d. %a)@]" (k + 1) (pp_tm_ (k + 1)) s
  | App'(t,u) -> fprintf ppf "@[<1>(%a %a)@]" (pp_tm_ k) t (pp_tm_ k) u
let pp_tm ppf (t : tm) = (pp_tm_ 0 ppf t)


let rec pp_ty_ k ppf a =
  match a with
  | U' -> fprintf ppf "U"
  | El' t -> fprintf ppf "[%a]" (pp_tm_ k) t
  | Pi'(a,b) -> (fprintf ppf "@[<1>([x%d:%a] -> %a)@]"
                  (k + 1) (pp_ty_ k) a (pp_ty_ (k + 1)) b)
let pp_ty ppf (a : ty) = (pp_ty_ 0 ppf a)

let rec nf_tm (t : nf) : tm =
  match t with
  | Lam t -> Lam' (nf_tm t)
  | Neu t -> ne_tm t
and ne_tm (t : ne) : tm =
  match t with
  | Var k -> Var' k
  | App(t,u) -> App'(ne_tm t, nf_tm u)
  | Unit -> Unit'

let pp_nf ppf (t : nf) = pp_tm ppf (nf_tm t)
let pp_ne ppf (t : ne) = pp_tm ppf (ne_tm t)

(***********************************************)
(* semantics                                   *)
(***********************************************)
type env = vltm list

and vltm = LamD of tm * env           (* closure *)
         | ReflD of vlty * vlne       (* defunctionalized reflection *)

and vlne = VarD of int
         | AppD of vlne * vlnf
         | UnitD

and vlnf = ReifD of vlty * vltm       (* defunctionalized reification *)

and vlty = UD
         | ElD of vlnf
         | PiD of vlty * (ty * env)   (* closure *)


let rec eval_tm (t : tm) (e : env) : vltm =
  match t with
  | Lam' s -> LamD(s,e)
  | Var' k -> List.nth e k
  | App' (t,u) -> appD (eval_tm t e) (eval_tm u e)
  | Unit' -> ReflD(UD, UnitD)
and eval_ty (a : ty) (e : env) : vlty =
  match a with
  | U' -> UD
  | El' t -> ElD(ReifD(UD, eval_tm t e))
  | Pi'(a,b) -> PiD(eval_ty a e, (b,e))
and appD (u : vltm) (v : vltm) : vltm =
  match u with
  | LamD (t,e) -> eval_tm t (v::e)
  (* defunctionalized reflection *)
  | ReflD(PiD(u,(b,e)), n) -> let b0 = (eval_ty b (v :: e)) in
                              ReflD(b0, AppD(n, ReifD(u, v)))
  | _ -> failwith "Applicand must be a closure or a reflection!"

(* readback -- evaluates defunctionalized reification *)
let rec reify_nf (k : int) (v : vlnf) : nf =
  match v with
  | ReifD(PiD(u,(b,e)), f) ->
     let w = (ReflD(u, VarD k)) in
     let b0 = (eval_ty b (w :: e)) in
     Lam(reify_nf (k + 1) (ReifD(b0, appD f w)))
  | ReifD(UD, ReflD(UD, t)) -> Neu(reify_ne k t)
  | ReifD(ElD _, ReflD(ElD _, t)) -> Neu(reify_ne k t)
  | _ -> failwith "Cannot reify ill-typed value!"
and reify_ne (k : int) (v : vlne) : ne =
  match v with
  | VarD j -> (if (j + 1) > k then (failwith "Negative index!")
               else Var (k - (j + 1)))
  | AppD(t,u) -> App(reify_ne k t, reify_nf k u)
  | UnitD -> Unit

let rec reify_ty (k : int) (v : vlty) : nty =
  match v with
  | UD -> U
  | ElD u -> El (reify_nf k u)
  | PiD(u, (b,e)) -> let a = (reify_ty k u) in
                     let w = (ReflD(u, VarD k)) in
                     Pi(a, reify_ty (k + 1) (eval_ty b (w :: e)))

let id_env (ctx : con) : env =
  let rec id_env_ (k : int) (ctx : con) =
    match ctx with
    | [] -> []
    | a::ctx -> let e = (id_env_ (k + 1) ctx) in
                ReflD(eval_ty a e, VarD k) :: e
  in (id_env_ 0 ctx)

let nbe (ctx : con) (a : ty) (t : tm) : nf =
  let e = (id_env ctx) in
  let u = (eval_ty a e) in
  reify_nf (List.length ctx) (ReifD(u, eval_tm t e))

let nbeT (ctx : con) (a : ty) : nty =
  reify_ty (List.length ctx) (eval_ty a (id_env ctx))

(****************************************************************)
(* Tests                                                        *)
(****************************************************************)

let _I = Lam' (Var' 0)
let _K = Lam' (Lam' (Var' 1))
(* (A -> (B -> C)) -> (A -> B) -> A -> C *)
let _S = Lam' (Lam' (Lam' (App'(App'(Var' 2, Var' 0),App'(Var' 1, Var' 0)))))

let _UU = Pi'(U',U')
let _UUU = Pi'(U',_UU)

let tests : (con * tm * ty) list
  = [([], _I, _UU);
     ([], _K, _UUU);
     ([], Lam' (Lam' (Var' 1)), Pi'(U',_UU));
     ([], Lam' (Lam' (App' (Var' 1,Var' 0))), Pi'(_UU, _UU));
     ([], Lam' (App' (_I, Var' 0)), _UU);
     ([], Unit', U');
     ([], App'(_I, Unit'), U');
     ([], _S, Pi'(_UUU,Pi'(_UU,_UU)));
     ([], Lam'(Lam' (App'(App'(_K, Var' 0),App'(Var' 1, Var' 0)))), Pi'(_UU,_UU));
     ([], App'(Lam' (Lam' (App'(App'(Var' 1,Var' 0), App'(_I, Var' 0)))),_K), _UU);
     ([], App'(App'(_S,_K),_K), _UU);
     ([], Lam' (* A : U *) (Lam' (* x : El A *) (Var' 1)), Pi'(U',Pi'(El' (Var' 0), U')));
     ([], Lam' (* A : U' *) (Lam' (* x : El' A *) (Var' 0)), Pi'(U',Pi'(El' (Var' 0), El' (Var' 1))));
     ([], Lam' (* A : U' *) (Lam' (* B : El' A -> U' *) (Var' 1)), Pi'(U',Pi'(Pi'(El'(Var' 0),U'),U')));
     ([], Lam'(Lam'(App'(Var' 0, Var' 1))), Pi'(U',Pi'(Pi'(U',U'), U')));

     ([], Lam' (* A : U' *) (Lam' (* B : El' A -> U' *) (Lam' (* x : A *) (App'(Var' 1, Var' 0)))), Pi'(U',Pi'(Pi'(El'(Var' 0),U'), Pi'(El'(Var' 1), U'))));
     ([], Lam' (* A : U' *) (Lam' (* B : El' A -> U' *) (Lam' (* C : (x : A) -> (B x) -> U' *) (Lam' (* x : A *) (Lam' (* y : B x *) (App'(App'(Var' 2, Var' 1),Var' 0)))))),
      Pi'(U', Pi'(Pi'(El'(Var' 0),U'), Pi'(Pi'(El'(Var' 1),Pi'(El'(App'(Var' 1,Var' 0)),U')), Pi'(El'(Var' 2), Pi'(El'(App'(Var' 2,Var' 0)), U'))))));
     ([], Lam' (* A : U' *) (Lam' (* x : El' A *) (Var' 0)), Pi'(U', Pi'(El' (App'(_I,Var' 0)), El' (Var' 1))));
     ([], Lam' (* A : U' *) (Lam' (* B : El' A -> El' A -> U' *) (Lam' (* x : El' A *) (App'(App'(Var' 1,Var' 0),Var' 0)))),
      Pi'(U', Pi'(Pi'(El'(Var' 0), Pi'(El'(Var' 1),U')), Pi'(El'(Var' 1), U'))));
     ([], Lam' (* A : U' *) (Lam' (* B : El' A -> El' A -> U' *) (Lam' (* x : El' A *) (Lam' (* y : El' A *) (App'(App'(Var' 2,Var' 1),Var' 0))))),
      Pi'(U', Pi'(Pi'(El'(Var' 0),Pi'(El'(Var' 1),U')), Pi'(El'(Var' 1), Pi'(El'(Var' 2),U')))));

     ([], Lam' (Lam' (Lam' (App'(App'(Var' 2,Var' 0),Var' 0)))), Pi'(Pi'(U',Pi'(U',U')),Pi'(U',Pi'(U',U'))));
     ([], Lam' (* N : U' *) (Lam' (* 0 : El' N*) (Lam' (* S : El' N -> El' N *) (App'(Var' 0,App'(Var' 0,App'(Var' 0,Var' 1)))))), Pi'(U', Pi'(El'(Var' 0), Pi'(Pi'(El'(Var' 1),El'(Var' 2)), El'(Var' 2)))));

    ]



let _ =
  for i=0 to (List.length tests) - 1 do
    (let (ctx,t,a) = (List.nth tests i) in
     (printf "test %d@\n %a@\n :: %a@\n" i pp_tm t pp_ty a);
     (printf "> %a@\n" pp_nf (nbe ctx a t)))
  done
