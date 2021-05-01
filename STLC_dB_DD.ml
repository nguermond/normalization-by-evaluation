open Format


(* types *)
type ty = U
        | Arr of ty * ty

(* normal/neutral terms *)
type nf = Lam of nf
       | Neu of ne
and ne = Var of int
       | App of ne * nf
       | Star

(* terms *)
type tm = Lam' of tm
        | Var' of int
        | App' of tm * tm
        | Star'

type con = ty list

let pp_tm ppf (t : tm) =
  let rec pp_tm_ k ppf t =
    match t with
    | Star' -> fprintf ppf "*"
    | Var' x -> fprintf ppf "x%d" (k - x)
    | Lam' s -> fprintf ppf "@[<1>(λx%d. %a)@]" (k + 1) (pp_tm_ (k + 1)) s
    | App'(t,u) -> fprintf ppf "@[<1>(%a %a)@]" (pp_tm_ k) t (pp_tm_ k) u
  in (pp_tm_ 0 ppf t)

let rec nf_tm (t : nf) : tm =
  match t with
  | Lam t -> Lam' (nf_tm t)
  | Neu t -> ne_tm t
and ne_tm (t : ne) : tm =
  match t with
  | Var k -> Var' k
  | App(t,u) -> App'(ne_tm t, nf_tm u)
  | Star -> Star'

let pp_nf ppf (t : nf) = pp_tm ppf (nf_tm t)
let pp_ne ppf (t : ne) = pp_tm ppf (ne_tm t)

(***********************************************)
(* semantics                                   *)
(***********************************************)
type env = vltm list
and vltm = LamD of tm * env
         | ReflD of ty * vlne
and vlne = VarD of int
         | AppD of vlne * vlnf
         | StarD
and vlnf = ReifD of ty * vltm


let rec eval_tm (t : tm) (e : env) : vltm =
  match t with
  | Lam' s -> LamD(s,e)
  | Var' k -> List.nth e k
  | App' (t,u) -> appD (eval_tm t e) (eval_tm u e)
  | Star' -> ReflD(U, StarD)
and appD (u : vltm) (v : vltm) : vltm =
  match u with
  | LamD (t,e) -> eval_tm t (v::e)
  (* defunctionalized reflection *)
  | ReflD(Arr(a,b), n) -> ReflD(b, AppD(n, ReifD(a, v)))
  | _ -> failwith "Must be a closure or a reflection!"


(* takes semantic objects to normal terms *)
let rec reify_nf (k : int) (v : vlnf) : nf =
  match v with
  | ReifD(Arr(a,b), f) -> Lam(reify_nf (k + 1) (ReifD(b, appD f (ReflD(a, VarD k)))))
  | ReifD(U, ReflD(U, t)) -> Neu(reify_ne k t)
  | ReifD(U, ReflD _)
  | ReifD(U, LamD _) -> failwith "Cannot reify ill-typed value!"
and reify_ne (k : int) (v : vlne) : ne =
  match v with
  | VarD j -> (if (j + 1) > k then (failwith "Negative index!")
               else Var (k - (j + 1)))
  | AppD(t,u) -> App(reify_ne k t, reify_nf k u)
  | StarD -> Star


let id_env (ctx : con) : env =
  let rec id_env_ (k : int) (ctx : con) =
    match ctx with
    | [] -> []
    | a::ctx -> ReflD(a, VarD k) :: (id_env_ (k + 1) ctx)
  in (id_env_ 0 ctx)

let nbe (ctx : con) (a : ty) (t : tm) : nf =
  let k = (List.length ctx) in
  reify_nf k (ReifD(a, eval_tm t (id_env ctx)))

(****************************************************************)
(* Tests                                                        *)
(****************************************************************)

let _I = Lam' (Var' 0)
(* technically this should be Var' 1 *)
let _K = Lam' (Lam' (Var' 0))
(* (A -> (B -> C)) -> (A -> B) -> A -> C *)
let _S = Lam' (Lam' (Lam' (App'(App'(Var' 2, Var' 0),App'(Var' 1, Var' 0)))))

let _UU = Arr(U,U)
let _UUU = Arr(U,_UU)

let tests : (con * tm * ty) list
  = [([], _I, _UU);
     ([], _K, _UUU);
     ([], Lam' (Lam' (Var' 1)), Arr(U,_UU));
     ([], Lam' (Lam' (App' (Var' 1,Var' 0))), Arr (_UU, _UU));
     ([], Lam' (App' (_I, Var' 0)), _UU);
     ([], Star', U);
     ([], App'(_I, Star'), U);
     ([], _S, Arr(_UUU,Arr(_UU,_UU)));
     ([], Lam'(Lam' (App'(App'(_K, Var' 0),App'(Var' 1, Var' 0)))), Arr(_UU,_UU));
     ([], App'(Lam' (Lam' (App'(App'(Var' 1,Var' 0), App'(_I, Var' 0)))),_K), _UU);
    ]


let _ =
  for i=0 to (List.length tests) - 1 do
    (let (ctx,t,a) = (List.nth tests i) in
     (printf "test %d :: %a@\n" i pp_tm t);
     (printf "> %a@\n" pp_nf (nbe ctx a t)))
  done
