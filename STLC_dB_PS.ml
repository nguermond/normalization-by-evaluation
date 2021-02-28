open Format



(* types *)
type ty = Unit
        | Arr of ty * ty

type tm = Var of int
        | Star
        | Lam of tm
        | App of tm * tm

type con = ty list

let pp_tm ppf (t : tm) =
  let rec pp_tm_ k ppf t =
    match t with
    | Star -> fprintf ppf "*"
    | Var x -> fprintf ppf "x%d" (k - x)
    | Lam s -> fprintf ppf "@[<1>(λx%d. %a)@]" (k + 1) (pp_tm_ (k + 1)) s
    | App(t,u) -> fprintf ppf "@[<1>(%a %a)@]" (pp_tm_ k) t (pp_tm_ k) u
  in (pp_tm_ 0 ppf t)

(* type of normal/neutral terms *)
type nf = Lam_ of nf
        | Neu of ne
and ne = Var_ of int
       | App_ of ne * nf
       | Star_

let rec nf_tm (t : nf) =
  match t with
  | Lam_ t -> Lam (nf_tm t)
  | Neu t -> ne_tm t
and ne_tm (t : ne) =
  match t with
  | Var_ k -> Var k
  | App_(t,u) -> App(ne_tm t, nf_tm u)
  | Star_ -> Star

let pp_nf ppf (t : nf) = pp_tm ppf (nf_tm t)
let pp_ne ppf (t : ne) = pp_tm ppf (ne_tm t)

(* Type of weakenings *)
(* These are the morphisms in a category W,
   whose objects are contexts, and whose morphisms are generated by
    W_id : hom(Γ,Γ)
    W1 : hom(Γ, Δ) → hom(Γ×U, Δ)
    W2 : hom(U, Δ) → hom(Γ×U, Δ×U)
   Note that this is for a single base type.
 *)
type wk = W_id
        | W1 of wk
        | W2 of wk

(* type of values *)
type vl = UnitD of nf
        (* here we could easily keep track of the types if needed! *)
        | ArrD of (wk -> (vl -> vl))

let rec pp_vl ppf (u : vl) =
  match u with
  | UnitD s -> fprintf ppf "(UnitD %a)" pp_nf s
  | ArrD f -> fprintf ppf "ArrD"

(* Composition in W *)
(*  wk_o : hom(Γ,Δ) → hom(Δ,Ξ) → hom(Γ,Ξ)  *)
let rec wk_o (w1 : wk) (w2 : wk) : wk =
  match (w1, w2) with
  | W_id,  _ -> w2
  | W1 w1, w2 -> W1 (wk_o w1 w2)
  | W2 w1, W_id -> W2 w1
  | W2 w1, W1 w2 -> W1 (wk_o w1 w2)
  | W2 w1, W2 w2 -> W2 (wk_o w1 w2)

(* Compute the pullback t[w]  *)
let rec wk_nf (w : wk) (t : nf) : nf =
  match (w,t) with
  | W_id, _ -> t
  | _,    Lam_ s -> Lam_ (wk_nf (W2 w) s)
  | _,    Neu t -> Neu (wk_ne w t)
and wk_ne (w : wk) (t : ne) : ne =
  match (w,t) with
  | W_id, _ -> t
  | _,    Star_ -> Star_
  | _,    App_(t,u) -> App_(wk_ne w t, wk_nf w u)
  | W1 w, Var_ x -> Var_ (x + 1)
  | W2 w, Var_ x -> (if x = 0 then (Var_ 0) else (wk_ne w (Var_ (x - 1))))


(* Pullback a value *)
let wk_vl (w : wk) (u : vl) : vl =
  match u with
  | UnitD s -> UnitD (wk_nf w s)
  | ArrD f -> ArrD (fun w' u -> f (wk_o w' w) u)  (* Should this be (wk_o w w') ?? *)

let wk_env (w : wk) (env : vl list) : vl list =
  List.map (wk_vl w) env

let appD (u : vl) (v : vl) : vl =
  match u with
  | ArrD f -> f W_id v
  | _ -> failwith "Not a lambda!"

let rec eval (t : tm) (env : vl list) : vl =
  match t with
  | Star -> UnitD (Neu Star_)
  | Var x -> List.nth env x
  | Lam s -> ArrD (fun w u -> eval s (u::(wk_env w env)))
  | App(t,u) -> appD (eval t env) (eval u env)

and reify (a : ty) (u : vl) : nf =
  (printf "Reifying %a.@\n" pp_vl u);
  (let res =
     match (a,u) with
     | Unit, UnitD s -> s
     | Arr(a,b), ArrD f -> Lam_ (reify b (f (W1 W_id) (reflect a (Var_ 0))))
     | _ -> failwith "Failure in reify!"
   in (printf "Reified %a.@\n" pp_nf res); res)
and reflect (a : ty) (t : ne) : vl =
  (printf "Reflecting %a.@\n" pp_ne t);
  (let res =
     match (a,t) with
     | Arr(a,b), t -> ArrD(fun w u -> reflect b (App_(wk_ne w t, reify a u)))
     | Unit, _ -> UnitD (Neu t)
   in (printf "Reflected %a.@\n" pp_vl res); res)



let nbe (a : ty) (t : tm) : nf =
  reify a (eval t [])



(****************************************************************)
(* Tests                                                        *)
(****************************************************************)


let _I = Lam (Var 0)
let _K = Lam (Lam (Var 0))
(* (A -> (B -> C)) -> (A -> B) -> A -> C *)
let _S = Lam (Lam (Lam (App(App(Var 2, Var 0),App(Var 1, Var 0)))))

let _UU = Arr(Unit,Unit)
let _UUU = Arr(Unit,_UU)

let tests : (tm * ty) list
  = [(_I, _UU);
     (_K, _UUU);
     (Lam (Lam (App (Var 1,Var 0))), Arr (_UU, _UU));
     (Lam (App (_I, Var 0)), _UU);
     (Star, Unit);
     (App(_I, Star), Unit);
     (_S, Arr(_UUU,Arr(_UU,_UU)));   (* Normal form is incorrect!! *)
     (Lam(Lam (App(App(_K, Var 0),App(Var 1, Var 0)))), Arr(_UU,_UU));
     (App(Lam (Lam (App(App(Var 1,Var 0), App(_I, Var 0)))),_K), _UU);
     (* (App(Lam (fun x -> Lam (fun y -> App (App (App (Var x,Var y), S (Var y)), S (S (Var y))))),
      *      Lam (fun x -> Lam (fun y -> Lam (fun z -> Var z)))), Arr(Nat,Nat)); *)
    ]


let _ =
  for i=0 to (List.length tests) - 1 do
    (let p = (List.nth tests i) in
     (printf "test %d :: %a@\n" i pp_tm (fst p));
     (printf "> %a@\n" pp_nf (nbe (snd p) (fst p))))
  done