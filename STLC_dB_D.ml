open Format




(* types *)
type ty = Unit
        | Nat
        | Arr of ty * ty

type tm = Var of int
        | Star
        | Z
        | S of tm
        | Lam of tm
        | App of tm * tm

let pp_tm ppf (t : tm) =
  let rec pp_tm_ k ppf t =
    match t with
    | Star -> fprintf ppf "*"
    | Z -> fprintf ppf "Z"
    | S s -> fprintf ppf "(S %a)" (pp_tm_ k) s
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
       | Z_
       | S_ of nf

let rec nf_tm (t : nf) =
  match t with
  | Lam_ t -> Lam (nf_tm t)
  | Neu t -> ne_tm t
and ne_tm (t : ne) =
  match t with
  | Var_ k -> Var k
  | App_(t,u) -> App(ne_tm t, nf_tm u)
  | Star_ -> Star
  | Z_ -> Z
  | S_ s -> S (nf_tm s)

let pp_nf ppf (t : nf) = pp_tm ppf (nf_tm t)
let pp_ne ppf (t : ne) = pp_tm ppf (ne_tm t)

(***********************************************)
(* semantics                                   *)
(***********************************************)
type vl = LamD of (vl -> vl)
        | StarD
        | ZD
        | SD of vl
        | SynD of ne
        | BotD
let appD (u : vl) (v : vl) : vl =
  match u with
  | BotD -> BotD
  | LamD f -> (f v)
  | _ -> BotD

let rec eval (t : tm) (env : vl list) : vl =
  match t with
  | Var k -> List.nth env k
  | Lam s -> LamD (fun v -> (eval s (v::env)))
  | App (t,u) -> appD (eval t env) (eval u env)
  | Star -> StarD
  | Z -> ZD
  | S s -> SD (eval s env)

(****************************************************************)
(* reify and reflect: from intermediate to target               *)
(****************************************************************)
let lift_nf (t : nf) =
  let rec lift_nf_ k t =
    match t with
    | Lam_ s -> Lam_ (lift_nf_ (k+1) s)
    | Neu s -> Neu (lift_ne_ k s)
  and lift_ne_ k t =
    match t with
    | Var_ x -> Var_ (x + 1)
    | App_(t,u) -> App_(lift_ne_ k t, lift_nf_ k u)
    | Star_ -> Star_
    | Z_ -> Z_
    | S_ s -> S_ (lift_nf_ k s)
  in (lift_nf_ 0 t)

(* takes semantic objects to normal terms *)
let rec reify (a : ty) (v : vl) (k : int) : nf =
  match (a,v) with
  | _,         SynD s -> Neu s
  | Arr (a,b), u -> let k' = (k + 1) in
                    Lam_ (lift_nf (reify b (appD u (reflect a (Var_ (-k')) k' )) k'))
  | Unit,      StarD -> Neu Star_
  | Nat,       ZD -> Neu Z_
  | Nat,       SD s -> Neu (S_ (reify Nat s k))
  | _ -> failwith "Cannot reify ill-typed value!"

(* takes neutral terms to semantic objects *)
and reflect (a : ty) (t : ne) (k : int) : vl =
  match a with
  | Arr (a,b) -> LamD (fun v -> (reflect b (App_ (t, reify a v k)) k))
  | _ -> SynD t


let nbe (a : ty) (t : tm) : nf =
  reify a (eval t []) 0

(****************************************************************)
(* Tests                                                        *)
(****************************************************************)


let _I = Lam (Var 0)
let _K = Lam (Lam (Var 0))
(* (A -> (B -> C)) -> (A -> B) -> A -> C *)
let _S = Lam (Lam (Lam (App(App(Var 2, Var 0),App(Var 1, Var 0)))))

let _UU = Arr(Unit,Unit)
let _UUU = Arr(Unit,_UU)
let _NN = Arr(Nat,Nat)
let _NNN = Arr(Nat,_NN)

let tests : (tm * ty) list
  = [(_I, _UU);
     (_K, _UUU);
     (Lam (Lam (Var 1)), Arr(Unit,_UU));
     (Lam (Lam (App (Var 1,Var 0))), Arr (_UU, _UU));
     (Lam (App (_I, Var 0)), _UU);
     (Star, Unit);
     (App(_I, Star), Unit);
     (_S, Arr(_UUU,Arr(_UU,_UU)));
     (_S, Arr(Arr(Nat,Arr(Unit,Nat)),Arr(Arr(Nat,Unit),Arr(Nat,Nat))));
     (Lam(Lam (App(App(_K, Var 0),App(Var 1, Var 0)))), Arr(_UU,_UU));
     (App(Lam (Lam (App(App(Var 1,Var 0), App(_I, Var 0)))),_K), _UU);
     (Z, Nat);
     (S Z, Nat);
     (Lam(S (Var 0)), _NN);
     (App(Lam(S (Var 0)), S Z), Nat);
     (Lam(Lam(App(App(App(Var 1,S (S Z)),Star),Var 0))), Arr(Arr(Nat,Arr(Unit,_NN)),_NN));
    ]


let _ =
  for i=0 to (List.length tests) - 1 do
    (let p = (List.nth tests i) in
     (printf "test %d :: %a@\n" i pp_tm (fst p));
     (printf "> %a@\n" pp_nf (nbe (snd p) (fst p))))
  done
