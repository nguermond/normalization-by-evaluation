open Format



(* types *)
type ty = Nat
        | Arr of ty * ty

(* syntax *)
type 'a tm = Z
           | S of ('a tm)
           | Rec of ty * ('a tm) * ('a tm)
           (* --------------- *)
           | Var of 'a
           | Lam of ('a -> 'a tm)
           | App of ('a tm) * ('a tm)

let rec pp_tm gensym pp_a ppf (t : 'a tm) =
  let pp_tm = (pp_tm gensym pp_a) in
  (match t with
   | Z -> fprintf ppf "Z"
   | S u -> fprintf ppf "(S %a)" pp_tm u
   | Rec (_,z,s) -> fprintf ppf "(Rec %a %a)" pp_tm z pp_tm s
   | Var x -> fprintf ppf "%a" pp_a x
   | Lam f -> (let x = gensym() in
               fprintf ppf "@[<1>(λ%a. %a)@]" pp_a x pp_tm (f x))
   | App (s,t) -> fprintf ppf "@[<1>(%a %a)@]" pp_tm s pp_tm t)



(* WHNF syntax *)
type 'a nf = Lam_ of ('a -> 'a nf)
           | Neu of ('a ne)
and 'a ne = App_ of ('a ne) * ('a nf)
          | Var_ of 'a
          | Z_
          | S_ of ('a nf)
          | Rec_ of ty * ('a nf) * ('a nf)


let rec nf_tm (t : 'a nf) : 'a tm =
  (match t with
   | Lam_ f -> Lam (fun x -> (nf_tm (f x)))
   | Neu n -> ne_tm n)
and ne_tm (t : 'a ne) : 'a tm =
  (match t with
   | App_ (t,u) -> App (ne_tm t, nf_tm u)
   | Var_ x -> Var x
   | Z_ -> Z
   | S_ u -> S (nf_tm u)
   | Rec_ (a,z,s) -> Rec (a,nf_tm z, nf_tm s))


(* semantics *)
type 'a vl = Num of int
           | Fun of ('a vl -> 'a vl)
           | Syn of 'a ne

let app (v : 'a vl) (u : 'a vl) : 'a vl =
  (match v with
   | Fun f -> (f u)
   | _ -> failwith "Ill-typed value: 'Fun'!.")

let zero : 'a vl = Num 0

let rec succ (v : 'a vl) : 'a vl =
  (match v with
   | Num k -> Num (k + 1)
   | Syn s -> Syn (S_ (Neu s))
   | Fun _ -> failwith "Ill-typed value 'Fun'!")

let rec nat_recD (a : ty) (z : 'a vl) (f : 'a vl) : 'a vl =
  Fun (fun v ->
      (match v with
       | Num k -> (if k = 0 then z
                   else (app f (app (nat_recD a z f) (Num (k - 1)))))
       | _ -> reflect a (App_ (Rec_ (a, reify a z, reify (Arr(a,a)) f), reify a v))))
(****************************************************************)
(* reify and reflect: from intermediate to target               *)
(****************************************************************)

(* takes semantic objects to normal terms *)
and reify (a : ty) (v : 'a vl) : 'a nf =
  (match (a,v) with
   | _, Syn n -> Neu n
   | Nat, Num k -> (if k>0 then (Neu (S_ (reify Nat (Num (k - 1)))))
                    else (Neu Z_))
   | Arr (a,b), Fun f -> Lam_ (fun v -> reify b (f (reflect a (Var_ v))))
   | _ -> failwith "Ill-typed value!")

(* takes neutral terms to semantic objects *)
and reflect (a : ty) (t : 'a ne) : 'a vl =
  (match a with
   | Nat -> Syn t
   | Arr (a,b) ->
      Fun (fun n -> (reflect b (App_ (t, reify a n)))))

let rec eval (t : ('a vl) tm) : 'a vl =
  (match t with
   | Z -> zero
   | S u -> succ (eval u)
   | Rec (a,z,s) -> nat_recD a (eval z) (eval s)
   | Var v -> v
   | Lam f -> Fun (fun v -> (eval (f v)))
   | App (t,u) -> app (eval t) (eval u))


let nbe (a : ty) (t : ('a vl) tm) : 'a nf =
  reify a (eval t)

(****************************************************************)
(* Tests                                                        *)
(****************************************************************)


let gensym =
  (let x = ref 0 in
   fun () ->
   incr x ;
   "x" ^ string_of_int !x)

let pp_var ppf s = Format.fprintf ppf "%s" s


let pp_tm_str = pp_tm gensym pp_var

let _1 = S Z
let _2 = S _1
let _3 = S _2
let _4 = S _3
let _5 = S _4
let _6 = S _5
let _7 = S _6
let _8 = S _7
let _9 = S _8

let _succ = Lam (fun x -> S (Var x))
let _I = Lam (fun x -> Var x)
let _K = Lam (fun x -> Lam (fun y -> Var y))
let _S = Lam (fun x -> Lam (fun y -> Lam (fun z -> App(App(Var x, Var z),App(Var y, Var z)))))
let _add = Lam (fun x -> Lam (fun y -> App(Rec(Nat, Var y, _succ),Var x)))
let _mul = Lam (fun x -> Lam (fun y -> App(Rec(Nat, Z, App(_add, Var x)), Var y)))

let tests : ('a tm * ty) list
  = [(Lam (fun x -> Var x), Arr (Nat,Nat));
     (Lam (fun f -> Lam (fun x -> App (Var f,Var x))), Arr (Arr (Nat,Nat), Arr (Nat, Nat)));
     (Lam (fun x -> App (Lam (fun y -> Var y), Var x)), Arr (Nat, Nat));
     (App (Lam (fun x -> S (Var x)), S Z), Nat);
     (Lam (fun x -> S (Var x)), Arr (Nat, Nat));
     (Lam (fun x -> App (Lam (fun x -> S (Var x)), S (Var x))), Arr (Nat, Nat));
     (Lam (fun x -> Lam (fun y -> App (Var x,Var y))), Arr(Arr (Nat, Nat), Arr (Nat, Nat)));
     (Lam (fun x -> Lam (fun y -> App (App (Var x,Var y), S (Var y)))), Arr(Arr (Nat, Arr (Nat, Nat)), Arr(Nat,Nat)));
     (Lam (fun x -> Lam (fun y -> App (App (App (Var x,Var y), S (Var y)), S (S (Var y))))), Arr(Arr (Nat, Arr (Nat, Arr (Nat, Nat))), Arr(Nat,Nat)));
     (Lam (fun x -> Lam (fun y -> Var y)), Arr(Nat,Arr(Nat,Nat)));
     (App(Lam (fun x -> Lam (fun y -> App (App (Var x,Var y), S (Var y)))),Lam (fun x -> Lam (fun y -> Var y))), Arr(Nat,Nat));
     (App(Lam (fun x -> Lam (fun y -> App (App (App (Var x,Var y), S (Var y)), S (S (Var y))))),
          Lam (fun x -> Lam (fun y -> Lam (fun z -> Var z)))), Arr(Nat,Nat));
     (_add, Arr(Nat,Arr(Nat,Nat)));
     (_mul, Arr(Nat,Arr(Nat,Nat)));
     (App(App(_add, _5), _7), Nat);
     (App(App(_mul, _3), _4), Nat);
     (Lam (fun x -> App(App(_mul, _3), Var x)), Arr(Nat,Nat));
    ]

let _ =
  for i=0 to (List.length tests) - 1 do
    (let p = (List.nth tests i) in
     let p' = (List.nth tests i) in
     (printf "test %d :: %a@\n" i pp_tm_str (fst p));
     (printf "> %a@\n" pp_tm_str (nf_tm (nbe (snd p') (fst p')))))
  done
