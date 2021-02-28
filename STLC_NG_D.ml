open Format



(* types *)
type ty = Nat
        | Arr of ty * ty

(* syntax *)
type 'a tm = Z
           | S of ('a tm)
           | Var of 'a
           | Lam of ('a -> 'a tm)
           | App of ('a tm) * ('a tm)

let rec pp_tm gensym pp_a ppf (t : 'a tm) =
  (match t with
   | Z -> fprintf ppf "Z"
   | S u -> fprintf ppf "(S %a)" (pp_tm gensym pp_a) u
   | Var x -> fprintf ppf "%a" pp_a x
   | Lam f -> (let x = gensym() in fprintf ppf "@[<1>(λ%a. %a)@]" pp_a x (pp_tm gensym pp_a) (f x))
   | App (s,t) -> fprintf ppf "@[<1>(%a %a)@]" (pp_tm gensym pp_a) s (pp_tm gensym pp_a) t)



(* WHNF syntax *)
type 'a nf = Lam_ of ('a -> 'a nf)
           | Neu of ('a ne)
and 'a ne = App_ of ('a ne) * ('a nf)
          | Var_ of 'a
          | Z_
          | S_ of ('a nf)


let rec nf_tm (t : 'a nf) : 'a tm =
  (match t with
   | Lam_ f -> Lam (fun x -> (nf_tm (f x)))
   | Neu n -> ne_tm n)
and ne_tm (t : 'a ne) : 'a tm =
  (match t with
   | App_ (t,u) -> App (ne_tm t, nf_tm u)
   | Var_ x -> Var x
   | Z_ -> Z
   | S_ u -> S (nf_tm u))


(* semantics *)
type 'a vl = Num of int
           | Fun of ('a vl -> 'a vl)
           | Syn of 'a ne

let app (t : 'a vl) (u : 'a vl) : 'a vl =
  (match t with
   | Fun f -> (f u)
   | _ -> failwith "Not a function")

let rec succ : 'a vl =
  Fun (fun v ->
      (match v with
       | Num k -> Num (k + 1)
       | Syn s -> Syn (S_ (Neu s))
       | Fun _ -> failwith "Ill-typed value!"))

let rec eval (t : ('a vl) tm) : 'a vl =
  (* printf "@[<1>Evaluating:@\n@]"; *)
  (match t with
   | Z -> Num 0
   | S u -> app succ (eval u)
   | Var v -> v
   | Lam f -> Fun (fun v -> (eval (f v)))
   | App (t,u) -> app (eval t) (eval u))

(****************************************************************)
(* reify and reflect: from intermediate to target               *)
(****************************************************************)

(* takes semantic objects to normal terms *)
let rec reify (a : ty) (v : 'a vl) : 'a nf =
  (*printf "@[<1>Reifying!@\n@]";*)
  (match (a,v) with
   | _, Syn n -> Neu n
   | Nat, Num k -> (if k>0 then (Neu (S_ (reify Nat (Num (k - 1))))) else (Neu Z_))
   | Arr (a,b), Fun f -> Lam_ (fun v -> reify b (f (reflect a (Var_ v))))
   | _ -> failwith "Ill-typed value!")

(* takes neutral terms to semantic objects *)
and reflect (a : ty) (t : 'a ne) : 'a vl =
  (*printf "@[<1>Reflecting!@\n@]";*)
  (match a with
   | Nat -> Syn t
   | Arr (a,b) ->
      Fun (fun n -> (reflect b (App_ (t, reify a n)))))

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


let tests : ('a tm * ty) list
  = [(Lam (fun x -> Var x), Arr (Nat,Nat));
     (Lam (fun f -> Lam (fun x -> App (Var f,Var x))), Arr (Arr (Nat,Nat), Arr (Nat, Nat)));
     (Lam (fun x -> App (Lam (fun y -> Var y), Var x)), Arr (Nat, Nat));
     (Z, Nat);
     (S Z, Nat);
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
    ]

let _I = Lam (fun x -> Var x)
let _K = Lam (fun x -> Lam (fun y -> Var y))
let _S = Lam (fun x -> Lam (fun y -> Lam (fun z -> App(App(Var x, Var z),App(Var y, Var z)))))

let _ =
  for i=0 to (List.length tests) - 1 do
    (let p = (List.nth tests i) in
     let p' = (List.nth tests i) in
     (printf "test %d :: %a@\n" i pp_tm_str (fst p));
     (printf "> %a@\n" pp_tm_str (nf_tm (nbe (snd p') (fst p')))))
  done
