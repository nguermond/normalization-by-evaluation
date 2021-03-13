open Format

(****************************************************************)
(* Terms                                                        *)
(****************************************************************)
type 'a tm = Var of 'a
           (* Empty type *)
           | Empty
           | EmptyElim of ('a tm)
           (* Unit type *)
           | Unit
           | Star
           (* Boolean type *)
           | Bool
           | True
           | False
           | BoolElim of ('a tm) * ('a tm) * ('a tm) * ('a tm)
           (* Naturals (* Can be constructed using W + Bool + Unit + Empty *) *)
           | Z
           | S of ('a tm)
           | NatRec of ('a tm) * ('a tm) * ('a tm)
           | Nat
           (* W type *)
           | Sup of ('a tm) * ('a tm)
           | WRec of ('a tm) * ('a tm) * ('a tm)
           | W of ('a tm) * ('a -> 'a tm)
           (* Sigma type *)
           | Sigma of ('a tm) * ('a -> 'a tm)
           | DPair of ('a tm) * ('a tm)
           | P1 of ('a tm)
           | P2 of ('a tm)
           (* Pi type *)
           | Lam of ('a -> 'a tm)
           | App of ('a tm) * ('a tm)
           | Pi of ('a tm) * ('a -> 'a tm)
           (* Universe *)
           | Type

(****************************************************************)
(* Normal/Neutral terms                                         *)
(****************************************************************)
type 'a nf = Lam_ of ('a -> 'a nf)
           | Neu_ of ('a ne)
and 'a ne = App_ of ('a ne) * ('a nf)
          | Var_ of 'a
          | Z_
          | S_ of ('a nf)
          | NatRec_ of ('a nf) * ('a nf) * ('a nf)
          | Sup_ of ('a nf) * ('a nf)
          | WRec_ of ('a nf) * ('a nf) * ('a nf)
          | Nat_
          | Pi_ of ('a nf) * ('a -> 'a nf)
          | W_ of ('a nf) * ('a -> 'a nf)
          | Sigma_ of ('a nf) * ('a -> 'a nf)
          | Type_
          | Empty_
          | EmptyElim_ of ('a nf)
          | Unit_
          | Star_
          | Bool_
          | True_
          | False_
          | BoolElim_ of ('a nf) * ('a nf) * ('a nf) * ('a nf)
          | DPair_ of ('a nf) * ('a nf)
          | P1_ of ('a nf)
          | P2_ of ('a nf)



(****************************************************************)
(* Pretty printing                                              *)
(****************************************************************)
let rec pp_tm gensym pp_a ppf (t : 'a tm) =
  let pp_tm = (pp_tm gensym pp_a) in
  match t with
  | Z -> fprintf ppf "Z"
  | S u -> fprintf ppf "(S %a)" pp_tm u
  | NatRec(a,z,s) -> fprintf ppf "@[<4>(NatRec %a@ %a)@]" (* pp_tm a  *) pp_tm z pp_tm s
  | Sup(x,s) -> fprintf ppf "@[<4>(Sup %a@ %a)@]" pp_tm x pp_tm s
  | WRec(w,c,s) -> fprintf ppf "@[<4>(WRec %a)@]" (* pp_tm w pp_tm c *) pp_tm s
  | Var x -> fprintf ppf "%a" pp_a x
  | Lam f -> (let x = gensym() in
              fprintf ppf "@[<4>(λ%a. %a)@]" pp_a x pp_tm (f x))
  | App(s,t) -> fprintf ppf "@[<2>(%a@ %a)@]" pp_tm s pp_tm t
  | Nat -> fprintf ppf "Nat"
  | Pi(a,fam) -> (let x = gensym() in
                fprintf ppf "@[<4>(Π[%a:%a].@ %a)@]" pp_a x pp_tm a pp_tm (fam x))
  | Sigma(a,fam) -> (let x = gensym() in
                     fprintf ppf "@[<4>(Σ[%a:%a].@ %a)@]" pp_a x pp_tm a pp_tm (fam x))
  | W(a,fam) -> (let x = gensym() in
               fprintf ppf "@[<4>(W[%a:%a].@ %a)@]" pp_a x pp_tm a pp_tm (fam x))
  | Type -> fprintf ppf "★"
  | Empty -> fprintf ppf "Empty"
  | EmptyElim a -> fprintf ppf "EmptyE" (*pp_tm a*)
  | Unit -> fprintf ppf "Unit"
  | Star -> fprintf ppf "*"
  | Bool -> fprintf ppf "Bool"
  | True -> fprintf ppf "⊤"
  | False -> fprintf ppf "⊥"
  | BoolElim(_,b,s,t) -> fprintf ppf "@[<4>(if %a@ then %a@ else %a)@]" pp_tm b pp_tm s pp_tm t
  | DPair(s,t) -> fprintf ppf "@[<2>⟨%a, %a⟩@]" pp_tm s pp_tm t
  | P1(s) -> fprintf ppf "(π₁ %a)" pp_tm s
  | P2(s) -> fprintf ppf "(π₂ %a)" pp_tm s


(* Inject normal terms to terms *)
let rec nf_tm (t : 'a nf) : 'a tm =
  match t with
  | Lam_ f -> Lam (fun x -> nf_tm (f x))
  | Neu_ n -> ne_tm n
and ne_tm (t : 'a ne) : 'a tm =
  match t with
  | App_ (t,u) -> App (ne_tm t, nf_tm u)
  | Var_ x -> Var x
  | Z_ -> Z
  | S_ u -> S (nf_tm u)
  | NatRec_ (a,z,s) -> NatRec (nf_tm a,nf_tm z, nf_tm s)
  | Sup_(x,s) -> Sup(nf_tm x, nf_tm s)
  | WRec_ (w,c,lim) -> WRec (nf_tm w, nf_tm c, nf_tm lim)
  | Nat_ -> Nat
  | Pi_(a,fam) -> Pi(nf_tm a, fun x -> nf_tm (fam x))
  | W_(a,fam) -> W(nf_tm a, fun x -> nf_tm (fam x))
  | Sigma_(a,fam) -> Sigma(nf_tm a, fun x -> nf_tm (fam x))
  | Type_ -> Type
  | Empty_ -> Empty
  | EmptyElim_(a) -> EmptyElim(nf_tm a)
  | Unit_ -> Unit
  | Star_ -> Star
  | Bool_ -> Bool
  | True_ -> True
  | False_ -> False
  | BoolElim_(a,b,s,t) -> BoolElim(nf_tm a, nf_tm b, nf_tm s, nf_tm t)
  | DPair_(s,t) -> DPair(nf_tm s, nf_tm t)
  | P1_(s) -> P1(nf_tm s)
  | P2_(s) -> P2(nf_tm s)

let gensym : unit -> string =
  (let x = ref 0 in
   fun () ->
   incr x ;
   "x" ^ string_of_int !x)

let pp_var ppf s = Format.fprintf ppf "%s" s

let pp_tm_str = pp_tm gensym pp_var

(****************************************************************)
(* Values                                                       *)
(****************************************************************)
type 'a vl = PiD of ('a vl) * ('a vl -> 'a vl)
           | WD of ('a vl) * ('a vl -> 'a vl)
           | SigmaD of ('a vl) * ('a vl -> 'a vl)
           | NatD
           | TypeD
           | EmptyD
           | UnitD
           | BoolD
           | StarD
           | TrueD
           | FalseD
           | EmptyElimD of ('a vl)
           | LamD of ('a vl -> 'a vl)
           | ZD
           | SD of ('a vl)
           | SupD of ('a vl) * ('a vl)
           | DPairD of ('a vl) * ('a vl)
           | SynD of ('a ne)
           | BotD

let arrD (a : 'a vl) (b : 'a vl) : ('a vl) = PiD(a, fun _ -> b)

(* We need to use reflect here! *)
let sigma_P1D (u : 'a vl) : 'a vl =
  match u with
  | DPairD(v,_) -> v
  | SynD s -> SynD (P1_(Neu_ s))
  | _ -> BotD

let sigma_P2D (u : 'a vl) : 'a vl =
  match u with
  | DPairD(_,v) -> v
  | SynD s -> SynD (P2_(Neu_ s))
  | _ -> BotD

let dpairD (u : 'a vl) (v : 'a vl) : 'a vl =
  match (u,v) with
  | SynD(P1_(Neu_ s)), SynD(P2_(Neu_ t)) when s = t -> SynD(s)
  | _ -> DPairD(u,v)

let appD (t : 'a vl) (u : 'a vl) : ('a vl) =
  match (t,u) with
  | _, BotD -> BotD
  | LamD f,_ -> (f u)
  | _ -> BotD

let rec nat_recD (a : 'a vl) (z : 'a vl) (f : 'a vl) : 'a vl =
  LamD (fun v ->
      match v with
      | ZD -> z
      | SD u -> (appD f (appD (nat_recD a z f) u))
      | _ -> reflect a (App_(NatRec_(reifyT a, reify a z, reify (arrD a a) f), reify a v)))

(* For a W-Type W(A,x.B), we have
     sup : (x : A) -> (B(x) -> W(A,x.B)) -> W(A,x.B)
   so to eliminate into a type C, we need
     lim : (x : A) -> (B(x) -> C) -> C  *)
and w_recD (w : 'a vl) (c : 'a vl) (lim : 'a vl) : 'a vl =
  LamD (fun v ->
      match (v,w) with
      | SupD(x,s), _ -> appD (appD lim x) (LamD (fun u -> appD (w_recD w c lim) (appD s u)))
      | _,         WD(a,fam) -> reflect c (App_(WRec_(reifyT w, reifyT c,
                                                      reify (PiD(a,fun u -> arrD (arrD (fam u) c) c)) lim), reify c v))
      (* What if the type does not evaluate to WD(_,_)?? maybe because it depends on some variable *)
      | _ -> failwith "Ill-typed w_recD!")

and bool_elimD (a : 'a vl) (b : 'a vl) (u : 'a vl) (v : 'a vl) : 'a vl =
  match b with
  | TrueD -> u
  | FalseD -> v
  | _ -> reflect a (BoolElim_(reifyT a, reify BoolD b, reify a u, reify a v))

and eval (t : ('a vl) tm) : ('a vl) =
  match t with
  | Z -> ZD
  | S u -> SD (eval u)
  | NatRec(a,z,s) -> nat_recD (eval a) (eval z) (eval s)
  | Sup(x,s) -> SupD(eval x, eval s)
  | WRec(w,c,s) -> w_recD (eval w) (eval c) (eval s)
  | Var v -> v
  | Lam f -> LamD (fun v -> eval (f v))
  | App(s,u) -> appD (eval s) (eval u)
  | Nat -> NatD
  | Pi(a,fam) -> PiD(eval a, fun v -> eval (fam v))
  | W(a,fam) -> WD(eval a, fun v -> eval (fam v))
  | Sigma(a,fam) -> SigmaD(eval a, fun v -> eval (fam v))
  | Type -> TypeD
  | Empty -> EmptyD
  | EmptyElim(a) -> EmptyElimD (eval a)
  | Unit -> UnitD
  | Star -> StarD
  | Bool -> BoolD
  | True -> TrueD
  | False -> FalseD
  | BoolElim(a,b,s,t) -> bool_elimD (eval a) (eval b) (eval s) (eval t)
  | DPair(s,t) -> dpairD (eval s) (eval t)
  | P1(s) -> sigma_P1D (eval s)
  | P2(s) -> sigma_P2D (eval s)

and reifyT (a : 'a vl) : ('a nf) =
  match a with
  | NatD -> Neu_ Nat_
  | TypeD -> Neu_ Type_
  | PiD(a,fam) -> Neu_ (Pi_(reifyT a, fun x -> reifyT (fam (reflect a (Var_ x)))))
  | WD(a,fam) -> Neu_ (W_(reifyT a, fun x -> reifyT (fam (reflect a (Var_ x)))))
  | SigmaD(a,fam) -> Neu_ (Sigma_(reifyT a, fun x -> reifyT (fam (reflect a (Var_ x)))))
  | EmptyD -> Neu_ Empty_
  | UnitD -> Neu_ Unit_
  | BoolD -> Neu_ Bool_
  | SynD t -> Neu_ t
  | _ -> failwith "Not a type!"

and reify (a : 'a vl) (v : 'a vl) : ('a nf) =
  match (a,v) with
  | _, EmptyElimD b -> Neu_ (EmptyElim_ (reifyT b))  (* Why is this needed? *)
  | PiD(a,fam), g -> Lam_ (fun x -> (let v = (reflect a (Var_ x)) in
                                     reify (fam v) (appD g v)))
  | WD(a,fam), SupD(u,s) -> Neu_ (Sup_(reify a u, reify (PiD(fam u, fun _ -> WD(a,fam))) s))
  | SigmaD(a,fam), DPairD(u,v) -> Neu_ (DPair_(reify a u, reify (fam u) v))
  | TypeD, a -> reifyT a
  | NatD, ZD -> Neu_ Z_
  | NatD, SD u -> Neu_ (S_ (reify NatD u))
  | UnitD, _ -> Neu_ Star_
  | _, TrueD -> Neu_ True_
  | _, FalseD -> Neu_ False_
  | _, StarD -> Neu_ Star_
  | _, SynD t -> Neu_ t
  | SynD neu, _ -> (printf "%a@\n" pp_tm_str (ne_tm neu)); failwith "Failed to reify value!"
  | _, BotD -> failwith "Cannot reify BotD!"
  | BotD, _ -> failwith "Cannot reify value of type BotD!"
  | _ -> failwith "Cannot reify ill-typed value!"

and reflect (a : 'a vl) (t : 'a ne) : ('a vl) =
  match a with
  | PiD(a,fam) -> LamD (fun v -> reflect (fam v) (App_(t, reify a v)))
  | BotD -> failwith "Cannot reflect term of type BotD!"
  | _ -> SynD t


let nbe (a : ('a vl) tm) (t : ('a vl) tm) : 'a nf =
  reify (eval a) (eval t)

let nbeT (a : ('a vl) tm) : 'a nf =
  reifyT (eval a)

(****************************************************************)
(* Tests                                                        *)
(****************************************************************)

(* Combinators for the lambda calculus *)
let _I = Lam (fun x -> Var x)
let _K = Lam (fun x -> Lam (fun y -> Var y))
let _S = Lam (fun x -> Lam (fun y -> Lam (fun z -> App(App(Var x, Var z),App(Var y, Var z)))))


(* Constructions with natural numbers *)
let _succ = Lam (fun x -> S (Var x))
let _add = Lam (fun x -> Lam (fun y -> App(NatRec(Nat, Var y, _succ),Var x)))
let _mul = Lam (fun x -> Lam (fun y -> App(NatRec(Nat, Z, App(_add, Var x)), Var y)))
(* The Ackermann function *)
let _ack = NatRec(Pi(Nat,fun _ -> Nat), _succ, Lam(fun f -> NatRec(Nat, App(Var f, S Z), Var f)))

let _1 = S Z
let _2 = S _1
let _3 = S _2
let _4 = S _3
let _5 = S _4
let _6 = S _5
let _7 = S _6
let _8 = S _7
let _9 = S _8


(* Construct Nat as a W-type using Bool, Unit, and Empty with constructors
     wZ : (Empty -> wNat) -> wNat
     wS : (Unit -> wNat) -> wNat
   and eliminator
     wNatRec : (a : Type) -> (z : a) -> (f : a -> a) -> wNat -> a  *)
let _wNat = W(Bool,fun b -> BoolElim(Type,Var b,Unit,Empty))
let _wZ = Sup(False, EmptyElim _wNat)
let _wS = Lam (fun n -> Sup(True, Lam (fun _ -> Var n)))
let _wadd = Lam (fun x -> Lam (fun y -> App(WRec(_wNat, _wNat, Lam (fun b -> Lam (fun s -> BoolElim(_wNat,Var b,App(_wS,App(Var s,Star)),Var y)))), Var x)))
let _wmul = Lam (fun x -> Lam (fun y -> App(WRec(_wNat, _wNat, Lam (fun b -> Lam (fun s -> BoolElim(_wNat,Var b, App(App(_wadd, Var x),App(Var s,Star)), _wZ)))), Var y)))
let _wNatRec = Lam (fun a -> Lam (fun z -> Lam (fun f -> WRec(_wNat, Var a, Lam (fun b -> Lam (fun s -> BoolElim(Var a, Var b, App(Var f, App(Var s, Star)), Var z)))))))
let _wadd' = Lam (fun x -> Lam (fun y -> App(App(App(App(_wNatRec, _wNat), Var y), _wS),Var x)))

let _w1 = App(_wS,_wZ)
let _w2 = App(_wS, _w1)
let _w3 = App(_wS, _w2)
let _w4 = App(_wS, _w3)
let _w5 = App(_wS, _w4)
let _w6 = App(_wS, _w5)
let _w7 = App(_wS, _w6)
let _w8 = App(_wS, _w7)
let _w9 = App(_wS, _w8)


(* To construct ordinals, we need the three element type:
     Three = Bool + Unit
   with constructors
     zero, one, two : Three
   and eliminator
     ThreeElim : (a : Type) -> Three -> a -> a -> a -> a   *)
let _Three = Sigma(Bool, fun b -> BoolElim(Type,Var b, Bool, Unit))
let _zero = DPair(False, Star)
let _one = DPair(True,False)
let _two = DPair(True,True)
let _ThreeElim = Lam (fun a -> Lam (fun t -> Lam (fun x0 -> Lam (fun x1 -> Lam (fun x2 -> BoolElim(Var a,P1(Var t),BoolElim(Var a,P2(Var t),Var x2,Var x1),Var x0))))))


(* Construct Type of ordinals as a W-type using Three, Empty, Unit, and Nat with constructors
     OrdZ : (Empty -> Ord) -> Ord
     OrdS : (Unit -> Ord) -> Ord
     OrdLim : (Nat -> Ord) -> Ord
   and eliminator
     OrdRec : (a : Type) -> a -> (a -> a) -> ((Nat -> a) -> a) -> Ord -> a   *)
let _Ord = W(_Three, fun t -> App(App(App(App(App(_ThreeElim,Type),Var t), Empty), Unit), Nat))
let _OrdZ = Sup(_zero, EmptyElim _Ord)
let _OrdS = Lam (fun x -> Sup(_one, Lam (fun _ -> Var x)))
let _OrdLim = Lam (fun f -> Sup(_two, Var f))
let _OrdRec = Lam (fun a -> Lam (fun z -> Lam (fun succ -> Lam (fun lim -> WRec(_Ord, Var a, Lam (fun t -> Lam (fun s ->
                                                          App(App(App(App(App(_ThreeElim,Var a), Var t), Var z), App(Var succ,App(Var s, Star))), App(Var lim, Var s)))))))))

let _OrdAdd = Lam (fun u -> Lam (fun v -> App(App(App(App(App(_OrdRec, _Ord), Var u), _OrdS), _OrdLim), Var v)))
let _OrdMul = Lam (fun u -> Lam (fun v -> App(App(App(App(App(_OrdRec, _Ord), _OrdZ), Lam (fun w -> App(App(_OrdAdd, Var w), Var u))), _OrdLim), Var v)))
let _OrdExp = Lam (fun u -> Lam (fun v -> App(App(App(App(App(_OrdRec, _Ord), App(_OrdS,_OrdZ)), Lam (fun w -> App(App(_OrdMul, Var w), Var u))), _OrdLim), Var v)))


(* some ordinals *)
let _add_omega = Lam (fun ord -> App(_OrdLim, Lam (fun n -> App(NatRec(_Ord,Var ord,_OrdS), Var n))))
let _omega = App(_add_omega, _OrdZ)
let _add_omega_2 = Lam (fun ord -> App(_OrdLim, Lam (fun n -> App(NatRec(_Ord,Var ord, _add_omega), Var n))))
let _omega_2 = App(_add_omega_2, _OrdZ)
let _add_omega_3 = Lam (fun ord -> App(_OrdLim, Lam (fun n -> App(NatRec(_Ord, Var ord, _add_omega_2), Var n))))
let _omega_3 = App(_add_omega_3, _OrdZ)
let _add_omega_n = Lam (fun m -> App(NatRec(Pi(_Ord,fun _ -> _Ord), _I,
                                             Lam (fun add_omega_n -> Lam (fun ord -> App(_OrdLim, Lam (fun n -> App(NatRec(_Ord, Var ord, Var add_omega_n), Var n)))))), Var m))
let _omega_omega = App(_OrdLim, Lam (fun n -> App(App(_add_omega_n, Var n), _OrdZ)))

let _epsilon_0 = App(_OrdLim, Lam (fun n -> App(NatRec(_Ord,_omega, App(_OrdExp,_omega)), Var n)))


(* Tests should be of the form (term, type) *)
let tests
  = [(_succ, Pi(Nat,fun _ -> Nat));
     (Lam (fun f -> Lam (fun x -> App (Var f,Var x))), Pi(Pi(Nat,fun _ -> Nat), fun _ -> Pi(Nat,fun _ -> Nat)));
     (Lam (fun x -> App (Lam (fun y -> Var y), Var x)), Pi(Nat,fun _ -> Nat));
     (App (Lam (fun x -> S (Var x)), S Z), Nat);
     (Lam (fun x -> S (Var x)), Pi(Nat,fun _ -> Nat));
     (Lam (fun x -> App (Lam (fun x -> S (Var x)), S (Var x))), Pi(Nat,fun _ -> Nat));
     (Lam (fun x -> Lam (fun y -> App (Var x,Var y))), Pi(Pi(Nat,fun _ -> Nat), fun _ -> Pi(Nat,fun _ -> Nat)));
     (Lam (fun x -> Lam (fun y -> App (App (Var x,Var y), S (Var y)))), Pi(Pi(Nat,fun _ -> Pi(Nat,fun _ -> Nat)), fun _ -> Pi(Nat,fun _ -> Nat)));
     (Lam (fun x -> Lam (fun y -> Var y)), Pi(Nat,fun _ -> Pi(Nat,fun _ -> Nat)));
     (App(Lam (fun x -> Lam (fun y -> App (App (Var x,Var y), S (Var y)))), _K), Pi(Nat,fun _ -> Nat));
     (App(Lam (fun x -> Lam (fun y -> App (App (App (Var x,Var y), S (Var y)), S (S (Var y))))),
          Lam (fun x -> Lam (fun y -> Lam (fun z -> Var z)))), Pi(Nat,fun _ -> Nat));
     (Lam (fun id -> App(App(Var id,App(Lam (fun x -> Var x), Z)),Z)), Pi(Pi(Nat,fun _ -> Pi(Nat,fun _ -> Type)),fun _ -> Type));
     (_add, Pi(Nat,fun _ -> Pi(Nat,fun _ -> Nat)));
     (_mul, Pi(Nat,fun _ -> Pi(Nat,fun _ -> Nat)));
     (App(App(_add, _5), _7), Nat);
     (App(App(_mul, _3), _4), Nat);
     (Lam (fun x -> App(App(_mul, _3), Var x)), Pi(Nat,fun _ -> Nat));
     (App(App(_ack, _2), App(App(_mul,_2),_3)), Nat);
     (Empty, Type);
     (Unit, Type);
     (Bool, Type);
     (BoolElim(Type,False,Empty,Bool), Type);
     (EmptyElim Unit, Pi(Empty, fun _ -> Unit));
     (EmptyElim Bool, Pi(Empty, fun _ -> Bool));
     (App(_wS,App(_wS,App(_wS,App(_wS,_wZ)))), _wNat);
     (BoolElim(_wNat,False,App(_wS,App(Lam (fun x -> _wZ),Star)),_wZ), _wNat);
     (App(WRec(_wNat, Unit, Lam (fun b ->
                                Lam (fun s ->
                                    BoolElim(Unit,Var b,App(_wS,App(Var s,Star)),Star)))), _wZ), Unit);
     (_wS, Pi(_wNat, fun _ -> _wNat));
     (App(WRec(_wNat, _wNat, Lam (fun b ->
                             Lam (fun s ->
                                 BoolElim(_wNat,Var b,App(_wS,App(Var s,Star)),App(_wS,App(_wS,App(_wS,_wZ))))))),App(_wS,App(_wS,_wZ))), _wNat);
     (NatRec(Nat, Z, _succ), Pi(Nat,fun _ -> Nat));
     (WRec(_wNat, _wNat, Lam (fun b ->
                             Lam (fun s ->
                                 BoolElim(_wNat,Var b,App(_wS,App(Var s,Star)),_wZ)))), Pi(_wNat, fun _ -> _wNat));

     (_wmul, Pi(_wNat, fun _ -> Pi(_wNat, fun _ -> _wNat)));
     (App(App(_wmul,_w3),_w7), _wNat);
     (_wadd', Pi(_wNat, fun _ -> Pi(_wNat, fun _ -> _wNat)));
     (App(App(_wadd', _w5), _w3), _wNat);
     (Sigma(Bool,fun b -> (BoolElim(Type,Var b, Unit, Nat))), Type);
     (DPair(False, S Z), Sigma(Bool,fun b -> (BoolElim(Type,Var b, Unit, Nat))));
     (P1(DPair(False,S Z)), Bool);
     (P2(DPair(False,S Z)), Nat);
     (Lam (fun p -> DPair(P1(Var p), P2(P1(DPair(Var p,Z))))), Pi(Sigma(Bool,fun b -> (BoolElim(Type,Var b, Unit, Nat))),
                                                                  fun _ -> Sigma(Bool,fun b -> (BoolElim(Type,Var b, Unit, Nat)))));
     (App(App(App(App(App(_ThreeElim,Nat),_zero),Z),S Z), S (S Z)), Nat);
     (_OrdRec, Pi(Type,fun a -> Pi(Var a,fun _ -> Pi(Pi(Var a, fun _ -> Var a), fun _ -> Pi(Pi(Pi(Nat, fun _ -> Var a), fun _ -> Var a), fun _ -> Pi(_Ord, fun _ -> Var a))))));
     (_omega, _Ord);
     (_omega_2, _Ord);
     (_omega_3, _Ord);
     (_epsilon_0, _Ord);
     (_add_omega, Pi(_Ord, fun _ -> _Ord));
     (App(App(_OrdAdd,_omega),_omega), _Ord);
     (App(_OrdAdd,_omega), Pi(_Ord, fun _ -> _Ord));
     (_OrdAdd, Pi(_Ord, fun _ -> Pi(_Ord, fun _ -> _Ord)));
     (* These do not work!*)
     (* (_add_omega_n, Pi(Nat,fun _ -> Pi(_Ord, fun _ -> _Ord)));
      * (_omega_omega, _Ord); *)
    ]


let _ =
  for i=0 to (List.length tests) - 1 do
    (let p = (List.nth tests i) in
     let p' = (List.nth tests i) in
     (printf "test %d :: %a@\n" i pp_tm_str (fst p));
     (printf "> %a@\n" pp_tm_str (nf_tm (nbe (snd p') (fst p')))))
  done
