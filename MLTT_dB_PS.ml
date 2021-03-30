open Format
open List

(* Note: Here as well we need to introduce "large elimination" for Bool *)
type tm = Var of int
        | App of tm * tm
        | Lam of tm
        (* Internal types for MLTT                                                 *)
        | Empty              (* Empty : U                                          *)
        | EmptyE             (* EmptyE : (a : U) -> El Empty -> El a               *)
        | Unit               (* Unit : U                                           *)
        | Star               (* star : El Unit                                     *)
        | Bool               (* Bool : U                                           *)
        | True               (* true : El Bool                                     *)
        | False              (* false : El Bool                                    *)
        | BoolE              (* BoolE : (a : U) -> El Bool -> El a -> El a -> El a *)
        | IPi                (* IPi : (a : U) -> (b : El a -> U) -> U                                         *)
        | Ilam               (* Ilam : (a : U) -> (b : El a -> U) -> ((x : El a) -> El (b x)) -> El (IPi a b) *)
        | Iapp               (* Iapp : (a : U) -> (b : El a -> U) -> El (IPi a b) -> (x : El a) -> El (b x)   *)
        | ISig               (* ISig : (a : U) -> (b : El a -> U) -> U                                        *)
        | Pair               (* Pair : (a : U) -> (b : El a -> U) -> (x : El a) -> El (b x) -> El (ISig a b)  *)
        | P1                 (* P1 : (a : U) -> (b : El a -> U) -> El (ISig a b) -> El a                      *)
        | P2                 (* P2 : (a : U) -> (b : El a -> U) -> (p : El (ISig a b)) -> El (b (P1 a b p))   *)
(*      | IW    *)           (* IW : (a : U) -> (b : El a -> U) -> U                                          *)
(*      | WRec  *)           (* WRec : (a : U) -> (b : El a -> U) -> (c : U)
                                       -> El c -> (El c -> El c) -> ((x : El a) -> (b x -> c) -> c)
                                       -> (El (IW a b)) -> El c                                               *)
(* I don't think we need equality here, we can define it as an inductive type... *)
(*      | Eq    *)           (* Eq : (a : U) -> (x y : El a) -> U                                             *)
(*      | Refl  *)           (* refl : (a : U) -> (x : El a) -> (Eq a x x)                                    *)


(* ◻ is the judgement `Kind`, ★ is the judgement `Type`.
 * Elements of ty are referred to as "Sets", "Sorts", or "Kinds"
 * Whereas terms of type U are referred to as "Types"              *)
type ty = U (* Type *)     (* Type is a kind, ie. (★ : ◻)         *)
        | El of tm         (* Every type is a kind , ie. (★ ≤ ◻)  *)
        | Pi of ty * ty    (* Pi ~ (◻,◻)                          *)

type sub = tm list
type con = ty list


(****************************************************)
(* Pretty printing                                  *)
(****************************************************)

(* Note: A neutral application does not need parentheses,
 * so there should be a pretty printing function for normalized terms *)
let rec pp_tm_ k ppf t =
  match t with
  | Var x -> fprintf ppf "x%d" (k - x)
  | Lam s -> fprintf ppf "@[<1>(λx%d. %a)@]" (k + 1) (pp_tm_ (k + 1)) s
  | App(t,u) -> fprintf ppf "@[<1>(%a@ %a)@]" (pp_tm_ k) t (pp_tm_ k) u
  | Empty -> fprintf ppf "𝟘"
  | Unit -> fprintf ppf "𝟙"
  | Bool -> fprintf ppf "𝟚"
  | True -> fprintf ppf "true"
  | False -> fprintf ppf "false"
  | Star -> fprintf ppf "*"
  | EmptyE -> fprintf ppf "EmptyE"
  | BoolE -> fprintf ppf "BoolE"
  | IPi -> fprintf ppf "Π"
  | Ilam -> fprintf ppf "ƛ"
  | Iapp -> fprintf ppf "·"
  | ISig -> fprintf ppf "Σ"
  | Pair -> fprintf ppf "Pair"
  | P1 -> fprintf ppf "π₁"
  | P2 -> fprintf ppf "π₂"
let pp_tm ppf (t : tm) = (pp_tm_ 0 ppf t)

let rec pp_sub_ k ppf (gamma : sub) =
  match gamma with
  | [] -> fprintf ppf "ε"
  | t::gamma -> fprintf ppf "⟨%a , %a⟩" (pp_sub_ k) gamma (pp_tm_ k) t
let pp_sub ppf gamma = pp_sub_ 0 ppf gamma

let rec pp_ty_ k ppf a =
  match a with
  | U -> fprintf ppf "Type"
  | El a -> fprintf ppf "%a" (pp_tm_ k) a
  | Pi(a,fam) -> (fprintf ppf "([x%d:%a] -> %a)"
                    (k + 1) (pp_ty_ k) a (pp_ty_ (k + 1)) fam)
let pp_ty ppf (a : ty) = (pp_ty_ 0 ppf a)


let rec pp_con_ l k ppf (ctx : con) =
  match ctx with
  | [] -> fprintf ppf "@[<3>"
  | a :: ctx -> (fprintf ppf "%a@ ▹ x%d:%a"
                   (pp_con_ l (k + 1)) ctx (l - k) (pp_ty_ (l - k - 1)) a)
let pp_con ppf ctx = (pp_con_ (length ctx) 0 ppf ctx); (fprintf ppf "@]")


let pp_ty_con ppf ((ctx,a) : con * ty) =
  (fprintf ppf "@[<3>%a@ ⊢ %a@]"
     pp_con ctx (pp_ty_ (length ctx)) a)

let pp_tm_ty_con ppf ((ctx,a,t) : con * ty * tm) =
  (fprintf ppf "@[<3>%a@ @[<2>⊢ %a@ : %a@]@]"
     pp_con ctx (pp_tm_ (length ctx)) t (pp_ty_ (length ctx)) a)



(****************************************************)
(* Type of weakenings                               *)
(****************************************************)
(* These are the morphisms in a category W,
 * whose objects are contexts, and whose morphisms are generated by
 *  W_id : hom(Γ,Γ)
 *  W1 : hom(Γ, Δ) → hom(Γ×U, Δ)
 *  W2 : hom(U, Δ) → hom(Γ×U, Δ×U)
 * Note that this is for a single base type.    *)

type wk = W_id
        | W1 of wk
        | W2 of wk

let rec pp_wk ppf (w : wk) =
  match w with
  | W_id -> fprintf ppf "W_id"
  | W1 w -> fprintf ppf "(W1 %a)" pp_wk w
  | W2 w -> fprintf ppf "(W2 %a)" pp_wk w


(* Composition in W *)
(*  wk_o : hom(Γ,Δ) → hom(Δ,Ξ) → hom(Γ,Ξ)  *)
let rec wk_o (w1 : wk) (w2 : wk) : wk =
  match (w1, w2) with
  | W_id,  _ -> w2
  | W1 w1, w2 -> W1 (wk_o w1 w2)
  | W2 w1, W_id -> W2 w1
  | W2 w1, W1 w2 -> W1 (wk_o w1 w2)
  | W2 w1, W2 w2 -> W2 (wk_o w1 w2)

(****************************************************)
(* type of normal/neutral terms                     *)
(****************************************************)

type nf = NLam of nf   (* Normal terms of type Pi *)
        | NeuU of ne   (* Normal terms of type U *)
        | NeuEl of ne  (* Normal terms of type El *)
and ne = Var_ of int
       | App_ of ne * nf
       (* MLTT *)
       | Empty_
       | Unit_
       | Bool_
       | Star_
       | True_
       | False_
       | EmptyE_
       | BoolE_
       | IPi_
       | Ilam_
       | Iapp_
       | ISig_
       | Pair_
       | P1_
       | P2_

type nesub = ne list

let id (n : int) : nesub =
  let rec id_ k n =
    (if (n = 0) then []
     else (Var_ k) :: (id_ (k + 1) (n - 1)))
  in (id_ 0 n)


let rec nf_tm (t : nf) =
  match t with
  | NLam t -> Lam (nf_tm t)
  | NeuU t -> ne_tm t
  | NeuEl t -> ne_tm t
and ne_tm (t : ne) =
  match t with
  | Var_ k -> Var k
  | App_(t,u) -> App(ne_tm t, nf_tm u)
  (* MLTT *)
  | Empty_ -> Empty
  | Unit_ -> Unit
  | Bool_ -> Bool
  | Star_ -> Star
  | True_ -> True
  | False_ -> False
  | EmptyE_ -> EmptyE
  | BoolE_ -> BoolE
  | IPi_ -> IPi
  | Ilam_ -> Ilam
  | Iapp_ -> Iapp
  | ISig_ -> ISig
  | Pair_ -> Pair
  | P1_ -> P1
  | P2_ -> P2

let pp_nf ppf (t : nf) = pp_tm ppf (nf_tm t)
let pp_ne ppf (t : ne) = pp_tm ppf (ne_tm t)

(* Compute the pullback t[w] for the presheaves Nf/Ne *)
let rec wk_nf (w : wk) (t : nf) : nf =
  match (w,t) with
  | W_id, _ -> t
  | _,    NLam s -> NLam (wk_nf (W2 w) s)
  | _,    NeuU t -> NeuU (wk_ne w t)
  | _,    NeuEl t -> NeuEl (wk_ne w t)
and wk_ne (w : wk) (t : ne) : ne =
  match (w,t) with
  | W_id, _ -> t
  | _,    App_(t,u) -> App_(wk_ne w t, wk_nf w u)
  | W1 w, Var_ x -> wk_ne w (Var_ (x + 1))
  | W2 w, Var_ x -> (if x = 0 then (Var_ 0) else (wk_ne w (Var_ (x - 1))))
  (* MLTT *)
  | _, Empty_ | _, Unit_ | _, Bool_ -> t
  | _, Star_ | _, True_ | _, False_ -> t
  | _, EmptyE_ | _, BoolE_ -> t
  | _, IPi_ | _, Ilam_ | _, Iapp_ -> t
  | _, ISig_ | _, Pair_ | _, P1_ | _, P2_ -> t


(****************************************************)
(* Values                                           *)
(****************************************************)
(* Term values
 * Γ ⊢ t : U         -->  ⟦t⟧(Δ,α) : Nf(Δ,U)
 * Γ ⊢ t : (El s)    -->  ⟦t⟧(Δ,α) : Nf(Δ, El ⟦s⟧(Δ,α))
 * Γ ⊢ t : (Pi A B)  -->  ⟦t⟧(Δ,α) : ⟦Pi A B⟧(Δ,α)                   *)
type vltm = UD of nf
          | ElD of nf
          | PiD of (wk -> (vltm -> vltm))

(* Type values
 * Γ ⊢ A type        -->  α : ⟦Γ⟧(Δ) ⊢ ⟦A⟧(α) : Set
 * ⟦U⟧(Δ,α) = Nf(Δ,U)
 * ⟦El t⟧(Δ,α) = Nf(Δ,El ⟦t⟧(Δ,α))
 * ⟦Pi A B⟧(Δ,α) = (w : 𝕎) -> (x: ⟦A⟧(Ξ, α[w]) -> ⟦B⟧(Ξ, (a[w],x))  *)
type vlty = VU
          | VEl of vltm
          | VPi of vlty * (wk -> (vltm -> vlty))

(* Substitution values
 * Γ ⊢ γ : Δ         -->  α : ⟦Γ⟧(Ξ) ⊢ ⟦γ⟧(Ξ,α) : ⟦Δ⟧(Ξ)
 * ⟦ε⟧(Ξ,α) : ⟦·⟧(Ξ)
 * ⟦⟨ γ , t⟩⟧(Ξ,α) : ⟦Δ ▹ A⟧(Ξ)                                       *)
type vlsub = vltm list

(* Context values
 * ⟦Γ⟧ : Set
 * ⟦·⟧(Δ) = 𝟙
 * ⟦Γ ▹ A⟧(Δ) = Σ ⟦Γ⟧(Δ) (λ α -> ⟦A⟧(Δ,α))                            *)
type vlcon = (vlsub -> vlty) list


(* Pullback a term value through a type value
 *  w : Δ -> Ξ, α : ⟦Γ⟧(Ξ), x : ⟦A⟧(Ξ, α) ⊢ x[w] : ⟦A⟧(Δ, α[w])       *)
let rec wk_vltm (w : wk) (u : vltm) : vltm =
  match u with
  | UD a ->  UD (wk_nf w a)
  | ElD s -> ElD(wk_nf w s)
  | PiD f -> PiD (fun w' u -> f (wk_o w' w) u)

(* Pullback a substitution value through a context value
 *  w : Δ -> Ξ, α : ⟦Γ⟧(Ξ) ⊢ α[w] : ⟦Γ⟧(Δ)                            *)
let wk_vlsub (w : wk) (env : vlsub) : vlsub =
  List.map (wk_vltm w) env


(****************************************************)
(* Evaluation/Reification/Reflection                *)
(****************************************************)

let appD (u : vltm) (v : vltm) : vltm =
  match u with
  | PiD f -> f W_id v
  | _ -> failwith "Not a lambda!"



(* α : ⟦Γ⟧(Δ) ⊢ ⟦t⟧(Δ,α) : ⟦A⟧(Δ,α) *)
let rec eval_tm (t : tm) (env : vlsub) : vltm =
  match t with
  | Var x    -> List.nth env x
  | Lam s    -> PiD (fun w u -> eval_tm s (u::(wk_vlsub w env)))
  | App(t,u) -> appD (eval_tm t env) (eval_tm u env)
(* MLTT *)
  | Empty    -> UD (NeuU Empty_)
  | Unit     -> UD (NeuU Unit_)
  | Bool     -> UD (NeuU Bool_)
  | True     -> ElD (NeuEl True_)
  | False    -> ElD (NeuEl False_)
  | Star     -> ElD (NeuEl Star_)
  | EmptyE   -> emptyED ()
  | BoolE    -> boolED env
  | IPi      -> ipiD ()
  | Iapp     -> iappD env
  | Ilam     -> ilamD ()
  | ISig     -> isigD ()
  | Pair     -> pairD ()
  | P1       -> pi1D env
  | P2       -> pi2D env


(* α : ⟦Γ⟧(Δ) ⊢ ⟦A⟧(Δ,α) : Set *)
and eval_ty (a : ty) (env : vlsub) : vlty =
  match a with
  | U         -> VU
  | El t      -> VEl (eval_tm t env)
  | Pi(a,fam) -> VPi(eval_ty a env, (fun w u -> eval_ty fam (u::(wk_vlsub w env))))

(* α : ⟦Γ⟧(Ξ) ⊢ ⟦γ⟧(Ξ,α) : ⟦Δ⟧(Ξ) *)
and eval_sub (gamma : sub) (env : vlsub) : vlsub =
  match gamma with
  | []         -> []
  | t :: gamma -> (let env = (eval_sub gamma env) in
                   (eval_tm t env) :: env)

(* ⟦Γ⟧ : Set *)
and eval_con (ctx : con) : vlcon =
  match ctx with
  | []     -> []
  | a::ctx -> (fun env -> eval_ty a env) :: (eval_con ctx)

(* Γ : Con, A : Ty Γ  ⊢  q A ⟦t⟧ : Nf(Γ,A) *)
and reify_tm (a : ty) (u : vltm) : nf =
  match (a,u) with
  | U,       UD a  -> a
  | El _,    ElD t -> t
  | Pi(a,b), PiD f -> (let v = (reflect_tm a (Var_ 0)) in
                       NLam (reify_tm b (f (W1 W_id) v)))
  | U, ElD _ -> failwith "!!!"
  | _ -> failwith "Unexpected call to reify_tm!"

(* Γ : Con  ⊢  q ⟦A⟧ : Ty Γ *)
and reify_ty (a : vlty) : ty =
  match a with
  | VU         -> U
  | VEl t      -> El (nf_tm (reify_tm U t))
  | VPi(av,bv) -> (let a = (reify_ty av) in
                   (let v = (reflect_tm a (Var_ 0)) in
                    Pi(a, (reify_ty (bv (W1 W_id) v)))))

(* Γ Δ : Con  ⊢  q Δ ⟦γ⟧ : Sub(Γ,Δ) *)
and reify_sub (ctx : con) (env : vlsub)  : sub =
  match ctx with
  | []       -> []
  | a :: ctx -> (nf_tm (reify_tm a (hd env))) :: (reify_sub ctx (tl env))

(*  ⊢  q ⟦Γ⟧ : Con *)
and reify_con (ctxv : vlcon) : con =
  match ctxv with
  | []         -> []
  | av :: ctxv -> (let ctx = (reify_con ctxv) in
                   (let env = (reflect_sub ctx (id (length ctxv))) in
                    (reify_ty (av env) :: ctx)))

(* Γ : Con, A : Ty Γ, t : Ne(Γ,A), α : ⟦Γ⟧(Δ)  ⊢  u A t : ⟦A⟧(Δ,α)  *)
and reflect_tm (a : ty) (t : ne) : vltm =
  match a with
  | Pi(a,b) -> PiD(fun w u -> reflect_tm b (App_(wk_ne w t, reify_tm a u)))
  | U       -> UD (NeuU t)
  | El _    -> ElD(NeuEl t)

(* Γ Δ : Con, γ : NeSub(Δ,Γ)  ⊢  u Γ γ : ⟦Γ⟧(Δ)  *)
and reflect_sub (ctx : con) (gamma : nesub) : vlsub =
  match ctx with
  | []       -> []
  | a :: ctx -> (reflect_tm a (hd gamma)) :: (reflect_sub ctx (tl gamma))

(* EmptyE : (a : U) -> El Empty -> El a *)
and emptyED () : vltm = (reflect_tm (Pi(U,Pi(El Empty,El (Var 1)))) EmptyE_)

(* BoolE : (a : U) -> El Bool -> El a -> El a -> El a *)
and boolED (env : vlsub) : vltm =
  PiD(fun w av ->
      PiD(fun w' bv ->
          (let av = (wk_vltm w' av) in
           (let env = (wk_vlsub (wk_o w' w) env) in
            (match bv with
             | ElD(NeuEl True_) -> (eval_tm (Lam (Lam (Var 1))) env)
             | ElD(NeuEl False_) -> (eval_tm (Lam (Lam (Var 0))) env)
             | _ -> (let a = reify_tm U av in
                     let b = reify_tm (El Bool) bv in
                     (reflect_tm (Pi(El(Var 1),Pi(El(Var 2),El(Var 3)))) (App_(App_(BoolE_, a), b)))))))))

and ipiD () : vltm = (reflect_tm (Pi(U, Pi(Pi(El(Var 0),U),U))) IPi_)
and ilamD () : vltm = (reflect_tm (Pi(U, Pi(Pi(El(Var 0),U), Pi(Pi(El(Var 1),El(App(Var 1,Var 0))), El(App(App(IPi,Var 2),Var 1)))))) Ilam_)
and iappD (env : vlsub) : vltm =
  PiD(fun w av ->
      PiD(fun w' bv ->
          PiD(fun w'' u ->
              PiD(fun w''' v ->
                  (let av = (wk_vltm (wk_o w''' (wk_o w'' w')) av) in
                   let bv = (wk_vltm (wk_o w''' w'') bv) in
                   let u = (wk_vltm w''' u) in
                   let env = (wk_vlsub (wk_o w''' (wk_o w'' (wk_o w' w))) env) in
                   (match u with
                    | ElD(NeuEl (App_(App_(App_(Ilam_,a),b), s))) -> (appD (eval_tm (nf_tm s) env) v)
                    | _ -> (let a = reify_tm U av in
                            let b = reify_tm (Pi(El(nf_tm a),U)) bv in
                            let t1 = reify_tm (El(App(App(IPi,nf_tm a), nf_tm b))) u in
                            let t2 = reify_tm (El(nf_tm a)) v in
                            (reflect_tm (El(App(nf_tm b,nf_tm t2))) (App_(App_(App_(App_(Iapp_, a), b), t1), t2))))))))))

and isigD () : vltm = (reflect_tm (Pi(U, Pi(Pi(El(Var 0),U),U))) ISig_)
and pairD () : vltm = (reflect_tm (Pi(U, Pi(Pi(El(Var 0),U), Pi(El(Var 1),Pi(El(App(Var 1,Var 0)),El(App(App(ISig,Var 3),Var 2))))))) Pair_)
and pi1D (env : vlsub) : vltm =
  PiD(fun w av ->
      PiD(fun w' bv ->
          PiD(fun w'' pv ->
              (let av = (wk_vltm (wk_o w'' w') av) in
               let bv = (wk_vltm w'' bv) in
               let env = (wk_vlsub (wk_o w'' (wk_o w' w)) env) in
               (match pv with
                | ElD(NeuEl (App_(App_(App_(App_(Pair_,a),b),x),y))) -> eval_tm (nf_tm x) env
                | _ -> (let a = reify_tm U av in
                        let b = reify_tm (Pi(El(nf_tm a),U)) bv in
                        let p = reify_tm (El(App(App(ISig,nf_tm a), nf_tm b))) pv in
                        (reflect_tm (El(nf_tm a)) (App_(App_(App_(P1_,a),b),p)))))))))

and pi2D (env : vlsub) : vltm =
  PiD(fun w av ->
      PiD(fun w' bv ->
          PiD(fun w'' pv ->
              (let av = (wk_vltm (wk_o w'' w') av) in
               let bv = (wk_vltm w'' bv) in
               let env = (wk_vlsub (wk_o w'' w') env) in
               (match pv with
                | ElD(NeuEl (App_(App_(App_(App_(Pair_,a),b),x),y))) -> eval_tm (nf_tm y) env
                | _ -> (let a = reify_tm U av in
                        let b = reify_tm (Pi(El(nf_tm a),U)) bv in
                        let p = reify_tm (El(App(App(ISig,nf_tm a),nf_tm b))) pv in
                        (reflect_tm (El(App(nf_tm b, (App(App(App(P1, nf_tm a),nf_tm b),nf_tm p))))) (App_(App_(App_(P2_,a),b), p)))))))))

let nbe_tm (ctx : con) (a : ty) (t : tm) : nf =
  reify_tm a (eval_tm t (reflect_sub ctx (id (length ctx))))

let nbe_ty (ctx : con) (a : ty) : ty =
  reify_ty (eval_ty a (reflect_sub ctx (id (length ctx))))

let nbe_con (ctx : con) : con =
  reify_con (eval_con ctx)

let nbe_sub (ctx : con) (gamma : sub) : sub =
  reify_sub ctx (eval_sub gamma (reflect_sub ctx (id (length ctx))))

(****************************************************************)
(* Tests                                                        *)
(****************************************************************)

let emptyE (a,x) = App(App(EmptyE,a),x)
let boolE (a,b,x,y) = App(App(App(App(BoolE,a),b),x),y)
let pi (a,b) = App(App(IPi,a),b)
let lam (a,b,s) = App(App(App(Ilam,a),b),s)
let app (a,b,t,u) = App(App(App(App(Iapp,a),b),t),u)
let sigma (a,b) = App(App(ISig,a),b)
let pair (a,b,x,y) = App(App(App(App(Pair,a),b),x),y)
let pi1 (a,b,p) = App(App(App(P1,a),b),p)
let pi2 (a,b,p) = App(App(App(P2,a),b),p)

let tm_ty_ctx
  = [([],El Unit,Star);
     ([],El Bool,True);
     ([],El Bool,False);
     ([El(Empty)],El Empty,Var 0);
     ([El(Empty)],El Empty,App(App(EmptyE,Empty),Var 0));
     ([],Pi(El Empty,El Empty), App(EmptyE,Empty));
     ([U], Pi(El Empty, El(Var 1)), App(EmptyE,Var 0));
     ([El(Empty);U], El(Var 1), App(App(EmptyE,Var 1),Var 0));
     ([El(Var 2);El(Var 1);El Bool;U], El(Var 3), App(App(App(App(BoolE,Var 3),Var 2),Var 1),Var 0));
     ([El(Var 1);El Bool;U], Pi(El(Var 2),El(Var 3)), App(App(App(BoolE,Var 2),Var 1),Var 0));
     ([El Bool;U], Pi(El(Var 1),Pi(El(Var 2),El(Var 3))), App(App(BoolE,Var 1),Var 0));
     ([U], Pi(El Bool,Pi(El(Var 1),Pi(El(Var 2),El(Var 3)))), App(BoolE,Var 0));
     ([], Pi(U,Pi(El Bool,Pi(El(Var 1),Pi(El(Var 2),El(Var 3))))), BoolE);
     ([El(Var 1);El(Var 0);U], El(Var 2), App(App(App(App(BoolE,Var 2),True),Var 1),Var 0));
     ([El(Var 1);El(Var 0);U], El(Var 2), App(App(App(App(BoolE,Var 2),False),Var 1),Var 0));
     ([El(App(App(IPi,Var 1),Var 0)); Pi(El(Var 0),U);U], El(App(App(IPi,Var 2),Var 1)), Var 0);
     ([U], El(App(App(IPi,Var 0),Lam (Var 1))), App(App(App(Ilam,Var 0),Lam (Var 1)), Lam (Var 0)));
     ([El(Var 2); El(App(App(IPi,Var 1),Var 0)); Pi(El(Var 0),U);U], El(App(Var 2,Var 0)), App(App(App(App(Iapp,Var 3),Var 2),Var 1),Var 0));
     (* x : A ⊢ ((λx. x) x) *)
     ([El(Var 0);U], El(pi(Var 1, Lam (Var 2))), app(Var 1, Lam (Var 2), lam(Var 1, Lam (Var 2), Lam (Var 0)), Var 0));
     (* (λx.(λy.x)) *)
     ([U], El(pi(Var 0, Lam(pi(Var 1, Lam (Var 2))))), lam(Var 0, Lam(pi(Var 1, Lam (Var 2))), Lam(lam(Var 1, Lam(Var 2), Lam(Var 1)))));
     (* (λx. x) (λx. x) *)
     ([U], El(pi(Var 0, Lam(Var 1))), app(pi(Var 0,Lam(Var 1)),Lam(pi(Var 1,Lam(Var 2))),
                                          lam(pi(Var 0, Lam(Var 1)), Lam(pi(Var 1, Lam (Var 2))), Lam(Var 0)),
                                          lam(Var 0,Lam(Var 1),Lam(Var 0))));
     (* (λx.(λy.x)) (λx.x) *)
     ([U], El(pi(Var 0, Lam(pi(Var 1, Lam(Var 2))))), app(pi(Var 0,Lam(Var 1)),
                                                          Lam(pi(Var 1,Lam(pi(Var 2,Lam(Var 3))))),
                                                          lam(pi(Var 0, Lam(Var 1)),
                                                              Lam(pi(Var 1, Lam(pi(Var 2,Lam(Var 3))))),
                                                              Lam(lam(Var 1, Lam(Var 2),Lam(Var 1)))),
                                                          lam(Var 0,Lam(Var 1),Lam(Var 0))));
     ([El(App(Var 1,Var 0));El(Var 1);Pi(El(Var 0),U);U], El(sigma(Var 3,Var 2)), pair(Var 3,Var 2,Var 1,Var 0));
     ([El(sigma(Var 1,Var 0));Pi(El(Var 0),U);U], El(Var 2), pi1(Var 2,Var 1,Var 0));
     ([El(sigma(Var 1,Var 0));Pi(El(Var 0),U);U], El(App(Var 1, pi1(Var 2,Var 1,Var 0))), pi2(Var 2,Var 1,Var 0));
     ([El(App(Var 1,Var 0));El(Var 1);Pi(El(Var 0),U);U], El(App(Var 2,Var 1)), pi2(Var 3,Var 2,pair(Var 3,Var 2,Var 1,Var 0)));
     ([El(App(Var 1,Var 0));El(Var 1);Pi(El(Var 0),U);U], El(App(Var 2,pi1(Var 3,Var 2,pair(Var 3,Var 2,Var 1,Var 0)))), pi2(Var 3,Var 2,pair(Var 3,Var 2,Var 1,Var 0)));
     ([El(App(Var 1,Var 0));El(Var 1);Pi(El(Var 0),U);U], El(Var 3), pi1(Var 3,Var 2,pair(Var 3,Var 2,Var 1,Var 0)));
    ]

let _ =
  for i=0 to (length tm_ty_ctx) - 1 do
    (let (ctx,a,t) = (nth tm_ty_ctx i) in
      (printf "(%d)@\n%a@\n" i pp_tm_ty_con (ctx,a,t));
      (printf "%a\n" pp_tm_ty_con
         (nbe_con ctx, nbe_ty ctx a, nf_tm (nbe_tm ctx a t))))
  done
