
open Abstract_syntax_tree

module Intervals  = struct
  include Value_domain

  type bwd = Int of Z.t | POSINF | NEGINF

  type t = Interval of bwd * bwd | BOT

  (* print *)
  let bound_to_string (t1 : bwd) =
    match t1 with Int v -> Z.to_string v | POSINF -> "+∞" | NEGINF -> "-∞"

  (* negation *)
  let bound_neg (a : bwd) : bwd =
    match a with 
    | NEGINF -> POSINF 
    | POSINF -> NEGINF 
    | Int i -> Int (Z.neg i)

  (* a+b *)
  let bound_add (a:bwd) (b:bwd) : bwd = match a,b with
    | NEGINF,POSINF | POSINF,NEGINF -> invalid_arg "bound_add" (* (+∞) + (−∞) *)
    | NEGINF,_ | _,NEGINF -> NEGINF
    | POSINF,_ | _,POSINF -> POSINF
    | Int i, Int j -> Int (Z.add i j)
    

  (* a * b *)
  let  bound_mult (a: bwd) (b: bwd) : bwd = match a,b with
    |Int c, POSINF | POSINF, Int c -> if (Z.equal c Z.zero)
      then Int Z.zero 
      else (if(Z.gt c Z.zero)
            then  POSINF
            else  NEGINF)
    |NEGINF, Int c | Int c, NEGINF -> if (Z.equal c Z.zero)
      then Int Z.zero 
      else (if (Z.gt c Z.zero) 
            then  NEGINF
            else  POSINF)
    |Int c1, Int c2 -> if (Z.equal c1 Z.zero)
      then Int Z.zero
      else (if (Z.equal c2 Z.zero)
            then Int Z.zero
            else Int (Z.mul c1 c2)
           )


    | NEGINF,POSINF | POSINF,NEGINF -> NEGINF

    | POSINF,POSINF  | NEGINF,NEGINF  -> POSINF

  (* a / b *)
  let bound_div (a: bwd) (b: bwd) : bwd = match a,b with 
    | POSINF,POSINF -> Int (Z.zero)
    | _,NEGINF | _,POSINF -> Int (Z.zero)
    | POSINF, Int c -> if (Z.gt c Z.zero)
      then POSINF
      else ( 
        if (Z.lt c Z.zero)
        then NEGINF
        else invalid_arg "div by 0"
      )
    | NEGINF, Int c ->  if (Z.gt c Z.zero)
      then NEGINF
      else ( 
        if (Z.lt c Z.zero)
        then POSINF
        else invalid_arg "div by 0"
      )

    | Int c1, Int c2 -> Int (Z.div c1 c2)



  (* compare a et b, retourne -1, 0 ou 1 *)
  let bound_cmp (a : bwd) (b : bwd) : int =
    match (a, b) with
    | NEGINF, NEGINF | POSINF, POSINF -> 0
    | NEGINF, _ | _, POSINF -> -1
    | POSINF, _ | _, NEGINF -> 1
    | Int i, Int j -> Z.compare i j

  (* minimum bound *)
  let bound_min (a : bwd) (b : bwd) : bwd =
    match bound_cmp a b with
    | -1 -> a
    | _ -> b


  (* maximum bound *)
  let bound_max (a : bwd) (b : bwd) : bwd =
    match bound_cmp a b with
    | -1 -> b
    | _ -> a 


  (* extension de f par f(⊥) = ⊥ *)
  let lift1 f x = match x with Interval (a, b) -> f a b | BOT -> BOT

  let lift2 f x y = match x,y with
    |BOT,_|_,BOT -> BOT
    |Interval(a1,b1),Interval(a2,b2) -> f a1 b1 a2 b2

  (* −x dans les intervalles *)
  let neg (x : t) : t = lift1 (fun a b -> Interval (bound_neg b, bound_neg a)) x

  let top = Interval (NEGINF, POSINF)

  let bottom = BOT

  (* [a1,b1] + [a2,b2] *)
  let add (a:t) (b:t) : t = lift2 (fun a1 b1 a2 b2 -> Interval(bound_add a1 a2, bound_add b1 b2)) a b 

  (* [a1,b1] - [a2,b2] *)
  let sub (a:t) (b:t) : t = lift2 (fun a1 b1 a2 b2 -> Interval(bound_add a1 (bound_neg b2), bound_add b1 (bound_neg a2))) a b 

  (* [a1,b1] * [a2,b2] *)
  let mult (a:t) (b:t) : t = lift2 (fun a1 b1 a2 b2 -> Interval(bound_min (bound_min (bound_mult a1 a2) (bound_mult a1 b2)) (bound_min  (bound_mult b1 a2) (bound_mult b1 b2) ) 
                                                          , bound_max (bound_max (bound_mult a1 a2) (bound_mult a1 b2))  (bound_max (bound_mult b1 a2) (bound_mult b1 b2)))) a b

  (* [a1,b1] / [a2,b2] *)
  let div  (a:t) (b:t) : t = lift2 (fun a1 b1 a2 b2 ->  match (bound_cmp (Int Z.one) a2) with
      | -1 | 0 -> Interval(bound_min (bound_div a1 a2) (bound_div a1 b2), bound_max (bound_div  b1 a2) (bound_div b1 b2) )
      | _ -> (match (bound_cmp b2 (Int (Z.neg Z.one))) with
          | -1 | 0 -> Interval(bound_min (bound_div b1 a2) (bound_div b1 b2), bound_max (bound_div  a1 a2) (bound_div a1 b2) )  
          | _ -> (match a2, b2 with
              | Int c1, Int c2 -> if((Z.equal Z.zero c1) && (Z.equal Z.zero c2))
                then BOT
                else Interval(bound_div a1 a2, bound_div b1 b2)
              | _ ->  Interval(bound_div a1 a2, bound_div b1 b2)
            )
        )
    ) a b

  (* constant: {c} *)
  let const c = Interval (Int c, Int c)

  (* interval: [a,b] *)
  let rand a b =
    match Z.leq a b with true -> Interval (Int a, Int b) | false -> BOT

  let join a b = match a,b with
    | BOT,c | c,BOT -> c
    | Interval(a1,b1),Interval(a2,b2) -> Interval(bound_min a1 a2, bound_max b1 b2)


  let meet a b =  match a,b with
    | BOT,_ | _,BOT -> BOT 
    | Interval(a1,b1), Interval(a2,b2) ->( match bound_cmp (bound_max a1 a2) (bound_min b1  b2) with
        | -1 | 0 -> Interval((bound_max a1 a2),(bound_min b1  b2)) 
        | _ -> BOT
      ) 

  (* x ⊆ y dans les intervalles *)
  let subset (x : t) (y : t) : bool =
    match (x, y) with
    | BOT, _ -> true
    | _, BOT -> false
    | Interval (a, b), Interval (c, d) -> bound_cmp a c >= 0 && bound_cmp b d <= 0

  let is_bottom a = (a=BOT)

  (* print abstract element *)
  let print fmt x =
    match x with
    | BOT -> Format.fprintf fmt "⊥"
    | Interval (t1, t2) ->
      Format.fprintf fmt "[%s;%s]" (bound_to_string t1) (bound_to_string t2)

  (*let print2  x =
    match x with
    | BOT ->  "⊥"
    | Interval (t1, t2) ->
      "["^(bound_to_string t1)^","^(bound_to_string t2)^"]"*)

  let unary a op =
    match op with AST_UNARY_PLUS -> a | AST_UNARY_MINUS -> neg a

  let binary a b op =
    match op with
    | AST_PLUS -> add a b
    | AST_MINUS -> sub a b
    | AST_MULTIPLY -> mult a b
    | AST_DIVIDE -> div a b

  let widen a b = match a,b with
    | x,BOT -> x
    | BOT,x -> x
    | Interval(a1,b1),Interval(a2,b2) -> (match bound_cmp a1 a2 with
        | -1 | 0 -> (match bound_cmp b1 b2 with
            | 1 | 0 -> Interval(a1,b1)
            | _ -> Interval(a1,POSINF)
          )
        | _ -> (match bound_cmp b1 b2 with
            | 1 | 0 -> Interval(NEGINF,b1)
            | _ -> Interval(NEGINF,POSINF)
          )
      )

  (* implémentation des opérations de comparaison *)

  (* égalités *)
  let eq a b = meet a b, meet a b 

  (* la  non-égalité *)
  let neq a b = 
    match a,b with
    | BOT,_ -> BOT,b
    | _,BOT -> a,BOT
    | Interval(a1,b1),Interval(a2,b2) -> ( match ((bound_cmp a1 a2),(bound_cmp b1 a2),(bound_cmp a1 b2) ,(bound_cmp b1 b2)) with
        | _,-1,_,_ -> a,b
        | _,_,1,_  -> a,b 
        | 0,_,_,0 ->  a,b
        | -1,0,_,_ -> Interval(a1,bound_add a2 (bound_neg (Int Z.one))), b
        | -1,1,_,_ -> Interval(a1,bound_add a2 (bound_neg (Int Z.one))), b
        | _,_,_,0 -> BOT,BOT
        | _,_,_,-1 -> BOT,BOT
        | _,_,_,_ -> Interval(bound_add b2 (Int Z.one),b1),b
      )


  let gt x y  = match x, y with
                |BOT, _     -> BOT, BOT
                |Interval(a,b), Interval(c,d) when (bound_cmp a c > 0) &&  (bound_cmp b d > 0) -> x,y
                |Interval(a, b), Interval(c, d)  -> if bound_cmp b c <= 0 then BOT, BOT
                              else if (bound_cmp a c == 1) &&  (bound_cmp b d  == 1) then  x,y 
                                               else   let bound_max  =  bound_max a (bound_add  c (Int Z.one))  in
                                                      let bound_min  =  bound_min (bound_add b (Int (Z.neg (Z.one))) ) d  in 
                                                       Interval (bound_max, b), Interval (c, bound_min)
                | _, _   -> x, y

  let geq x y  = match x, y with
                  |BOT, _                -> BOT, BOT
                  |Interval(a, b), Interval(c, d)  -> if bound_cmp b c < 0 then BOT, BOT
                                            else   let bound_max  = bound_max a c in
                                                   let bound_min  = bound_min b d  in 
                                                     Interval (bound_max, b), Interval (c, bound_min)
                  | _, _   -> x, y


  let compare a b op = 
    match op with
    | AST_EQUAL -> eq a b
    | AST_NOT_EQUAL -> neq a b
    | AST_GREATER_EQUAL -> geq a b
    | AST_GREATER -> gt a b
    | AST_LESS_EQUAL ->  
      let y', x' = geq b a in
      (x', y')
    | AST_LESS -> 
      let y', x' = gt b a in
      (x', y')

  (* a vérifier auprés du prof  *)
  let bwd_unary x op r = match op with
    | AST_UNARY_PLUS -> meet x r
    | AST_UNARY_MINUS -> meet x (neg r)

  (* a vérifier auprés du prof/ meme que les constantes  *)
  let bwd_binary x y op r =
    match op with
    | AST_PLUS ->
        (* r=x+y => x=r-y and y=r-x *)
        (meet x (sub r y), meet y (sub r x))
    | AST_MINUS ->
        (* r=x-y => x=y+r and y=x-r *)
        (meet x (add y r), meet y (sub x r))
    | AST_MULTIPLY ->
        (* r=x*y => (x=r/y or y=r=0) and (y=r/x or x=r=0)  *)
        let contains_zero o = subset (const Z.zero) o in
        ( (if contains_zero y && contains_zero r then x else meet x (div r y)),
          if contains_zero x && contains_zero r then y else meet y (div r x) )
    | AST_DIVIDE ->
        (* this is sound, but not precise *)
        meet x (mult y r), meet y (div x r)
end
