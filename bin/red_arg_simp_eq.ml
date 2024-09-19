(** Reduce arguments by simple equalities *)

open Util
open Syntax
open Term_util

module Dbg = struct
  let dbg = debug_mode_of __MODULE__
  let fprintf fm f = if dbg then Format.fprintf fm f else Format.ifprintf fm f
  let printf f = fprintf Format.std_formatter f
end

type sample = var * int list list
and equality = var list * (var * term) list

and check_result = Invariant | NonInvariant of counterexample
and counterexample = sample list
[@@deriving show]

let var_of_int i =
  new_var ~wrap:false ("x" ^ string_of_int i)

module Matrix = struct
  type row = int array
  and t = elm array
  and elm = {row:row; x:int; e:expr}
  and expr = int array
  [@@deriving show]

  let pp_var fm x =
    Format.fprintf fm "x%d" (x+1)
  let pp_expr fm e =
    if Array.for_all ((=) 0) e then
      Format.fprintf fm "0"
    else
      let n = Array.length e in
      Array.Labels.iteri e ~f:(fun i c ->
          if i = n-1 then
            match c with
            | 0 -> ()
            | 1 -> Format.fprintf fm " + 1"
            | -1 -> Format.fprintf fm " - 1"
            | _ when c < 0 -> Format.fprintf fm " - %d" (abs c)
            | _ -> Format.fprintf fm " + %d" c
          else
            match c with
            | 0 -> ()
            | 1 -> Format.fprintf fm " + %a" pp_var i
            | -1 -> Format.fprintf fm " - %a" pp_var i
            | _ when c < 0 -> Format.fprintf fm " - %d %a" (abs c) pp_var i
            | _ -> Format.fprintf fm " + %d %a" c pp_var i)
  let pp_eq fm e = Format.fprintf fm "0 =%a" pp_expr e
  let pp fm (mat:t) =
    let pr {row; x; e} =
      Format.fprintf fm "%a : %a, %a@\n" pp_row row pp_var x pp_expr e
    in
    Array.iter pr mat

  let from_samples samples =
    let n = List.length samples in
    let m = List.length (List.hd samples) in
    let samples =
      samples
      |> List.map (Array.of_list)
      |> Array.of_list
    in
    Array.init (m+1) (fun i ->
        let row =
          if i = m then
            Array.make n 1
          else
            Array.init n (fun j -> samples.(j).(i))
        in
        let x = i in
        let e = Array.init (m+1) (fun j -> if j = i then 1 else 0) in
        {row; x; e})

  let swap i j mat =
    if i = j then
      mat
    else
      Array.Labels.mapi mat ~f:(fun k r ->
          if k = i then
            mat.(j)
          else if k = j then
            mat.(i)
          else
            r)

  let mult i d (mat:t) : t =
    Array.Labels.mapi mat
      ~f:(fun k r ->
        if i <> k then
          r
        else
          let f x = x * d in
          let {row; x; e} = mat.(i) in
          let row' = Array.map f row in
          let e' = Array.map f e in
          {row=row'; x; e=e'})

  let sub_expr e1 e2 =
    Array.map2 (-) e1 e2

  let sub i j (mat:t) : t =
    let {row=rowj; e=ej; _} = mat.(j) in
    Array.Labels.mapi mat
      ~f:(fun k r ->
        if i <> k then
          r
        else
          let {row; x; e} = mat.(i) in
          let row' = Array.mapi (fun k x -> x - rowj.(k)) row in
          let e' = sub_expr e ej in
          {row=row'; x; e=e'})

  let deps_of (mat:t) : (int * int) list =
    mat
    |> Array.to_list
    |> List.filter_mapi (fun i {row;x;_} -> if Array.for_all ((=) 0) row then Some (i,x) else None)
    |> List.sort (Compare.on snd)

  let (.%()) mat (i,j) = mat.(i).row.(j)

  let rec elim n m (task:(int * int * t)) =
    let pp fm (x,y,m) =
      Dbg.fprintf fm "%d, %d, @[%a@." x y pp m
    in
    Dbg.printf "[%s] task:@.  %a@." __FUNCTION__ pp task;
    let (i,rank,mat) = task in
    if i >= n || i >= m then
      mat
    else
      let task' =
        match
          List.fromto rank n
          |> List.filter_map (fun j -> let x = mat.%(j,i) in if x <> 0 then Some (j,x) else None)
        with
        | [] -> ((i+1), rank, mat)
        | jxs ->
            let _,pivot = List.hd jxs in
            Dbg.printf "[%s] pivot: %d@." __FUNCTION__ pivot;
            let lcm = Math.lcm_list @@ List.map (snd |- abs) jxs in
            let mat' : t = List.fold_left (fun mat (j,x) -> mult j (lcm / x) mat) mat jxs in
            let mats =
              jxs
              |> List.rev_map (fun (j,_) ->
                     jxs
                     |> List.fold_left (fun mat (k,x) -> if j = k || x = 0 then mat else sub k j mat) mat'
                     |> swap rank j)
            in
            let mat = List.hd mats in
            (i+1, rank+1, mat)
      in
      elim n m task'

  let gaussian_elimination mat : t =
    elim (Array.length mat) (Array.length mat.(0).row) (0, 0, mat)

  let map_of_vars tys =
    List.L.fold_left tys
      ~init:(0,0,[])
      ~f:(fun (i,j,map) ty ->
        match ty with
        | TInt -> i+1, j+1, (j,i)::map
        | _ -> i+1, j, map)
    |> Triple.trd

  let term_of mat tys (i,x) =
    let e = mat.(i).e in
    let n = Array.length e in
    let map = map_of_vars tys in
    let var_of_int' i =
      List.assoc_default i i map
      |> var_of_int
    in
    let monomial i c =
      if i = n-1 then
        Term.int c
      else
        let j = var_of_int' i in
        Term.(int c * var j)
    in
    let t = Array.fold_lefti (fun e i c -> Term.(monomial i c + e)) Term.(int 0) e in
    var_of_int' x, Term.(int 0 = t)

end

let synthesize_candidate (env:env) (samples : sample list) : (var * equality) list =
  samples
  |> List.map (fun (p, vs) ->
         let tys = CHC.arg_tys_of p env in
         let vars = List.mapi (fun i _ -> var_of_int i) tys in
         let cand =
           if vs = [] then
             List.map (fun x -> x, Term.ff) vars
           else
             let open Matrix in
             let mat =
               vs
               |> from_samples
               |> gaussian_elimination
             in
             deps_of mat
             |> List.map (term_of mat tys)
         in
         p, (vars, cand))

(** [candidates] must have all the predicates in chc *)
let check_candidate
      (candidates : (var * equality) list)
      (chc : CHC.t)
    : check_result
  =
  let term_of_equality (xs,eqs) =
    xs, Term.and_ (List.map snd eqs)
  in
  let model = List.map (Pair.map_snd term_of_equality) candidates in
  match CHC.check_model_all model chc with
  | Ok () -> Invariant
  | Error cex ->
      let get_samples (cl,sol) =
        match cl.CHC.head with
        | App(p, ts) ->
            let tys = CHC.arg_tys_of p chc.genv in
            let vs = List.map (eval sol) ts in
            let samples =
              List.filter_map2 (fun v ty ->
                  match v, ty with
                  | CInt n, TInt -> Some n
                  | _ -> None) vs tys
            in
            p, samples
        | _ -> assert false
      in
      let samples =
        cex
        |> List.map get_samples
        |> List.classify ~eq:(Eq.on fst)
        |> List.map (fun pcex -> fst (List.hd pcex), List.map snd pcex)
      in
      NonInvariant samples

let (+++) samples1 samples2 =
  List.fold_left (fun s2 (p,vss) -> snd @@ List.assoc_map p ((-$-) (@@@) vss) s2) samples2 samples1

let rec find_equalities
          (samples : sample list)
          (chc : CHC.t)
        : (var * equality) list
  =
  Dbg.printf "[%s] samples:@.  @[%a@." __FUNCTION__ Print_.(list pp_sample) samples;
  let candidates = synthesize_candidate chc.genv samples in
  Dbg.printf "[%s] candidates:@.  @[%a@.@." __FUNCTION__ Print_.(list (pp_var * pp_equality)) candidates;
  match check_candidate candidates chc with
  | Invariant ->
      Dbg.printf "[%s] Found equality:@.  @[%a@.@." __FUNCTION__ Print_.(list (pp_var * pp_equality)) candidates;
      candidates
  | NonInvariant samples' ->
      find_equalities (samples' +++ samples) chc

let reduce
      (eqs : (var * equality) list)
      (chc : CHC.t)
    : CHC.t * (CHC.model -> CHC.model)
  =
  let map =
    let make_map (xs,eqs) =
      let deps = List.map (List.mem_assoc -$- eqs) xs in
      xs,                          (** all the arguments *)
      deps,                        (** if [List.ith deps i = true] then [List.nth xs i] will be removed *)
      Term.and_ (List.map snd eqs) (** equaltion to be conjuncted *)
    in
    Fmap.(list (snd make_map)) eqs
  in
   (** Replace "P(ts)" with "P(ts') /\ eq" if [conj = ture] and
       replace "P(ts)" with "P(ts')" if [conj = false] *)
  let replace_term conj =
    make_trans (fun _tr t ->
        match t with
        | App(f,ts) ->
            let xs,deps,t_eq = List.assoc f map in
            let ts' = List.filter_map2 (fun t dep -> if dep then None else Some t) ts deps in
            let t_eq' = subst_map (List.combine xs ts) t_eq in
            let t =
              if conj then
                Term.(f@ts' && t_eq')
              else
                Term.(f@ts')
            in
            Some t
        | _ -> None)
  in
  let replace_clause {CHC.env; body; head} =
    let body = List.map (replace_term true) body in
    let head = replace_term false head in
    {CHC.env; body; head}
  in
  let chc =
    let genv =
      let update env (p,(_,deps,_)) =
          env
          |> List.assoc_map p (fun ty ->
                 let tys,ty' = Val._TFun ty in
                 let tys' = List.filter_map2 (fun t dep -> if dep then None else Some t) tys deps in
                 TFun(tys',ty'))
          |> snd
      in
      List.fold_left update chc.genv map
    in
    let rules = List.map replace_clause chc.rules in
    {CHC.genv; rules}
  in
  let inv_model model =
    ignore model;
    unsupported "%s" __FUNCTION__
  in
  chc, inv_model

let run chc =
  Dbg.printf "[%s] chc.genv: %a@." __FUNCTION__ pp_env chc.CHC.genv;
  let samples =
    CHC.pvars_of chc
    |@> Dbg.printf "[%s] pvars: %a@." __FUNCTION__ Print_.(list pp_var)
    |> List.map (fun p -> p, [])
  in
  let equalities =
    chc
    |> CHC.definite_of
    |> find_equalities samples
  in
  if equalities = [] then
    chc, Fun.id
  else
    reduce equalities chc
