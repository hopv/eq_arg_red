(** Reduce arguments by conditional equalities *)

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

(*
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

  let rec elim n m (tasks:((int * int * int list * t) list)) acc =
    let b = true in
    let pp fm (x,y,vs,m) =
      Dbg.fprintf fm "%d, %d, %a, @[%a@." x y Print_.(list int) vs pp m
    in
    if b then Dbg.printf "tasks:@.";
    if b then List.iter (Dbg.printf "%a@." pp) tasks;
    if tasks = [] then
      acc
    else
      let tasks',acc' =
        List.L.fold_left
          tasks
          ~init:([],acc)
          ~f:(fun (tasks,acc) (i,rank,xs,mat) ->
            if i >= n || i >= m then
              tasks, mat::acc
            else
              let tasks' =
                match
                  List.fromto rank n
                  |> List.filter_map (fun j -> let x = mat.%(j,i) in if x <> 0 then Some (j,x) else None)
                with
                | [] -> ((i+1), rank, -1::xs, mat)::tasks
                | jxs ->
                    if b then Dbg.printf "jxs: %a@.@." Print_.(list (int * int)) jxs;
                    let lcm = Math.lcm_list @@ List.map (snd |- abs) jxs in
                    let mat' : t = List.fold_left (fun mat (j,x) -> mult j (lcm / x) mat) mat jxs in
                    let mats =
                      jxs
                      |> List.rev_map (fun (j,_) ->
                             jxs
                             |> List.fold_left (fun mat (k,x) -> if j = k || x = 0 then mat else sub k j mat) mat'
                             |> swap rank j
                             |> Pair.pair -$- (1 + mat.(j).x))
                    in
                    List.L.fold_left
                      mats
                      ~init:tasks
                      ~f:(fun tasks (mat,x) ->
                        let xs' = List.insert x xs in
                        if List.exists (Quadruple.trd |- (=) xs') tasks then
                          tasks
                        else
                          (i+1, rank+1, xs', mat)::tasks)
              in
              tasks', acc)
      in
      elim n m tasks' acc'

  let gaussian_elimination mat : t list =
    elim (Array.length mat) (Array.length mat.(0).row) [0, 0, [], mat] []

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
(      if i = n - 1 then
        Term.int c
      else
        let j = var_of_int' i in
        Term.(int c * var j))
|@>      Format.printf "monomial %d %d: %a@." i c Print.term

    in
    let t = Array.fold_lefti (fun e i c -> Term.(monomial i c + e)) Term.(int 0) e in
    Format.printf "[%s] i,x: %d, %d@."__FUNCTION__  i x;
    Format.printf "[%s] eq: %a@." __FUNCTION__ pp_eq e;
    var_of_int' x, Term.(int 0 = t) |@>     Format.printf "[%s] eq: %a@.@." __FUNCTION__ pp_term

end

type guard =
  | Guard of term
  | Otherwise
[@@deriving show { with_path = false }]

let rec subsets xs =
  match xs with
  | [] -> [[]]
  | x::xs' ->
      let ys = subsets xs' in
      ys @ List.map (List.cons x) ys

let all_simple_eqs tys samples : (var * term) list  =
  let open Matrix in
  let calc_eqs samples =
    if samples = [] then
      []
    else
      let () = Format.printf "[%s] samples:@.  %a@." __FUNCTION__ Print.(list (list int)) samples in
      samples
      |> from_samples
      |> gaussian_elimination
      |> List.rev_map_flatten (fun mat ->
             Matrix.deps_of mat
             |> List.map (term_of mat tys)
             |@> Format.printf "[%s] terms:@.  %a@.@." __FUNCTION__ Print.(list (var * term)))
      |> List.sort_unique compare
  in
  subsets samples
  |> List.rev_flatten_map calc_eqs

let satisfy (sample:int list) (eq:term) : bool =
  let env = List.mapi (fun i v -> var_of_int i, CInt v) sample in
  eval env eq = CBool true

exception Failed

let rec greedy acc (eqs:term list) samples k =
  if samples = [] then
    k acc
  else
    let check (eq:term) samples =
      let ts,fs = List.partition (satisfy -$- eq) samples in
(*
      Format.printf "[%s] eq: %a@." __FUNCTION__ Print.term eq;
      Format.printf "[%s] samples: %a@." __FUNCTION__ Print.(list (list int)) samples;
      Format.printf "[%s] ts: %a@." __FUNCTION__ Print.(list (list int)) ts;
      Format.printf "[%s] fs: %a@.@." __FUNCTION__ Print.(list (list int)) fs;
 *)
      eq, (List.length ts, ts, List.length fs, fs)
    in
    let cmp = Compare.on (fun (_,(_,_,n,_)) -> n) in
    match
      eqs
      |> List.rev_map (check -$- samples)
      |> List.sort cmp
    with
    | [] -> assert false
    | (_,(0,_,_,_))::_ -> raise Not_found
    | (e,(_,_,n,fs))::eqs' ->
        match
          if n = 0 then
            try
              Some (k (e::acc))
            with Failed -> None
          else
            None
        with
        | None -> greedy (e::acc) (List.map fst eqs') fs k
        | Some r -> r
let greedy = greedy []

let pick_candidates (r : (var * term) list) : (var * term) list =
  let rec pick acc_rev r =
    match r with
    | [] -> List.rev acc_rev
    | (x,ceq)::r' ->
        let acc_rev' =
          let fv = get_fv ceq in
          if List.Set.disjoint fv @@ List.map fst acc_rev then
            (x, ceq) :: acc_rev
          else
            acc_rev
        in
        pick acc_rev' r'
  in
  pick [] r


let get_coefficients n x ts fs =
  Format.printf "ts: %a@." Print.(list (list int)) ts;
  Format.printf "fs: %a@.@." Print.(list (list int)) fs;
  let env = List.init (n+1) (fun i -> var_of_int i, TInt) in
  let assert_ op vs =
    vs @ [1]
    |> List.mapi (fun j v -> let y = var_of_int j in if x = y then Term.int 0 else Term.(var y * int v))
    |> Term.add
    |> op Term.(int 0)
  in
  let tt = List.map (assert_ Term.(<=)) ts in
  let ff = List.map (assert_ Term.(>)) fs in
  SMT.Z3.solve env (tt@@@ff |@> Format.printf "tt@@@@@@ff: %a@." Print.(list term))
  |> Result.to_option
  |@> Format.printf "[%s] result: %a@." __FUNCTION__ Print.(option (list (string * const)))

let term_of_coefficients n sol =
  assert (List.length sol = n + 1);
  let t =
    sol
    |> List.sort compare
    |> List.map (function (_, CInt n) -> n | _ -> assert false)
    |> List.mapi (fun i m -> if i = n then Term.int m else let x = var_of_int i in Term.(int m * var x))
    |> Term.add
  in
  Term.(int 0 <= t)

let term_of_cond_eq (ceqs : (guard * term) list) : term =
  let otherwise =
    ceqs
    |> List.filter_map (fst |- function Guard t -> Some t | Otherwise -> None)
    |> Term.or_
    |> Term.not
  in
  Format.printf "otherwise: %a@." Print.term otherwise;
  let add_guard (g, eq) =
    let g' =
      match g with
      | Guard t -> t
      | Otherwise -> otherwise
    in
    Term.([g'] => eq)
  in
  ceqs
  |> List.map add_guard
  |> Term.and_

let find_guards (x:var) eqs samples : term =
  Dbg.printf "[%s] eqs: %a@." __FUNCTION__ Print.(list term) eqs;
  let n = List.length (List.hd samples) in
  let guard_of (eq:term) : term option =
    samples
    |> List.partition (satisfy -$- eq)
    |> Fun.uncurry @@ get_coefficients n x
    |> Option.map (term_of_coefficients n)
  in
  let last = List.length eqs - 1 in
  List.L.fold_lefti
    eqs
    ~init:[]
    ~f:(fun acc_rev i eq ->
      let guard =
        if i < last then
          match guard_of eq with
          | None ->
              Dbg.printf "[%s] Failed@." __FUNCTION__;
              raise Failed
          | Some g -> Guard g
        else
          Otherwise
      in
      Dbg.printf "guard: %a@." pp_guard guard;
      Dbg.printf "eq: %a@.@." pp_term eq;
      (guard, eq)::acc_rev)
  |> List.rev (* just for readability *)
  |> term_of_cond_eq

let assert_candidate (sample : int list list) (cand : (var * term) list) =
  let xs = List.sort compare @@ List.map fst cand in
  assert (xs = List.sort_uniq compare xs);
  let check eq vs =
    Format.printf "eq: %a@." Print.term eq;
    Format.printf "vs: %a@.@." Print.(list int) vs;
    let env = List.mapi (fun i v -> var_of_int i, CInt v) vs in
    assert (eval env eq = CBool true)
  in
  List.iter (fun (_,eq) -> List.iter (check eq) sample) cand

let synthesize_candidate (env:env) (samples : sample list) : (var * equality) list =
  samples
  |> List.map (fun (p, vs) ->
         let tys = CHC.arg_tys_of p env in
         let vars = List.mapi (fun i _ -> var_of_int i) tys in
         let eqs =
           all_simple_eqs tys vs
           |> List.sort_unique compare
           |> List.filter (fst |- List.mem -$- vars)
           |> List.classify ~eq:(Eq.on fst)
           |> List.map (fun eqs -> fst (List.hd eqs), List.rev_map snd eqs)
         in
         Dbg.printf "vars: %a@." Print.(list var) vars;
         Dbg.printf "simple_eqs: %a@." Print.(list (var * list term)) eqs;
         let cand : (var * term) list =
           if eqs = [] then
             List.map (fun x -> x, Term.ff) vars
           else
             vars
             |> List.filter_map (fun x ->
                    try
                      let eq = List.assoc x eqs in
                      let@ eqs = greedy eq vs in
                      List.iter (Dbg.printf "expr[%a]: %a@." pp_var x pp_term) eqs;
                      Some (x, find_guards x eqs vs)
                    with Failed -> None)
             |> pick_candidates
         in
         if Dbg.dbg then assert_candidate (List.assoc p samples) cand;
         p, (vars, cand))

 *)

module Original = struct
  module Smt = struct
    open Util

    module Debug = struct
      let dbg = debug_mode_of __MODULE__
      let printf f = if dbg then Format.printf f else Format.iprintf f
      let fprintf fm f = if dbg then Format.fprintf fm f else Format.ifprintf fm f
    end

    let solver = "z3"
    let filename = "_tmp.smt2"

    exception SolverError
    exception ParseError

    let assert_ op i cout xs =
      let pr fm (j,v) = if i <> j then Format.fprintf fm "(* %d c%d)" v (j+1) in
      let ivs = List.mapi Pair.pair @@ Array.to_list xs in
      Format.asprintf "(assert (%s 0 (+ c0 %a)))\n" op (print_list pr " ") ivs
      |> output_string cout
    let assert_leq i cout ts = assert_ "<=" i cout ts
    let assert_gt i cout fs = assert_ ">" i cout fs

    let decls n cout =
      for i = 0 to n do
        Printf.fprintf cout "(declare-const c%d Int)\n" i
      done

    let check_get cout =
      Printf.fprintf cout "(check-sat)\n";
      Printf.fprintf cout "(get-model)\n"

    let make_smt_file i ts fs =
      let cout = open_out filename in
      decls (Array.length @@ List.hd ts) cout;
      List.iter (assert_leq i cout) ts;
      List.iter (assert_gt i cout) fs;
      check_get cout;
      close_out cout


    let parse_error sexp =
      Format.printf "ParseError: %s" (Sexplib.Sexp.to_string sexp);
      raise ParseError

    let parse_int (sexp : Sexplib.Sexp.t) =
      try
        match sexp with
        | Atom v -> int_of_string v
        | List [Atom "-"; Atom v] -> - int_of_string v
        | _ -> invalid_arg ""
      with _ -> parse_error sexp

    let parse_define (sexp : Sexplib.Sexp.t) =
      match sexp with
      | List [Atom "define-fun"; Atom x; List []; Atom "Int"; v] when String.starts_with x "c" ->
          int_of_string (String.tl x), parse_int v
      | _ -> parse_error sexp

    let parse_model (sexp : Sexplib.Sexp.t) =
      match sexp with
      | List defs -> List.map parse_define defs
      | _ -> parse_error sexp

    let get_model cin =
      let open Sexplib in
      let model = Sexp.input_sexp cin in
      Debug.printf "model: %s@." (Sexp.to_string model);
      parse_model model
      |> List.sort compare

    let run () =
      Unix.CPS.open_process_in (solver ^ " " ^ filename) (fun cin ->
          match input_line cin with
          | "sat" -> Some (get_model cin)
          | "unsat" -> None
          | _ -> raise SolverError)

    let pp_leq fm cs =
      match cs with
      | [] -> invalid_arg "%s" __FUNCTION__
      | c::cs ->
          Format.fprintf fm "0 <= %d" c;
          List.iteri (fun i c ->
              if c <> 0 then
                (if c = 1 then
                   Format.fprintf fm " +"
                 else if c = -1 then
                   Format.fprintf fm " -"
                 else
                   Format.fprintf fm " + %d" c;
                 Format.fprintf fm " x%d" (i+1))) cs

    (* result [c0; c1; ...; cn] represents 0 <= c0 + c1 x1 + ... cn xn *)
    let get_coefficients i ts fs =
      make_smt_file i ts fs;
      match run() with
      | None -> None
      | Some model ->
          assert (List.for_alli (fun i (j,_) -> i = j) model);
          let cs = List.map snd model in
          let cs' = List.replace_nth cs (i+1) 0 in
          Debug.printf "guard: %a@." pp_leq cs';
          Some cs'
  end

  module Debug = struct
    let dbg = debug_mode_of __MODULE__
    let printf f = if dbg then Format.printf f else Format.iprintf f
    let fprintf fm f = if dbg then Format.fprintf fm f else Format.ifprintf fm f
  end

  type samples = int array list
  and row = int array
  and matrix = elm array
  and elm = {row:row; x:var; e:expr}
  and var = int
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
  let pp fm (mat:matrix) =
    let pr {row; x; e} =
      Format.fprintf fm "%a : %a, %a@\n" pp_row row pp_var x pp_expr e
    in
    Array.iter pr mat

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

  let mult i d (mat:matrix) : matrix =
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

  let sub i j (mat:matrix) : matrix =
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

  let delim = ','

  let input_row cin : row =
    input_line cin
    |> String.split_on_char delim
    |> List.map int_of_string
    |> Array.of_list

  let (.%()) mat (i,j) = mat.(i).row.(j)

  type int_pair_list = (int * int) list
  [@@deriving show]

  (*
  let rec elim i rank n m (mat:matrix) =
    if false then printf "mat[%d,%d,(%d*%d)]:@.%a@." i rank n m pp mat;
    if i >= n || i >= m then
      [mat]
    else
      match
        List.fromto rank n
        |> List.filter_map (fun j -> let x = mat.%(j,i) in if x <> 0 then Some (j,x) else None)
      with
      | [] -> elim (i+1) rank n m mat
      | jxs ->
          printf "jxs: %a@.@." pp_int_pair_list jxs;
          let lcm = Math.lcm_list @@ List.map (snd |- abs) jxs in
          let mat' : matrix = List.fold_left (fun mat (j,x) -> mult j (lcm / x) mat) mat jxs in
          jxs
          |> List.rev_map_flatten (fun (j,_) ->
                 List.fold_left (fun mat (k,x) -> if j = k || x = 0 then mat else sub k j mat) mat' jxs
                 |> swap rank j
                 |> elim (i+1) (rank+1) n m)
  let gaussian_elimination mat : matrix list =
    elim 0 0 (Array.length mat) (Array.length (Triple.fst mat.(0))) mat
   *)
  type intlist = int list
  [@@deriving show]

  let rec elim n m (tasks:((int * int * int list * matrix) list)) acc =
    let pp fm (x,y,vs,m) =
      Debug.fprintf fm "%d, %d, %a, @[%a@." x y pp_intlist vs pp m
    in
    Debug.printf "tasks:@.";
    List.iter (Debug.printf "%a@." pp) tasks;
    if tasks = [] then
      acc
    else
      let tasks',acc' =
        List.L.fold_left
          tasks
          ~init:([],acc)
          ~f:(fun (tasks,acc) (i,rank,xs,mat) ->
            if i >= n || i >= m then
              tasks, mat::acc
            else
              let tasks' =
                match
                  List.fromto rank n
                  |> List.filter_map (fun j -> let x = mat.%(j,i) in if x <> 0 then Some (j,x) else None)
                with
                | [] -> ((i+1), rank, -1::xs, mat)::tasks
                | jxs ->
                    Debug.printf "jxs: %a@.@." pp_int_pair_list jxs;
                    let lcm = Math.lcm_list @@ List.map (snd |- abs) jxs in
                    let mat' : matrix = List.fold_left (fun mat (j,x) -> mult j (lcm / x) mat) mat jxs in
                    let mats =
                      jxs
                      |> List.rev_map (fun (j,_) ->
                             jxs
                             |> List.fold_left (fun mat (k,x) -> if j = k || x = 0 then mat else sub k j mat) mat'
                             |> swap rank j
                             |> Pair.pair -$- (1 + mat.(j).x))
                    in
                    List.L.fold_left
                      mats
                      ~init:tasks
                      ~f:(fun tasks (mat,x) ->
                        let xs' = List.insert x xs in
                        if List.exists (Quadruple.trd |- (=) xs') tasks then
                          tasks
                        else
                          (i+1, rank+1, xs', mat)::tasks)
              in
              tasks', acc)
      in
      elim n m tasks' acc'

  let gaussian_elimination mat : matrix list =
    elim (Array.length mat) (Array.length mat.(0).row) [0, 0, [], mat] []

  let deps_of (mat:matrix) =
    mat
    |> Array.to_list
    |> List.filter_map (fun {row;x;_} -> if Array.for_all ((=) 0) row then Some x else None)
    |> List.sort compare

  let deps_of_with_index (mat:matrix) =
    mat
    |> Array.to_list
    |> List.filter_mapi (fun i {row;x;_} -> if Array.for_all ((=) 0) row then Some (i,x) else None)
    |> List.sort (Compare.on snd)

  let normalize_expr e =
    let d = Math.gcd_list @@ List.map abs @@ Array.to_list e in
    Array.map ((-$-) (/) d) e

  let string_of_int_list = String.join "," -| List.map string_of_int
  let string_of_int_array = String.join "," -| List.map string_of_int -| Array.to_list

  let output mat =
    let deps_with = deps_of_with_index mat in
    Printf.printf "%s\n" (string_of_int_list (List.map snd deps_with));
    List.iter (fun (i,_) -> Printf.printf "%s\n" (string_of_int_array (normalize_expr mat.(i).e))) deps_with

  let output_all mats =
    Printf.printf "%d\n" (List.length mats);
    List.iter output mats

  let make_matrix_from_samples samples =
    let n = Array.length samples in
    let m = Array.length samples.(0) in
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

  let input_samples cin =
    let n = int_of_string (input_line cin) in
    assert (n >= 1);
    Array.init n (fun _ -> input_row cin)

  let check_deps mat =
    let deps =
       mat
       |> deps_of_with_index
    in
    let check (i,_) =
      let e = mat.(i).e in
      let n = List.count (fun (_,x) -> e.(x) <> 0) deps in
      assert (n = 1) (* needs normalization *)
    in
    List.iter check deps
  type ilill = (int list * int list) list [@@deriving show]
  type ill = int list list [@@deriving show]

  let rec subsets xs =
    match xs with
    | [] -> [[]]
    | x::xs' ->
        let ys = subsets xs' in
        ys @ List.map (List.cons x) ys

  let all_simple_eqs samples =
    let samples = Array.to_list samples in
    let calc_eqs samples =
      if samples = [] then
        []
      else
        let samples = Array.of_list samples in
        let n = Array.length samples in
        samples
        |> make_matrix_from_samples
        |> gaussian_elimination
        |*> List.filter_out (List.mem (n+1) -| deps_of)
        |> List.rev_map_flatten (fun mat -> deps_of_with_index mat |> List.map (fun (i,x) -> x, mat.(i).e))
    in
    let f samples =
      if false then Format.printf "samples: @[%a@." pp_samples samples;
      calc_eqs samples
      |> List.sort_unique compare
      |*> List.iter (fun (x,e) -> Format.printf "%a: %a@." pp_var x pp_eq e)
    in
    subsets samples
    |> List.rev_flatten_map f

  let satisfy sample (eq:expr) =
    List.fold_left2 (fun acc v c -> acc + v*c) 0 (Array.to_list sample@[1]) (Array.to_list eq) = 0

  let rec greedy (eqs:expr list) samples acc =
    Debug.printf "|samples|: %d@." (List.length samples);
    Debug.printf "|eqs|: %d@." (List.length eqs);
    if samples = [] then
      acc
    else
      let check (eq:expr) samples =
        let ts,fs = List.partition (satisfy -$- eq) samples in
        if false then Format.printf "eq[%d]: %a@." (List.length ts) pp_eq eq;
        eq, (List.length ts, ts, List.length fs, fs)
      in
      let cmp = Compare.on (fun (_,(_,_,n,_)) -> n) in
      match
        eqs
        |> List.rev_map (check -$- samples)
        |> List.sort cmp
      with
      | [] -> assert false
      | (_,(0,_,_,_))::_ -> raise Not_found
      | (e,(_,_,0,_))::_ -> e::acc
      | (e,(_,_,_,fs))::eqs' -> greedy (List.map fst eqs') fs (e::acc)
  let greedy (eqs:expr list) (samples:int array array) = greedy eqs (Array.to_list samples) []

  type guard = GLeq of int list | Otherwise
  [@@deriving show { with_path = false }]

  let find_guards x eqs samples =
    let samples = Array.to_list samples in
    let guard_of eq =
      samples
      |> List.partition (satisfy -$- eq)
      |> Fun.uncurry @@ Smt.get_coefficients x
    in
    let last = List.length eqs - 1 in
    List.L.fold_lefti
      eqs
      ~init:[]
      ~f:(fun acc i eq ->
        let guard =
          if i < last then
            match guard_of eq with
            | None -> raise Not_found
            | Some g -> GLeq g
          else
            Otherwise
        in
        (guard, eq)::acc)
    |> List.rev

  let csv_of_int_list xs =
    xs
    |> List.map string_of_int
    |> String.join ","

  let csv_of_int_array a =
    Array.to_list a
    |> csv_of_int_list


  (***
  Format:
  [The number of candidates]
  [The index of a variable to be removed]
  [The number of the conjuncts (n)]
  [1st guard (precedent)]
  [1st equality (antecedent)]
  [2nd guard (precedent)]
  [2nd equality (antecedent)]
  ...
  [n-th equality (antecedent)]

  Memo:
  - [n-th guard (precedent)] is not present (The negation of the disjunctions of the other guards)
  - [precedent] is a sequence of coefficients
    For example, "1,2,3,4" represents 0 <= 1 + x0 + 2 x1 + 3 x2 + 4 x3
  - [antecend] is a sequence of coefficients
    For example, "1,2,3,4" represents 0 = x0 + 2 x1 + 3 x2 + 4
  - (0 <= x0 => 0 = -x0 + x1) /\ (_ => 0 = x1 + x0) can be represented by
    "2"
    "-1,1,0"
    "0,1,0"
    "1,1,0"
   ***)
  let output_result cout r =
    Printf.fprintf cout "%d\n" (List.length r);
    r
    |> List.iter (fun (x,ceqs) ->
           Printf.fprintf cout "%d\n" x;
           Printf.fprintf cout "%d\n" (List.length ceqs);
           ceqs
           |> List.iter (fun (g,e) ->
                  output_endline cout (csv_of_int_array e);
                  match g with
                  | GLeq cs ->
                      output_endline cout (csv_of_int_list cs);
                  | Otherwise -> ()))

  let fv_of_guard ?(acc=[]) guard =
    match guard with
    | GLeq cs -> List.fold_lefti (fun acc i c -> if i <> 0 && c <> 0 then (i-1)::acc else acc) acc cs
    | Otherwise -> [] (* WARNING! *)

  let fv_of_eq ?(acc=[]) eq =
    let last = Array.length eq - 1 in
    Array.fold_lefti (fun acc i c -> if i <> last && c <> 0 then i::acc else acc) acc eq

  let fv_of_ceqs ceqs =
    List.fold_left (fun acc (guard,eq) -> fv_of_eq eq ~acc:(fv_of_guard ~acc guard)) [] ceqs
    |> List.sort_unique compare

  let pp_ceqs fm ceqs =
    let pr fm (g,e) = Format.fprintf fm "@[(@[%a@] =>@ %a)@]" pp_guard g pp_eq e in
    Format.fprintf fm "@[%a@]" (print_list pr " /\\ ") ceqs

  let pick_candidates r =
    let rec pick acc_rev r =
      match r with
      | [] -> List.rev acc_rev
      | (x,ceqs)::r' ->
          let acc_rev' =
            let fv = fv_of_ceqs ceqs in
            if List.Set.disjoint fv @@ List.map fst acc_rev then
              let () = Debug.printf "picked[%a]: %a@." pp_var x pp_ceqs ceqs in
              (x,ceqs) :: acc_rev
            else
              acc_rev
          in
          pick acc_rev' r'
    in
    pick [] r


  let main samples =
    Debug.printf "samples: %a@." pp_samples @@ Array.to_list samples;
  (*
    let n = Array.length samples in
    let mat = make_matrix_from_samples samples in
    let mats =
      gaussian_elimination mat
      |> List.filter_out (List.mem (n+1) -| deps_of)
      |@> List.iter check_deps
      |@> List.iter (Debug.printf "mat:@.%a@." pp);
    in
    output_all mats
   *)
    let eqs =
      all_simple_eqs samples
      |> List.sort_unique compare
      |@> List.iter (fun (x,e) -> Debug.printf "%a: 0 =%a@." pp_var x pp_expr e)
      |> List.map (Pair.map_snd normalize_expr)
      |> List.classify ~eq:(Eq.on fst)
      |> List.map (fun eqs -> fst (List.hd eqs), List.map snd eqs)
    in
    let candidates =
      List.fromto 0 (Array.length samples.(0))
      |> List.map (fun x ->
             x,
             List.assoc x eqs
             |> greedy -$- samples
             |@> List.iter (Debug.printf "expr[%d]: 0 =%a@." (x+1) pp_expr))
    in
    candidates
    |> List.map (fun (x,eqs) -> x, try Some (find_guards x eqs samples) with Not_found -> None)
    |@> List.iter (fun (x,ceqs) -> Debug.printf "%a: %a@." pp_var x (Print_.option pp_ceqs) ceqs)
    |> List.filter_map (fun (x,ceqs) -> Option.map (Pair.pair x) ceqs)
    |> pick_candidates
end

let synthesize_candidate (env:env) (samples : sample list) : (var * equality) list =
  let term_of (eqs : (Original.guard * Original.expr) list) : term =
    let term_of_guard g =
      match g with
      | Original.GLeq vs ->
          vs
          |> List.mapi (fun i v -> if i = 0 then Term.int v else let x = var_of_int (i-1) in Term.(var x * int v))
          |> Term.add
          |> Term.((<=) (int 0))
          |> Option.some
      | Otherwise -> None
    in
    let term_of_expr vs =
      let n = Array.length vs in
      vs
      |> Array.to_list
      |> List.mapi (fun i v -> if i = n-1 then Term.int v else let x = var_of_int i in Term.(var x * int v))
      |> Term.add
      |> Term.((=) (int 0))
    in
    let eqs' = Fmap.(list (term_of_guard * term_of_expr)) eqs in
    let otherwise =
      List.filter_map fst eqs'
      |> Term.or_
      |> Term.not
    in
    eqs'
    |> List.map (fun (g,eq) -> let g' = Option.default otherwise g in Term.([g'] => eq))
    |> Term.and_
  in
  samples
  |> List.map (fun (p, vs) ->
         let sample = Array.of_list (List.map Array.of_list vs) in
         let tys = CHC.arg_tys_of p env in
         let vars = List.mapi (fun i _ -> var_of_int i) tys in
         let eqs =
           if vs = [] then
             List.map (fun x -> x, Term.ff) vars
           else
             (Fmap.(list (var_of_int * term_of)) @@ Original.main sample)
         in
         p, (vars, eqs))

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
      Dbg.printf "[%s] Found equality:@.  @[%a@.@." __FUNCTION__ Print.(list (var * pp_equality)) candidates;
      candidates
  | NonInvariant samples' ->
      find_equalities (samples' +++ samples) chc
  | exception Not_found -> []

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
