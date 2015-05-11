type id = int (* start at 1 *)

type cell =
  | Empty          (* empty vertex *)
  | Shape of id    (* normal shape *)
  | Start of id    (* start of path *)
  | End of id      (* end of path *)
  | Count of int   (* paths must pass through n times *)

type t = cell array array

(* vertex *)
type v = int * int

(* edge *)
type e = v * v

let iter_v f (t: t) =
  Array.iteri (fun i -> Array.iteri (fun j v -> f (i,j) v)) t

let offset (i,j) di dj =
  (i+di,j+dj)

let dimensions t =
  let i = Array.length t in
  if i = 0 then
    (0,0)
  else
    (i,Array.length t.(0))

let valid_v t (i,j) =
  let (di,dj) = dimensions t in
  0 <= i && i < di && 0 <= j && j < dj && t.(i).(j) <> Empty

let valid_e t (v1,v2) =
  valid_v t v1 && valid_v t v2

let valid t l : e list = List.filter (valid_e t) l


let departing t v : e list =
  valid t [
    v, offset v 1 1;
    v, offset v 1 0;
    v, offset v 1 (-1);
    v, offset v 0 (-1);
    v, offset v (-1) (-1);
    v, offset v (-1) 0;
    v, offset v (-1) 1;
    v, offset v 0 1;
  ]

let arriving t v : e list =
  valid t [
    offset v 1 1, v;
    offset v 1 0, v;
    offset v 1 (-1), v;
    offset v 0 (-1), v;
    offset v (-1) (-1), v;
    offset v (-1) 0, v;
    offset v (-1) 1, v;
    offset v 0 1, v;
  ]

let reverse_edge (v1,v2) = (v2,v1)

let reversed l =
  List.map reverse_edge l

let crossing t v : e list =
  valid t [
    v, offset v 1 1;
    offset v 1 1, v;
    offset v 1 0, offset v 0 1;
    offset v 0 1, offset v 1 0
  ]

let vertical t v : e list =
  valid t [
    v, offset v 1 0;
    offset v 1 0, v;
  ]

let horizontal t v : e list =
  valid t [
    v, offset v 0 1;
    offset v 0 1, v;
  ]

let iter_e f (t: t) =
  iter_v (fun v1 _ ->
      List.iter f (departing t v1)
    ) t

let fmt_v ff (i,j) =
  Format.fprintf ff "v%d_%d" i j

let fmt_e ff (v1,v2) =
  Format.fprintf ff "e%a_%a" fmt_v v1 fmt_v v2

let path ff e =
  Format.fprintf ff "(path %a)" fmt_e e

let index ff e =
  Format.fprintf ff "(index %a)" fmt_e e

let preamble ff () =
  Format.fprintf ff "(declare-datatypes (T1 T2) ((Pair (pair (path T1) (index T2)))))@."

let max_id (t:t) =
  Array.map (Array.map (function
      | Shape id
      | Start id
      | End id -> id
      | _ -> 0
    )) t |>
  Array.fold_left (Array.fold_left max) 0

let declare ff max t =
  iter_e (fun e ->
      Format.fprintf ff "(declare-const %a (Pair Int Int))@." fmt_e e;
      Format.fprintf ff "  (assert (and (<= 0 %a) (<= %a %d)))@." path e path e max;
      Format.fprintf ff "  (assert (ite (> %a 0) (>= %a 0) (= %a -10)))@." path e index e index e

    ) t

let max_one ff l =
  Format.fprintf ff "(assert (>= 1 (+ 0 0 %a)))@."
    (Format.pp_print_list
       ~pp_sep:Format.pp_print_space
       (fun ff e -> Format.fprintf ff "(ite (> %a 0) 1 0)" path e))
    l

let only_n ff n l =
  Format.fprintf ff "(assert (= %d (+ 0 0 %a)))@." n
    (Format.pp_print_list
       ~pp_sep:Format.pp_print_space
       (fun ff e -> Format.fprintf ff "(ite (> %a 0) 1 0)" path e))
    l

let exact_id ff l id =
  Format.fprintf ff "(assert (and true %a))@."
    (Format.pp_print_list
       ~pp_sep:Format.pp_print_space
       (fun ff e -> Format.fprintf ff "(or (= %a %d) (= %a 0))" path e id path e))
    l

let path_start ff l =
  Format.fprintf ff "(assert (and true %a))@."
    (Format.pp_print_list
       ~pp_sep:Format.pp_print_space
       (fun ff e -> Format.fprintf ff "(=> (> %a 0) (= %a 0))" path e index e))
    l
  
let rec iter_select f past future =
  match future with
  | [] -> ()
  | h::tl ->
    f h (List.rev_append past tl);
    iter_select f (h::past) tl

let iter_select f l = iter_select f [] l


let rec numbered ff i arr =
  if i = 0 then
    Format.fprintf ff "(and true %a %a)"
      (Format.pp_print_list
         ~pp_sep:Format.pp_print_space
         (fun ff e -> Format.fprintf ff "(= %a 0)" path e))
      arr
      (Format.pp_print_list
         ~pp_sep:Format.pp_print_space
         (fun ff e -> Format.fprintf ff "(= %a 0)" path e))
      (reversed arr)
  else begin
    Format.fprintf ff "(or ";
    iter_select (fun earr rarr ->
        iter_select (fun edep rdep ->
            Format.fprintf ff "(and true ";
            Format.fprintf ff "(= %a %a) " path earr path edep;
            Format.fprintf ff "(> %a 0) " path earr;
            Format.fprintf ff "(> %a 0) " path edep;
            Format.fprintf ff "(= (+ %a 1) %a) " index earr index edep;
            numbered ff (i-1) (reversed rdep);
            Format.fprintf ff ")"
          ) (reversed rarr)
      ) arr;
    Format.fprintf ff ")"
  end

let numbered ff i arr =
  Format.fprintf ff "(assert ";
  numbered ff i arr;
  Format.fprintf ff ")@."

let constrain_edges ff t =
  iter_v (fun v _ ->
      Format.fprintf ff "; Edges from %a@." fmt_v v;
      max_one ff (crossing t v);
      max_one ff (horizontal t v);
      max_one ff (vertical t v)
    ) t

let constrain_vertexes ff t =
  iter_v (fun v vt ->
      Format.fprintf ff "; Vertex %a@." fmt_v v;
      match vt with
      | Empty -> ()
      | Shape id ->
        Format.fprintf ff ";   shape %d@." id;
        exact_id ff (arriving t v) id;
        exact_id ff (departing t v) id;
        (*only_n ff 1 (arriving t v);*)
        (*only_n ff 1 (departing t v);*)

        numbered ff 1 (arriving t v);
        ()
      | Start id ->
        Format.fprintf ff ";   start %d@." id;
        only_n ff 1 (departing t v);
        only_n ff 0 (arriving t v);
        exact_id ff (departing t v) id;
        path_start ff (departing t v);
        ()
      | End id ->
        Format.fprintf ff ";   end %d@." id;
        only_n ff 1 (arriving t v);
        only_n ff 0 (departing t v);
        exact_id ff (arriving t v) id;
        ()
      | Count c ->
        Format.fprintf ff ";   count %d@." c;
        (*only_n ff c (arriving t v);*)
        (*only_n ff c (departing t v);*)
        numbered ff c (arriving t v);
        ()
    ) t

let get_edges ff t =
  iter_e (fun e ->
      Format.fprintf ff "(get-value (%a))@." fmt_e e
    ) t

let emit ff (t:t) =
  let max = max_id t in
  preamble ff ();
  declare ff max t;
  constrain_edges ff t;
  constrain_vertexes ff t;
  Format.fprintf ff "(check-sat)@.";
  get_edges ff t;
  ()

 
let rec read_lines (ch: in_channel) : string list =
  try
    let l = input_line ch in
    let rest = read_lines ch in
    l::rest
  with End_of_file ->
    []

let get_results () =
  let fin = open_in "result.smt2" in
  let l = read_lines fin in
  close_in fin;
  let not_inc = Str.regexp "pair 0" in
  let line = Str.regexp "((ev\\([0-9]+\\)_\\([0-9]+\\)_v\\([0-9]+\\)_\\([0-9]+\\) (pair \\([0-9]+\\) \\([0-9]+\\))))" in
  let l = List.filter (fun s ->
      try
        ignore(Str.search_forward not_inc s 0);
        false
      with Not_found ->
      Str.string_match line s 0
    ) l in
  let l = List.map (fun s ->
      if not(Str.string_match line s 0) then 
        failwith "Could not parse result";
      let i1 = int_of_string (Str.matched_group 1 s) in
      let j1 = int_of_string (Str.matched_group 2 s) in
      let i2 = int_of_string (Str.matched_group 3 s) in
      let j2 = int_of_string (Str.matched_group 4 s) in
      let v = int_of_string (Str.matched_group 5 s) in
      let i = int_of_string (Str.matched_group 6 s) in
      (((i1,j1),(i2,j2)), v, i)
    ) l in
  List.sort (fun (e1, v1, i1) (e2, v2, i2) ->
      let res = compare v1 v2 in
      if res <> 0 then res
      else compare i1 i2
    ) l

let parse (ch: in_channel) : t =
  let l = read_lines ch in
  let rows = List.length l in
  if rows = 0 then begin
    Format.printf "Empty input (no rows)@.";
    exit 0
  end;
  let cols = List.fold_left (fun cols l -> max cols (String.length l)) 0 l in
  if cols = 0 then begin
    Format.printf "Empty input (no columns)@.";
    exit 0
  end;
  let a = Array.make_matrix rows cols Empty in
  let capcount = Hashtbl.create 29 in
  let get_letter l =
    let count = try Hashtbl.find capcount l with Not_found -> 0 in
    Hashtbl.replace capcount l (count + 1);
    if count = 0 then
      Start l
    else if count = 1 then
      End l
    else
      failwith "imbalanced number of capital letters"
  in
  List.iteri (fun i s ->
      for j = 0 to (String.length s) - 1 do
        let caps = s.[j] <> (Char.lowercase s.[j]) in
        let c = Char.code (Char.lowercase s.[j]) in
        let v = if Char.code '1' <= c && c <= Char.code '9' then
            Count (c - Char.code '0')
          else if Char.code 'a' <= c && c <= Char.code 'z' then
            if caps then
              get_letter c
            else
              Shape c
          else if Char.code ' ' = c then
            Empty
          else
            failwith "unsupported input character"
        in
        a.(i).(j) <- v
      done
    ) l;
  a

let print_t t =
  Array.iter (fun a ->
      Array.iter (function
          | Empty -> Format.printf " "
          | Shape c -> Format.printf "%c" (Char.chr c)
          | Start c -> Format.printf "%c" (Char.uppercase (Char.chr c))
          | End c -> Format.printf "%c" (Char.uppercase (Char.chr c))
          | Count c -> Format.printf "%d" c
        ) a;
      Format.printf "@."
    ) t

let line m ((i1,j1),(i2,j2)) c =
  let i1 = i1 * 4 in
  let j1 = j1 * 4 in
  let i2 = i2 * 4 in
  let j2 = j2 * 4 in
  let di = i2 - i1 in
  let dj = j2 - j1 in
  if i1 = i2 then begin
    (* horizontal line *)
    let (j1,j2) = if j1 > j2 then (j2,j1) else (j1,j2) in
    for j = j1+1 to j2-1 do
      m.(i1).(j) <- '-'
    done;
    m.(i1).(j1+(abs dj)/2) <- c
  end else if j1 = j2 then begin
    (* vertical line *)
    let (i1,i2) = if i1 > i2 then (i2,i1) else (i1,i2) in
    for i = i1+1 to i2-1 do
      m.(i).(j1) <- '|'
    done;
    m.(i1+(abs di)/2).(j1) <- c
  end else if di = dj then begin
    (* down right diagonal *)
    let (i1,j1) = if i1 > i2 then (i2,j2) else (i1,j1) in
    for i = 1 to (abs di)-1 do
      m.(i1+i).(j1+i) <- '\\'
    done;
    m.(i1+(abs di)/2).(j1+(abs di)/2) <- c
  end else if di = (-dj) then begin
    (* down left diagonal *)
    let (i1,j1) = if i1 > i2 then (i2,j2) else (i1,j1) in
    for i = 1 to (abs di)-1 do
      m.(i1+i).(j1-i) <- '/'
    done;
    m.(i1+(abs di)/2).(j1-(abs di)/2) <- c
  end else
    failwith "unsupported line"


let print_grid t res =
  let rows = Array.length t in
  let cols = Array.length t.(0) in
  let m = Array.make_matrix (rows*4-3) (cols*4-3) ' ' in
  Array.iteri (fun i a ->
      Array.iteri (fun j v ->
          let c = match v with
            | Empty -> ' '
            | Shape c -> Char.chr c
            | Start c -> Char.uppercase (Char.chr c)
            | End c -> Char.uppercase (Char.chr c)
            | Count c -> Char.chr (c + Char.code '0')
          in
          m.(4*i).(4*j) <- c
        ) a
    ) t;
  List.iter (fun (e,v,i) -> line m e (Char.chr v)) res;

  Array.iter (fun a ->
      Array.iter (Format.printf "%c") a;
      Format.printf "@."
    ) m
  
          

let solve t =
  print_t t;
  Format.printf "======================@.";
  let fout = open_out "problem.smt2" in
  let ff = Format.formatter_of_out_channel fout in
  emit ff t;
  close_out fout;
  ignore(Unix.system "z3 problem.smt2 > result.smt2");
  let res = get_results () in
  print_grid t res;
  Format.printf "======================@.";
  List.iter (fun (((i1,j1),(i2,j2)), v, i) ->
      Format.printf "%d,%d -> %d,%d : %c %d@." i1 j1 i2 j2 (Char.chr v) i
    ) res

let solve_in () =
  let t = parse stdin in
  solve t


let test1 : t = [|
  [| Shape 2; Shape 2; Start 1 |];
  [| Shape 2; Count 3; Count 2 |];
  [| Count 2; Start 2; Count 2 |];
  [| End   2; Shape 1; End   1 |];
|]

let test2 : t = [| [| Start 1; Shape 1; End 1 |] |]

let test3 : t = [| [| Start 1; Count 1; End 1 |] |]

let test4 : t = [|
  [| Start 1; Count 2; End 1 |];
  [| Start 2; Empty  ; End 2 |];
|]

let _ =
  (*solve test1*)
  solve_in ()
