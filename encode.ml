type t = char array array (* matrix of descriptive characters *)

type v = int * int (* (vert, horiz) must both be even numbers *)

type e = v * v (* must be lexicographically sorted *)

(* validators and string converters *)

let vertex_valid (a:t) ((i,j) : v) =
  let il = Array.length a in
  let jl = Array.length (a.(0)) in
  0 <= i && i < il && 0 <= j && j < jl && i mod 2 = 0 && j mod 2 = 0

let string_of_vertex (i,j) =
  "v"^(string_of_int i)^"_"^(string_of_int j)

let edge_correct (e:e) : e =
  let v1,v2 = e in
  let i1,j1 = v1 in
  let i2,j2 = v2 in
  if i1 < i2 then
    (v1,v2)
  else if i1 = i2 && j1 < j2 then
    (v1,v2)
  else
    (v2,v1)

let edge_valid (a:t) (e:e) =
  let (v1,v2) = edge_correct e in
  if v1 <> v2 && vertex_valid a v1 && vertex_valid a v2 then
    Some (v1,v2)
  else
    None

let string_of_edge ?decl:(decl=false) ?path:(path=false) (v1,v2) =
  if decl then
    "e"^(string_of_vertex v1)^"_"^(string_of_vertex v2)
  else if path then
    "(second e"^(string_of_vertex v1)^"_"^(string_of_vertex v2)^")"
  else
    "(first e"^(string_of_vertex v1)^"_"^(string_of_vertex v2)^")"

type vt =
  | PassThrough of int
  | Terminal of int
  | Numbered of int
  | Empty

let classify_vertex map i =
  let ic = Char.code i in
  if ic >= Char.code 'a' && ic <= Char.code 'z' then
    PassThrough (Hashtbl.find map i)
  else if ic >= Char.code 'A' && ic <= Char.code 'Z' then
    Terminal (Hashtbl.find map (Char.lowercase i))
  else if ic >= Char.code '0' && ic <= Char.code '9' then
    Numbered (ic - Char.code '0')
  else if i = ' ' then
    Empty
  else
    failwith ("unsupported input: " ^ (String.make 1 i))


(* helper routines *)

let rec list_map_filter (f: 'a -> 'b option) : 'a list -> 'b list = function
  | [] -> []
  | h::tl ->
    match f h with
    | None -> list_map_filter f tl
    | Some h -> h::(list_map_filter f tl)

let rec list_of_string l i s sl =
  if i < sl then
    list_of_string ((s.[i])::l) (i+1) s sl
  else
    List.rev l

let list_of_string (s: string) : char list =
  list_of_string [] 0 s (String.length s)

let rec fold_pairs f l r =
  match l with
  | [] -> r
  | e1::rest ->
    let r = List.fold_left (fun r e2 -> f e1 e2 r) r rest in
    fold_pairs f rest r

let map_pairs f l =
  fold_pairs (fun i j r -> (f i j)::r) l []

let rec remove e = function
  | [] -> []
  | h::rest when h = e -> rest
  | h::rest -> h::(remove e rest)

let rec read_lines (ch: in_channel) : string list =
  try
    let l = input_line ch in
    let rest = read_lines ch in
    l::rest
  with End_of_file ->
    []

(* iterators *)

let iter f a =
  Array.iteri (fun i -> Array.iteri (fun j v -> f i j v)) a

let iter_v f a = iter (fun i j v ->
    if i mod 2 == 0 && j mod 2 == 0 then
      f (i,j) v
    else ()
  ) a

let iter_nv f a = iter (fun i j v ->
    if i mod 2 == 0 && j mod 2 == 0 then
      ()
    else f i j v
  ) a

(* accessors *)

type et =
  | Horiz of e
  | Vert of e
  | Diag of e * e (* down-right, down-left *)

let edges a i j =
  if i mod 2 == 0 then (* horizontal line *)
    Horiz (edge_correct ((i,j-1),(i,j+1)))
  else if j mod 2 == 0 then (* vertical line *)
    Vert (edge_correct ((i-1,j),(i+1,j)))
  else (* diagonals *)
    Diag (edge_correct ((i-1,j-1),(i+1,j+1)), edge_correct ((i-1,j+1),(i+1,j-1)))

let adjacent_edges a ((i,j) as v) =
  let l = [
    (i-2,j+2),v;
    (i-2,j),v;
    (i-2,j-2),v;
    (i,j-2),v;

    (i+2,j-2),v;
    (i+2,j),v;
    (i+2,j+2),v;
    (i,j+2),v
  ] in
  list_map_filter (edge_valid a) l

let mem_vertex a (i,j) =
  a.(i).(j) <> ' '


(* parse input *)

let parse1 (ch: in_channel) : t =
  let l = read_lines ch in
  let a = Array.of_list l in
  let a = Array.map (fun s -> s |> list_of_string |> Array.of_list) a in
  a

let parse2 (ch: in_channel) : t =
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
  let a = Array.make_matrix (rows*2-1) (cols*2-1) ' ' in
  List.iteri (fun i s ->
      for j = 0 to (String.length s) - 1 do
        a.(i*2).(j*2) <- s.[j]
      done
    ) l;
  iter_nv (fun i j _ ->
      match edges a i j with
      | Vert (v1,v2) ->
        if mem_vertex a v1 && mem_vertex a v2 then
          a.(i).(j) <- '|'
      | Horiz (v1,v2) ->
        if mem_vertex a v1 && mem_vertex a v2 then
          a.(i).(j) <- '-'
      | Diag ((v1,v2),(v3,v4)) ->
        if mem_vertex a v1 && mem_vertex a v2 && mem_vertex a v3 && mem_vertex a v4 then
          a.(i).(j) <- 'X'
        else if mem_vertex a v1 && mem_vertex a v2 then
          a.(i).(j) <- '\\'
        else if mem_vertex a v3 && mem_vertex a v4 then
          a.(i).(j) <- '/'
    ) a;
  (*Array.iter (fun v ->
      Array.iter (fun v ->
          Format.printf "%c" v
        ) v;
      Format.printf "@."
    ) a;*)
  a

(* generate mapping from vertex types to integers *)
let find_map a =
  let h = Hashtbl.create 29 in
  let c = ref 0 in
  let aid = Char.code 'a' in
  let zid = Char.code 'z' in
  iter_v (fun _ v ->
      let v = Char.lowercase v in
      let vid = Char.code v in
      if vid < aid || vid > zid then
        ()
      else if Hashtbl.mem h v then
        ()
      else begin
        incr c;
        Hashtbl.replace h v !c
      end
    ) a;
  (h, !c)

let print_map ff map =
  Hashtbl.iter (fun c id ->
      Format.fprintf ff ";  %c -> %d@." c id
    ) map

(* generate variable declarations *)
let declare_vars ff max a =
  Format.fprintf ff "(declare-datatypes (T1 T2) ((Pair (pair (first T1) (second T2)))))@.";
  iter_nv (fun i j v ->
      let print_decl e =
          Format.fprintf ff "(declare-const %s (Pair Int Int))@." (string_of_edge ~decl:true e);
          Format.fprintf ff " (assert (>= %s 0))@." (string_of_edge e);
          Format.fprintf ff " (assert (<= %s %d))@." (string_of_edge e) max;
      in
      match edges a i j with
      | Horiz e -> print_decl e
      | Vert e -> print_decl e
      | Diag (e1,e2) -> print_decl e1; print_decl e2
    ) a

let get_vars ff a =
  iter_nv (fun i j v ->
      let print_get e =
          Format.fprintf ff "(get-value (%s))@." (string_of_edge e)
      in
      match edges a i j with
      | Horiz e -> print_get e
      | Vert e -> print_get e
      | Diag (e1,e2) -> print_get e1; print_get e2
    ) a

let edge_constraints ff a =
  Format.fprintf ff ";  Edge constraints@.";
  iter_nv (fun i j v ->
      match v, (edges a i j) with
      | 'X',  Diag (e1,e2)
      | 'x',  Diag (e1,e2) ->
        Format.fprintf ff "(assert (or (= %s 0) (= %s 0)))@."
          (string_of_edge e1)
          (string_of_edge e2)
      | '\\', Diag (_e1,e2) ->
        Format.fprintf ff "(assert (= %s 0))@."
          (string_of_edge e2)
      | '/',  Diag (e1,_e2) ->
        Format.fprintf ff "(assert (= %s 0))@."
          (string_of_edge e1)
      | '-',  Horiz e1 -> ()
      | '|',  Vert e1 -> ()
      | ' ',  Diag (e1,e2) ->
        Format.fprintf ff "(assert (= %s 0))@."
          (string_of_edge e1);
        Format.fprintf ff "(assert (= %s 0))@."
          (string_of_edge e2)
      | ' ',  Vert e1
      | ' ',  Horiz e1 ->
        Format.fprintf ff "(assert (= %s 0))@."
          (string_of_edge e1)
      | _ -> failwith "invalid input"
    ) a

let rec numbered i e =
  if i = 0 then
    "(and "^(
      e |>
      List.map (fun e -> Format.sprintf "(= %s 0)" (string_of_edge e)) |>
      String.concat " "
    )^")"
  else
    "(or "^(
      e |>
      map_pairs (fun e1 e2 ->
          Format.sprintf "(and (= %s %s) (> %s 0) (> %s 0) %s)"
            (string_of_edge e1)
            (string_of_edge e2)
            (string_of_edge e1)
            (string_of_edge e2)
            (numbered (i-1) (remove e1 (remove e2 e)))
        ) |>
      String.concat " "
    )^")"
    

let vertex_constraints ff map a =
  Format.fprintf ff ";  Vertex constraints@.";
  iter_v (fun v i ->
      match classify_vertex map i with
      | PassThrough id ->
        Format.fprintf ff "; PassThrough@.";
        List.iter (fun e ->
            Format.fprintf ff "(assert (or (= %s 0) (= %s %d)))@."
              (string_of_edge e) (string_of_edge e) id
          ) (adjacent_edges a v);
        Format.fprintf ff "(assert (= (+";
        List.iter (fun e ->
            Format.fprintf ff " %s" (string_of_edge e)
          ) (adjacent_edges a v);
        Format.fprintf ff ") %d))@." (2*id)
      | Terminal id ->
        Format.fprintf ff "; Terminal@.";
        List.iter (fun e ->
            Format.fprintf ff "(assert (or (= %s 0) (= %s %d)))@."
              (string_of_edge e) (string_of_edge e) id
          ) (adjacent_edges a v);
        Format.fprintf ff "(assert (= (+";
        List.iter (fun e ->
            Format.fprintf ff " %s" (string_of_edge e)
          ) (adjacent_edges a v);
        Format.fprintf ff ") %d))@." id
      | Numbered count ->
        Format.fprintf ff "; Numbered@.";
        Format.fprintf ff "(assert %s)@."
          (numbered count (adjacent_edges a v))
      | Empty ->
        Format.fprintf ff "; Empty@.";
        List.iter (fun e ->
            Format.fprintf ff "(assert (= %s 0))@." (string_of_edge e)
          ) (adjacent_edges a v)
    ) a

(* parse results *)

let parse_results () =
  let fin = open_in "result.smt2" in
  let l = read_lines fin in
  close_in fin;
  let r = Str.regexp "(((first ev\\([0-9]+\\)_\\([0-9]+\\)_v\\([0-9]+\\)_\\([0-9]+\\)) \\([0-9]+\\)))" in
  list_map_filter (fun s ->
      if Str.string_match r s 0 then begin
        let i1 = int_of_string (Str.matched_group 1 s) in
        let j1 = int_of_string (Str.matched_group 2 s) in
        let i2 = int_of_string (Str.matched_group 3 s) in
        let j2 = int_of_string (Str.matched_group 4 s) in
        let v = int_of_string (Str.matched_group 5 s) in
        Some (((i1,j1),(i2,j2)), v)
      end else
        None
    ) l

let get_results map =
  let r = parse_results () in
  let rmap = Hashtbl.create 29 in
  Hashtbl.iter (fun k v ->
      Hashtbl.replace rmap v k
    ) map;
  let res = Hashtbl.create 29 in
  List.iter (fun (v,vi) ->
      if vi <> 0 then
        Hashtbl.replace res v (Hashtbl.find rmap vi)
    ) r;
  res

let print_results r =
  Hashtbl.iter (fun ((i1,j1),(i2,j2)) v ->
      Format.printf "%d,%d -> %d,%d : %c@." i1 j1 i2 j2 v
    ) r

type dir =
  | Hor
  | Ver
  | DownRight
  | DownLeft

let generate_result_matrix a res =
  let m = Array.make_matrix ((Array.length a)*2) ((Array.length a.(0))*2) ' ' in
  iter_v (fun (i,j) v ->
      m.(i*2).(j*2) <- a.(i).(j)
    ) a;
  iter_nv (fun i j _ ->
      let update_result e d =
        try
          let v = Hashtbl.find res e in
          m.(i*2).(j*2) <- v;
          match d with
          | Hor ->
            m.(i*2).(j*2-1) <- '-';
            m.(i*2).(j*2+1) <- '-';
          | Ver ->
            m.(i*2-1).(j*2) <- '|';
            m.(i*2+1).(j*2) <- '|';
          | DownRight ->
            m.(i*2-1).(j*2-1) <- '\\';
            m.(i*2+1).(j*2+1) <- '\\';
          | DownLeft ->
            m.(i*2-1).(j*2+1) <- '/';
            m.(i*2+1).(j*2-1) <- '/'
        with Not_found ->
          ()
      in
      match edges a i j with
      | Horiz e -> update_result e Hor
      | Vert e -> update_result e Ver
      | Diag (e1,e2) -> update_result e1 DownRight; update_result e2 DownLeft
    ) a;
  Array.iter (fun a ->
      Array.iter (Format.printf "%c") a;
      Format.printf "@."
    ) m





let run () =
  let fout = open_out "problem.smt2" in
  let ff = Format.formatter_of_out_channel fout in
  let a = parse2 stdin in
  let (map,max) = find_map a in
  print_map ff map;
  declare_vars ff max a;
  edge_constraints ff a;
  vertex_constraints ff map a;
  Format.fprintf ff "(check-sat)@.";
  get_vars ff a;
  close_out fout;
  ignore(Unix.system "z3 problem.smt2 > result.smt2");
  let res = get_results map in
  (*print_results res;*)
  generate_result_matrix a res



let _ =
  run ()
