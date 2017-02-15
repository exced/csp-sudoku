open Graph.Pack.Graph;;
open Format;;

exception Found;;
exception Fail;;

(*set of legal values for a vertex *)
let domain = [1;2;3;4;5;6;7;8;9];;

(* type of vertex : x and y position in sudoku + available domain *)
type vt = {
    x: int; 
    y: int;
    mutable d: int list;
};;

(* Abstract graph type*)
module G = Graph.Imperative.Graph.Abstract(struct type t = vt end)

(* The Sudoku grid = a graph with 9x9 nodes *)
let g = G.create ();;

(* We create the 9x9 nodes, add them to the graph and keep them in a matrix 
   for later access *)
let nodes = 
    let new_node i j = let r = {x=i; y=j; d=domain} in let v = G.V.create (r) in 
    G.add_vertex g v; v in
    Array.init 9 (fun i -> Array.init 9 (new_node i))
;;

(* shortcuts for easier access *)
let node i j = nodes.(i).(j);;

(* remove element e from list l and returns l *)
let listRemoveElement e l = List.filter (fun x -> x <> e) l;; 

(* set domain and apply constraints on other concerned nodes *)
let applyConstraints n () = 
    match (G.V.label n).d with
    | [a] -> G.iter_succ (fun vt -> (G.V.label vt).d <- listRemoveElement a (G.V.label vt).d;) g n;
    | _ -> ();
;;

let applyInitConstraints () =
    G.iter_vertex (fun vt -> applyConstraints vt ();) g;
;;   

(* We read the initial constraints from standard input *)
let createFromStdin () =
    for i = 0 to 8 do
        let s = read_line () in
        for j = 0 to 8 do 
            match s.[j] with
            | '1'..'9' as ch -> 
                (G.V.label (node i j)).d <- [(Char.code ch - Char.code '0')];
                G.Mark.set (node i j) (Char.code ch - Char.code '0');
            | _ -> ()
        done
    done
;;

(* We add the 810 constraint edges: 
   two nodes are connected whenever they can't have the same value,
   i.e. they belong to the same line, the same column or the same 3x3 group *)
let initConstraints () =
    for i = 0 to 8 do
        for j = 0 to 8 do
            for k = 0 to 8 do
                if k <> i then G.add_edge g (node i j) (node k j); 
                if k <> j then G.add_edge g (node i j) (node i k); 
            done;
            let gi = 3 * (i / 3) and gj = 3 * (j / 3) in
            for di = 0 to 2 do 
                for dj = 0 to 2 do
                    let i' = gi + di and j' = gj + dj in
                    if i' <> i || j' <> j then G.add_edge g (node i j) (node i' j'); 
                done
            done
        done 
    done    
;;     

let rec invalid ?(i=0) x y n =
i<9 && ( (G.Mark.get (node y i)) = n || (G.Mark.get (node i x)) = n || (G.Mark.get (node (y/3*3 + i/3) (x/3*3 + i mod 3))) = n || invalid ~i:(i+1) x y n )

(*
 * Constraints: is n value invalid ? check line, row and unit.
*) 
let rec valid ?(i=0) n value =
    let x = (G.V.label n).x in let y = (G.V.label n).y in
    not (i<9 && ( (G.Mark.get (node y i)) = value || (G.Mark.get (node i x)) = value || (G.Mark.get (node (y/3*3 + i/3) (x/3*3 + i mod 3))) = value || valid ~i:(i+1) n value ))
;;    

(* 
 * isValid in given assignments ?
 *)
let isConsistent v l = 
    List.fold_right (fun vt vq -> (valid vt v) && vq) l true
;; 

(* is t include in l ? *)
let varInclude t l =
	List.fold_right (fun vt vq -> (t = vt) || vq) l false;
;;   
 
(* get unassigned variables in csp *) 
let getUnassigned g =
    G.fold_vertex (fun vt q -> 
        match (G.V.label vt).d  with
        | [a] -> q
        | _ -> vt::q
    ) g;
;;

(* get unassigned variables in graph \ list *) 
let selectUnassigned l =
    G.fold_vertex (fun vt q ->
        if (varInclude vt l) then q else vt::q
    ) g;
;;

(* get assigned variables in csp *) 
let getAssigned g =
    G.fold_vertex (fun vt q -> 
        match (G.V.label vt).d  with
        | [a] -> vt::q
        | _ -> q
    ) g;
;;      

(* minimum remaining values + degree heuristic strategy *)
let selectStrategy v1 v2 =
    if (List.length (G.V.label v1).d) = (List.length (G.V.label v2).d) then
        let nbConsRestCsp v = List.fold_right (fun vt q -> List.length (G.V.label vt).d + q) (G.succ g v) 0 in
        if ((nbConsRestCsp v1) <= (nbConsRestCsp v2)) then v1 else v2
    else if (List.length (G.V.label v1).d) < (List.length (G.V.label v2).d) then v1
    else v2
;;    

let selectVarStrategy l =
    match l with
    | [x] -> x
    | h::t -> List.fold_left (fun hs ts -> selectStrategy hs ts) h l
;; 

let nbConstraints a n = List.fold_right (fun vt q ->
    let d = (G.V.label vt).d in
    match d with
    | [x] -> q
    | _ ->
        if (varInclude a d) then 1 + q else q) (G.succ g n) 0;; 

(* least constraining value *)
let orderDomainLeastConstraining n =
    List.sort (fun a b -> if ((nbConstraints a n) > (nbConstraints b n)) then -1 else
    (if (nbConstraints a n) < (nbConstraints b n) then 1 else 0)) ((G.V.label n).d)
;;    

(* high level fold func : iterates until (l = u) *)
let rec fold f accu l u = if (l = u) then accu else fold f (f accu l) (l+1) u;;

(* 
let rec search ?(x=0) ?(y=0) f accu = match x, y with
    9, y -> search ~x:0 ~y:(y+1) f accu (* Next row *)
  | 0, 9 -> f accu                      (* Found a solution *)
  | x, y ->
      if ((G.Mark.get (node y x)) <> 0) then search ~x:(x+1) ~y f accu else
        fold (fun accu n ->
                if invalid x y n then accu else
                  (G.Mark.set (node y x) n;
                   let accu = search ~x:(x+1) ~y f accu in
                   G.Mark.set (node y x) 0;
                   accu)) accu 1 10;;
*)                   

(*
 * Backtracking solver
 * @param g = csp
 *)
let rec backtrack f accu =
    if (List.length l >= 81) then l else
        let var = selectVarStrategy ((selectUnassigned l) []) in
        List.iter (fun value -> 
        if (isConsistent value l) then
            
            try (back_rec (l@[var])) with            
            | Fail -> (listRemoveElement var l) 
            | Found -> l
            | _ -> (l@[var])
        ) (orderDomainLeastConstraining var);
    in back_rec ((getAssigned g) []) ;;
;;    

(* Displaying the current state of the graph *)
let display () =
  for i = 0 to 8 do
    for j = 0 to 8 do printf "%d" (G.Mark.get (node i j)) done;
    printf "\n";
  done;
  printf "@?"
;;    


 let solveFromStdin () =
    createFromStdin ();
    initConstraints ();
    applyInitConstraints ();
    display (); 
    (* 
    printf "%d solutions\n" (search (fun i -> display(); i+1) 0)
    *)
;;    
solveFromStdin ();;



