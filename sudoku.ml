open Graph.Pack.Graph;;
open Format;;

exception Failure

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
(* Queue of arcs *)
let arcsQ = [];;

(* We create the 9x9 nodes, add them to the graph and keep them in a matrix 
   for later access *)
let nodes = 
    let new_node i j = let r = {x=i; y=j; d=domain} in let v = G.V.create (r) in 
    G.add_vertex g v; v in
    Array.init 9 (fun i -> Array.init 9 (new_node i))
;;

let node i j = nodes.(i).(j);; (* shortcut for easier access *)

(* We read the initial constraints from standard input *)
let createFromStdin () =
    for i = 0 to 8 do
        let s = read_line () in
        for j = 0 to 8 do 
            match s.[j] with
            | '1'..'9' as ch -> 
                G.Mark.set (node i j) (Char.code ch - Char.code '0');
            | _ -> ()
        done
    done
;;

(* We add the 810 edges: 
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

(* Displaying the current state of the graph *)
let display () =
    for i = 0 to 8 do
        for j = 0 to 8 do 
            printf "%d" (G.Mark.get (node i j)) done;
        printf "\n";
    done
;;

(* Display the current domains of the graph *)
let displayDomain { x = x; y = y; d = d } () = List.map (fun v -> Format.printf "%d, " v) d;;
let displayDomains () =
    for i = 0 to 8 do
        printf "[";
        for j = 0 to 8 do 
            printf "\n";
            displayDomain (G.V.label (node i j)) ();
        done;
        printf "]\n";
    done
;;        

(*
 * ac3
 *)
 (*
let ac3 () =
    List.fold_right (
        fun (xi, xj) q1 -> if (rmInconsistentValues xi xj) then 
            List.fold_right (fun xk q2 -> q1@[(xk, xi)]) (G.find_all_edges g xk xi) ()
    ) arcsQ ();
;;
*)
(*
let rmInconsistentValues xi xj = 

;;    
*)

 let solveFromStdin () =
    createFromStdin ();
    initConstraints ();
    display ()
;;    


solveFromStdin ();;

(* displayDomains ();; *)


(*
 * Constraints: is n value valid ? check line, row and unit.
 
let rec invalid ?(i=0) x y n = 
    i<9 && ( csp.(y).[i] = n || csp.(i).[x] = n || csp.(y/3*3 + i/3).[x/3*3 + i mod 3] = n || invalid ~i:(i+1) x y n )
*) 
