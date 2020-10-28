open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let dependances = [[1];[-1;2];[-1;3;4;5];[-2;6];[-3;7];[-4;8;9];[-4;9];[-9;-6];[-9;-7];[-4;-5];[-8;-9];[-6;-7]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* est_dedans: int -> int list -> bool 
    vérifie si un élément x est dans une liste l*)
let rec est_dedans x l = match l with
  | [] -> false
  | h::t -> if h = x then true else est_dedans x t
;;

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)
let rec simplifie i clauses =
  let rec simplifie_aux = function
    | [] -> []
    | h::t-> if h = (i*(-1)) then simplifie_aux t else h::simplifie_aux t
  in
  match clauses with
  | [] -> clauses
  | h::t-> if est_dedans i h then simplifie i t
    else simplifie_aux (h)::(simplifie i t)
;;

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split exemple_3_12 []) *)
(* let () = print_modele (solveur_split exemple_7_2 [])  *)
(* let () = print_modele (solveur_split exemple_7_4 [])  *)
(* let () = print_modele (solveur_split exemple_7_8 [])  *)
(* let () = print_modele (solveur_split systeme [])      *)
(* let () = print_modele (solveur_split dependances [])  *) 
(* let () = print_modele (solveur_split coloriage [])    *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
  let rec unitaire_aux = function
    | [a] -> a
    | _ -> 0
  in
  match clauses with
  | [] -> raise (Not_found) (*On atteint la fin de la liste sans trouver de clause unitaire*)
  | h::t -> if unitaire_aux h = 0 then unitaire t else unitaire_aux h
;;

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  let l = List.sort compare (clauses |> List.flatten) in
  let rec pur_aux = function
    | [] -> failwith "pas de littéral pur" (*On atteint la fin de la liste sans trouver de littéral pur*)
    | h::t -> if (est_dedans (h*(-1)) l) then pur_aux t else h
  in
  pur_aux l
;;

(* supp_clause : int list list -> int list list 
  applique la suppression de clause*)
let rec supp_clause =
  let rec supp_clause_aux = function
    | [] -> [] (*Fin d'une clause*)
    | h::t -> 
    if (h > 0 && est_dedans (-h) t)||(h < 0 && est_dedans (h*(-1)) t) then []
    else h::supp_clause_aux t
  in
  function
  | [] -> [] (*Fin de la liste des clauses*)
  | h'::t' -> if supp_clause_aux h' = [] then (supp_clause t') else supp_clause_aux (h')::(supp_clause t')
;;

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  let cl = supp_clause clauses in
  let rec solveur_dpll_rec_aux = function
    | [] -> None (*la liste est vide car je n'ai plus de clauses*)
    | h::t -> if (solveur_dpll_rec (simplifie h cl) (h::interpretation) != None)
      then (solveur_dpll_rec (simplifie h cl) (h::interpretation))
      else solveur_dpll_rec_aux t
  in
  match cl with
  | [] -> Some interpretation
  | _ -> let u = try unitaire cl with
    | Not_found -> try pur cl with
      | Failure _ -> 0 in
    if (u = 0) then solveur_dpll_rec_aux (List.sort compare (cl |> List.flatten)) else
      solveur_dpll_rec (simplifie u cl) (u::interpretation)

;;

(* tests *)
(* let () = print_modele (solveur_dpll_rec exemple_3_12 []) *)
(* let () = print_modele (solveur_dpll_rec exemple_7_2 [])  *)
(* let () = print_modele (solveur_dpll_rec exemple_7_4 [])  *)
(* let () = print_modele (solveur_dpll_rec exemple_7_8 [])  *)
(* let () = print_modele (solveur_dpll_rec systeme [])      *)
(* let () = print_modele (solveur_dpll_rec dependances [])  *) 
(* let () = print_modele (solveur_dpll_rec coloriage [])    *) 

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
