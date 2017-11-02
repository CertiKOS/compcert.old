open Camlcoq
open RockSaltAsm

(* Debug *)
let print_globdef (id:AST.ident) (def: ((fundef, gv_info) AST.globdef) option) =
  let typ = 
    match def with
    | None -> "None"
    | Some d -> match d with
                | AST.Gfun f -> 
                   (match f with
                    | AST.Internal _ -> "Internal Function"
                    | AST.External _ -> "External Function")
                | AST.Gvar _ -> "Variable"
  in
  Printf.printf "%s: %s\n" (extern_atom id) typ

let print_globdefs (p:program) =
  List.iter (fun (id,def) -> print_globdef id def) p.prog_defs
