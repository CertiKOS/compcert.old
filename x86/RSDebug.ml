open Camlcoq

(* Debug *)
let print_rs_globdef (id:AST.ident) (def: ((RockSaltAsm.fundef, RockSaltAsm.gv_info) AST.globdef) option) =
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

let print_rs_globdefs (p:RockSaltAsm.program) =
  List.iter (fun (id,def) -> print_rs_globdef id def) 
            (let open RockSaltAsm in p.prog_defs)

let print_asm_globdef (id:AST.ident) (def: ((Asm.fundef, unit) AST.globdef) option) =
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

let print_asm_globdefs (p:Asm.program) =
  List.iter (fun (id,def) -> print_asm_globdef id def) 
            (let open Asm in p.prog_defs)
