(* open Pretyping *)

(** In Coq trunk, use the API for plugins, a subset of all the interfaces of Coq. *)   
open API

(** To use tactics from the Ltac plugin *)   
open Ltac_plugin   

(** Plugin declaration, reflected in myplug.v's "Declare ML Module" *)   
DECLARE PLUGIN "myplug"

let () = Mltop.add_known_plugin (fun () ->
  Flags.if_verbose Feedback.msg_info Pp.(str"myplug 1.0 at your service"))
  "myplug"
;;

open Glob_term
open Globnames
open Misctypes
open Evar_kinds
open Decl_kinds
open Names
open Proofview
open Pretyping
open Genarg
open Tacticals.New
open Stdarg

(* Checks whether a variable x appears in a term trm. 
Flag b true when recursion is allowed, false otherwise. *)
let rec find b x trm =
  (* First reduces, then tries to find the variable.
     b describes whether we reduce in this step,
     b' describes whether we found variables in the subcases,
     b'' is the reduction behaviour in the next step
 *)
  let redB b b' b'' trm = if (b&&b')
    then find b'' x (EConstr.to_constr Evd.empty (Reductionops.nf_all Evd.empty (EConstr.of_constr trm)))             
    else (b', trm) in
  match Term.kind_of_term trm with
  (* True if the variables correspond, false otherwise. *)  
  | Term.Rel y -> if (x == y) then (true, Term.mkRel x) else (false, Term.mkRel y) 
  | Term.Prod (y, s, t) -> (let (b1, n1) = find true x s in
                                  let (b2, n2) = find true (x +1) t in
                                  (b1 || b2, Term.mkProd (y, n1, n2) ))
  | Term.App (s, ts) ->  (let (b1, n1) = find true x s in
                                   let (b2, n2) = CArray.fold_map (fun b t -> let (b2, n2) = find true x t in
                                                                                 (b ||b2, n2))  false ts in
                                   redB b (b1 || b2) false (Term.mkApp (n1, n2)))
  | Term.Lambda (y, t1, t2) -> (let (b1, n1) = find true x t1 in
                                  let (b2, n2) = find true (x +1) t2 in
                                  (b1 || b2, Term.mkLambda (y, n1, n2) ))
  | Term.LetIn (y, s, t, u) ->  (let (b1, n1) = find true x s in
                                 let (b2, n2) = find true x t in
                                 let (b3, n3) = find true (x +1) u in
                                 redB b (b1 || b2 || b3) false (Term.mkLetIn (y, n1, n2, n3) )) (* TODO: THINK ABOUT REDUCTION THEORY *)
  | Term.Case (i, s, t, us) -> (let (b1, n1) = find true x s in
                                 let (b2, n2) = find true x t in
                                 let (b3, n3) = CArray.fold_map (fun b u -> let (b3, n3) = find true x u in
                                                                                 (b ||b3, n3))  false us  in
                                 redB b (b1 || b2 || b3) false (Term.mkCase (i, n1, n2, n3) )) (* TODO: THINK ABOUT REDUCTION THEORY. Maybe it would be clever to FIRST reduce the term matched on? *)
  | Term.Proj (y, z) -> redB b true true z
  | Term.Cast (s, k, t) ->  (let (b1, n1) = find true x s in
                                  let (b2, n2) = find true x t in
                                  (b1 || b2, Term.mkCast (n1, k, n2) ))
  | Term.Fix  ((ys, y), (name_array, type_array, term_array)) -> (
    let (b2, n2) = CArray.fold_map (fun b u -> let (b3, n3) = find true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false type_array in
    let (b3, n3) = CArray.fold_map (fun b u -> let (b3, n3) = find true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false term_array 
    in redB b (b2 || b3) false (Term.mkFix ((ys, y), (name_array, n2, n3))))
  (* TODO: THINK ABOUT REDUTION BEHAVIOUR. *)                                                                
  | Term.CoFix  (y, (name_array, type_array, term_array)) -> (
    let (b2, n2) = CArray.fold_map (fun b u -> let (b3, n3) = find true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false type_array in
    let (b3, n3) = CArray.fold_map (fun b u -> let (b3, n3) = find true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false term_array 
    in redB b (b2 || b3) false (Term.mkCoFix (y, (name_array, n2, n3))))
  (* TODO: THINK ABOUT REDUTION BEHAVIOUR. *)                                                                
  | _ -> (false, trm)
;;

let rec plugin (arg: Term.constr) : bool * Term.constr =
  match Term.kind_of_term arg with
  | Term.Lambda (x, _, trm) -> find true 1 trm
  | _ -> CErrors.user_err ~hdr:"myplug" Pp.(str "A lambda is required.")
;;

(** TODO: Check how the term can be returned. *)
let wrapper (s : Term.constr) =
  let (b, t) = plugin s in
  Feedback.msg_info Pp.(if b then str "The first argument is needed." else str "The first argument may be omitted.")
;;

VERNAC COMMAND EXTEND Myplug_test
       CLASSIFIED AS QUERY
| [ "Detect" constr(c) ] -> [let (evm,env) = Lemmas.get_current_context () in
                             let c' = Constrintern.interp_constr env evm c in
                             wrapper (fst c') ]
                              END

(** Command to print constant bodies associated to a global name *)
let myprint name =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  (* References can be constants, inductives, constructors or local variables,
     we only treat constants here. *)
  | ConstRef c ->
      begin match Global.body_of_constant c with
      | Some b ->
         (** Feedback is used to print information to various channels. *)
         Feedback.msg_info Pp.(Printer.pr_constr b)
      | None -> Feedback.msg_info Pp.(str "an axiom, nothing to print")
      end
  | _ ->
     (** Standard error reporting function *)
     CErrors.user_err ~hdr:"myplug" Pp.(str "not implemented")
;;

(** Extend the Vernacular grammar for our new command. 
    The CLASSIFIED clause is used by the STM to schedule the execution
    of this command when seen in a document. *)  
VERNAC COMMAND EXTEND Myplug_print
       CLASSIFIED AS QUERY
| [ "Myprint" global(name) ] -> [ myprint name ]
END