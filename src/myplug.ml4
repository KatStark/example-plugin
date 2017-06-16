(* open Pretyping *)

(** In Coq trunk, use the API for plugins, a subset of all the interfaces of Coq. *)   

(** To use tactics from the Ltac plugin *)   
open Ltac_plugin   


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
open Reductionops
open Genarg
open Tacticals.New
open Stdarg

let redBetaIotaZeta env t =
          EConstr.to_constr Evd.empty 
          (Reductionops.nf_betaiotazeta (* or use Redexpr.cbv_vm *) 
            (* env *)
            Evd.empty 
            (EConstr.of_constr t))

let whdAll env t =
          EConstr.to_constr Evd.empty 
          (Reductionops.whd_all env
            Evd.empty 
            (EConstr.of_constr t))

(* let whdNthTerm (ts : Term.constr array) (n): bool(*?*)*Term.constr array *)
let rec isHeadAConstructor (t:Term.constr) :bool =
  match Term.kind_of_term t with
  | Term.Construct _ -> true
  | Term.App (f,_) -> isHeadAConstructor f
  | _ -> false

(* Checks whether a variable x appears in a term trm. 
Flag b true when recursion is allowed, false otherwise. *)
let rec find (env: Environ.env) b x trm =
  (* First reduces, then tries to find the variable.
     b describes whether we reduce in this step. this is to avoid looping when no progress is made.
     b' true iff [x] was found in [trm]
 *)
  let redB (env: Environ.env) b b' trm = 
      (*Feedback.msg_info (Printer.pr_constr_env env Evd.empty trm); *)
    if (b&&b')
    then 
      let trmn= (redBetaIotaZeta env trm) in
      (* Feedback.msg_info (Printer.pr_constr trmn); *)
      find env false x trmn
    else (b', trm) in
    if Vars.noccurn x trm then (false,trm) else 
 (
  match Term.kind_of_term trm with
  (* True if the variables correspond, false otherwise. *)  
  | Term.Rel y -> if (x == y) then (true, Term.mkRel x) else (false, Term.mkRel y) 
  | Term.Prod (y, s, t) ->(let (b1, n1) = find env true x s in
      let env = Environ.push_rel (Context.Rel.Declaration.LocalAssum (y,s)) env in
                                  let (b2, n2) = find env true (x +1) t in
                                  (b1 || b2, Term.mkProd (y, n1, n2) ))
  | Term.App (s, ts) -> 
      (let n1 = whdAll env s in
      let (progress, newApTerm) =
      (match Term.kind_of_term n1 with
      | Term.Lambda (lamVar, lamTyp, lamBody) ->
          (true, Term.mkApp (n1,ts))
      | Term.Fix  ((structArgs, mutIndex), _) ->
          (let structArgIndex = Array.get structArgs mutIndex in
          let args = Array.mapi
            (
              fun i bd -> if i=structArgIndex then whdAll env bd else bd 
            )
            ts in
            let structArg = Array.get args structArgIndex in
            (isHeadAConstructor structArg, Term.mkApp (n1,args))
          )

      | _ -> (false, Term.mkApp (n1,ts))
      ) in
      if progress 
      then
        find env true x (redBetaIotaZeta env newApTerm)
      else
      let (b1, n1) =  find env true x n1 in
      let (b2, n2) = CArray.fold_map (fun b t -> let (b2, n2) = find env true x t in
                                                                                 (b ||b2, n2))  false ts in
                                   ((b1 || b2), Term.mkApp (n1, n2)))
  | Term.Lambda (y, typ, t2) ->(let (b1, n1) = find env true x typ in
      let env = Environ.push_rel (Context.Rel.Declaration.LocalAssum (y,typ)) env in
                                  let (b2, n2) = find env true (x +1) t2 in
                                  (b1 || b2, Term.mkLambda (y, n1, n2) ))
  | Term.LetIn (y, s, typ, u) ->  (let (b1, n1) = find env true x s in
                                 let (b2, n2) = find env true x typ in
      let env = Environ.push_rel (Context.Rel.Declaration.LocalDef (y,s,typ)) env in
                                 let (b3, n3) = find env true (x+1) u in
                                 redB env b (b1 || b2 || b3)  (Term.mkLetIn (y, n1, n2, n3) ))
  | Term.Case (i, discriminee, t, us) -> (*the branches are lambdas. so no need to add to the typing context*) 
    let discriminee = whdAll env discriminee in
    if (isHeadAConstructor discriminee)
    then 
      let wholeTerm =  redBetaIotaZeta env (Term.mkCase (i, discriminee, t, us)) in
      find env true x wholeTerm
    else
      let (b1, n1) = find env true x discriminee in
      let (b2, n2) = find env true x t in
      let (b3, n3) = 
        CArray.fold_map 
          (fun b u -> let (b3, n3) = find env true x u in (b ||b3, n3)) false us  in
      (b1 || b2 || b3,Term.mkCase (i, n1, n2, n3))
  | Term.Proj (y, z) ->  ( redB env b true z)
  (*TODO: just ignore [t] and recurse on [s]? Casts can be safely erased in Term.constr because 
    there is no ambiguity?*)
  | Term.Cast (s, k, t) -> ( (let (b1, n1) = find env true x s in
                                  let (b2, n2) = find env true x t in
                                  (b1 || b2, Term.mkCast (n1, k, n2) )))
  | Term.Fix  ((ys, y), (name_array, type_array, term_array)) -> (
    (* TODO: add binders to typing context. *)
    let (b2, n2) = CArray.fold_map (fun b u -> let (b3, n3) = find env true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false type_array in
    let (b3, n3) = CArray.fold_map (fun b u -> let (b3, n3) = find env true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false term_array 
    in redB env b (b2 || b3) (Term.mkFix ((ys, y), (name_array, n2, n3))))
  (* TODO: THINK ABOUT REDUTION BEHAVIOUR. *)                                                                
  | Term.CoFix  (y, (name_array, type_array, term_array)) ->  (
    let (b2, n2) = CArray.fold_map (fun b u -> let (b3, n3) = find env true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false type_array in
    let (b3, n3) = CArray.fold_map (fun b u -> let (b3, n3) = find env true (x + CArray.length name_array) u in
                                               (b ||b3, n3))  false term_array 
    in redB env b (b2 || b3) (Term.mkCoFix (y, (name_array, n2, n3))))
  (* TODO: THINK ABOUT REDUTION BEHAVIOUR. *)                                                                
  | _ -> (false, trm))
;;

let rec plugin (arg: Term.constr) : bool * Names.Name.t * Term.constr * Term.constr =
  match Term.kind_of_term arg with
  | Term.Lambda (x, typ, trm) -> 
    let env = Environ.push_rel (Context.Rel.Declaration.LocalAssum (x,typ)) (Global.env ()) in
    let (b, body) = find env true 1 trm in
    (b,x, typ, body)
  | _ -> CErrors.user_err ~hdr:"myplug" Pp.(str "A lambda is required. Given a [Lam (x:T) b], the plugin tries
        to come up with a [b'] that is definitionally equal to b and does not mention x")
;;

(* Printer.pr_constr *)
let wrapper (s : Term.constr) =
  let (b,_,_, t) = plugin s in
  Feedback.msg_info 
     Pp.(str (if b then ( "The first argument is needed. The reduced term is")  
        else "The first argument may be omitted. The reduced term is: ")++ Printer.pr_constr t) 
;;

let declare (s : Term.constr) (name : Names.Id.t) =
  let (b, x, typ, body) = plugin s in
  let body= if b then Term.mkLambda (x, typ, body) else body in
  let _ = 
      Declare.declare_definition 
	      ~kind:Decl_kinds.Definition name
	      (body, Univ.ContextSet.empty) in ()

;;

(** Plugin declaration, reflected in myplug.v's "Declare ML Module" *)   
DECLARE PLUGIN "myplug"

VERNAC COMMAND EXTEND Myplug_test
       CLASSIFIED AS QUERY
| [ "Detect" constr(c) ] -> [let (evm,env) = Lemmas.get_current_context () in
                             let c' = Constrintern.interp_constr env evm c in
                             wrapper (fst c') ]
                              END

VERNAC COMMAND EXTEND ReduceAwayLamVar
       CLASSIFIED AS SIDEFF
| [ "ReduceAwayLamVar" ident(name) ":=" constr(c)  ] -> [let (evm,env) = Lemmas.get_current_context () in
                             let c' = Constrintern.interp_constr env evm c in
                             declare (fst c') name]
                              END
