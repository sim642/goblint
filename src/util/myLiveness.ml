
(* Calculate which variables are live at
 * each statememnt.
 *
 * copied from ../cil/ext/liveness.ml with minor changes to compute a big hash
 * for all sids all over the program.
 *
*)

open Cil
open Feature
open Pretty

module DF = Dataflow
module UD = Usedef
module IH = Inthash
module E = Errormsg

let debug = ref false

let live_label = ref ""
let live_func = ref ""

module VS = UD.VS

let debug_print () vs = (VS.fold
                           (fun vi d ->
                              d ++ text "name: " ++ text vi.vname
                              ++ text " id: " ++ num vi.vid ++ text " ")
                           vs nil) ++ line

let min_print () vs = (VS.fold
                         (fun vi d ->
                            d ++ text vi.vname
                            ++ text "(" ++ d_type () vi.vtype ++ text ")"
                            ++ text ",")
                         vs nil) ++ line

let printer = ref debug_print

module LiveFlow = struct
  let name = "Liveness"
  let debug = debug
  type t = VS.t

  let pretty () vs =
    let fn = !printer in
    fn () vs

  let stmtStartData = IH.create 113
  let visited_fds = ref VS.empty

  let funcExitData = VS.empty

  let combineStmtStartData (stm:stmt) ~(old:t) (now:t) =
    if not(VS.compare old now = 0)
    then Some(VS.union old now)
    else None

  let combineSuccessors = VS.union

  let doStmt stmt =
    if !debug then ignore(E.log "looking at: %a\n" d_stmt stmt);
    let handle_stm vs = match stmt.skind with
        Instr _ -> vs
      | s -> let u, d = UD.computeUseDefStmtKind s in
        VS.union u (VS.diff vs d)
    in
    DF.Post handle_stm

  let doInstr i vs =
    let transform vs' =
      let u,d = UD.computeUseDefInstr i in
      VS.union u (VS.diff vs' d)
    in
    DF.Post transform

  let filterStmt stm1 stm2 = true

end

module L = DF.BackwardsDataFlow(LiveFlow)

(* XXX: This does not compute the best ordering to
 * give to the work-list algorithm.
*)
let all_stmts = ref []
class nullAdderClass = object(self)
  inherit nopCilVisitor

  method vstmt s =
    all_stmts := s :: (!all_stmts);
    IH.add LiveFlow.stmtStartData s.sid VS.empty;
    DoChildren

end

let null_adder fdec =
  ignore(visitCilFunction (new nullAdderClass) fdec);
  !all_stmts

let computeLiveness fdec: unit =
  if VS.mem fdec.svar !LiveFlow.visited_fds then
    LiveFlow.visited_fds := VS.add fdec.svar !LiveFlow.visited_fds
  else begin
    (*  IH.clear LiveFlow.stmtStartData;*)
    UD.onlyNoOffsetsAreDefs := false;
    all_stmts := [];
    let a = null_adder fdec in
    try
      L.compute a
    with E.Error -> begin
        ignore(E.log "Liveness failed on function:\n %a\n" d_global (GFun(fdec,locUnknown)));
        E.s "Bug in Liveness compute"
      end
  end

let getLiveSet sid =
  try Some(IH.find LiveFlow.stmtStartData sid)
  with Not_found -> None

let getLiveness (s:stmt) = Inthash.find LiveFlow.stmtStartData s.sid

let getPostLiveness (s:stmt) : LiveFlow.t =
  let foldLiveness live s = VS.union live (getLiveness s) in
  List.fold_left foldLiveness VS.empty s.succs

let instrLiveness (il : instr list) (stm : stmt) (vs : VS.t) (out: bool) : VS.t list =
  let proc_one vsl i =
    match vsl with
    | [] ->
      let u,d = UD.computeUseDefInstr i in
      (VS.union u (VS.diff vs d))::vsl
    | vs'::rst ->
      let u,d = UD.computeUseDefInstr i in
      (VS.union u (VS.diff vs' d))::vsl
  in
  let liveout = getPostLiveness stm in
  let folded = List.fold_left proc_one [liveout] (List.rev il) in
  if out then List.tl folded else folded

(* Inherit from this to visit with liveness info at instructions.
   If out is true, then gives liveness after instructions.
   If out is false, then gives liveness before instructions. *)
class livenessVisitorClass (out : bool) = object(self)
  inherit nopCilVisitor

  val mutable sid = -1

  val mutable liv_dat_lst = []

  val mutable cur_liv_dat = None

  method vstmt stm =
    sid <- stm.sid;
    match getLiveSet sid with
    | None -> begin
        if !debug then E.log "livVis: stm %d has no data\n" sid;
        cur_liv_dat <- None;
        DoChildren
      end
    | Some vs -> begin
        match stm.skind with
        | Instr il -> begin
            liv_dat_lst <- instrLiveness il stm vs out;
            DoChildren
          end
        | _ -> begin
            cur_liv_dat <- None;
            DoChildren
          end
      end

  method vinst i =
    if liv_dat_lst = [] then (if !debug then E.log "livnessVisitor: il liv_dat_lst mismatch\n")
    else begin
      let data = List.hd liv_dat_lst in
      cur_liv_dat <- Some(data);
      liv_dat_lst <- List.tl liv_dat_lst;
      if !debug then E.log "livVis: at %a, data is %a\n" d_instr i debug_print data;
    end;
    DoChildren
end

let print_everything () =
  let d = IH.fold (fun i vs d ->
      d ++ num i ++ text ": " ++ LiveFlow.pretty () vs)
      LiveFlow.stmtStartData nil in
  ignore(printf "%t" (fun () -> d))

let match_label lbl = match lbl with
    Label(str,_,b) ->
    if !debug then ignore(E.log "Liveness: label seen: %s\n" str);
    (*b && *)(String.compare str (!live_label) = 0)
  | _ -> false

class doFeatureClass = object(self)
  inherit nopCilVisitor

  method vfunc fd =
    if String.compare fd.svar.vname (!live_func) = 0 then
      (Cfg.clearCFGinfo fd;
       ignore(Cfg.cfgFun fd);
       computeLiveness fd;
       if String.compare (!live_label) "" = 0 then
         (printer := min_print;
          print_everything();
          SkipChildren)
       else DoChildren)
    else SkipChildren

  method vstmt s =
    if List.exists match_label s.labels then try
        let vs = IH.find LiveFlow.stmtStartData s.sid in
        (printer := min_print;
         ignore(printf "%a" LiveFlow.pretty vs);
         SkipChildren)
      with Not_found ->
        if !debug then ignore(E.log "Liveness: stmt: %d not found\n" s.sid);
        DoChildren
    else
      (if List.length s.labels = 0 then
         if !debug then ignore(E.log "Liveness: no label at sid=%d\n" s.sid);
       DoChildren)

end

let do_live_feature (f:file) =
  visitCilFile (new doFeatureClass) f

let feature =
  {
    fd_name = "Liveness";
    fd_enabled = false;
    fd_description = "Spit out live variables at a label";
    fd_extraopt = [
      "--live_label",
      Arg.String (fun s -> live_label := s),
      " Output the variables live at this label";
      "--live_func",
      Arg.String (fun s -> live_func := s),
      " Output the variables live at each statement in this function.";
      "--live_debug",
      Arg.Unit (fun n -> debug := true),
      " Print lots of debugging info";];
    fd_doit = do_live_feature;
    fd_post_check = false
  }
