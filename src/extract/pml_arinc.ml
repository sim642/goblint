open BatteriesExceptionless

(* enums *)
type return_code = SUCCESS | ERROR
and partition_mode = IDLE | COLD_START | WARM_START | NORMAL
and status = NOTCREATED | STOPPED | SUSPENDED | WAITING | READY | DONE
and waiting_for = NONE | BLACKBOARD | SEMA | EVENT | TIME
and queuing_discipline = FIFO | PRIO
[@@deriving show { with_path = false }, enum]

let extract_types = ["t123"] (* TODO extract variables of a certain type *)

let init ?(nproc=99) ?(nsema=99) ?(nevent=99) ?(nbboard=99) () = (* TODO better solution for the number of resources? the numbers are only for checking out-of-bounds accesses... *)
  let has_semas = nsema > 0 in
  let open Pml in let open Chan in
  let nproc   = fst @@ var (Byte nproc) "nproc" in
  let nsema   = fst @@ var (Byte nsema) "nsema" in
  let nevent  = fst @@ var (Byte nevent) "nevent" in
  let nbboard = fst @@ var (Byte nbboard) "nbboard" in
  Pml.do_; (* from now on ; is bind *)
  (* type delcarations, TODO generate this? *)
  (* TODO might need adjustment if there are enums with gaps or enums not starting at 0 *)
  enum return_code_of_enum show_return_code "return_code";
  enum partition_mode_of_enum show_partition_mode "partition_mode";
  enum status_of_enum show_status "status";
  enum waiting_for_of_enum show_waiting_for "waiting_for";
  enum queuing_discipline_of_enum show_queuing_discipline "queuing_discipline";
  (* variable declarations *)
  (* TODO inject: let%s status = arr nprocNOTCREATED in *)
  partition_mode <-- var (Enum (COLD_START, show_partition_mode)) "partition_mode";
  lock_level  <-- var (Byte 0) "lock_level"; (* scheduling only takes place if this is 0 *)
  exclusive   <-- var (Byte 0) "exclusive"; (* id of process that has exclusive privilige toecute if lockLevel > 0 *)
  status      <-- arr !nproc (Enum (NOTCREATED, show_status)) "status";
  (* TODO type for structured data types *)
  waiting_for <-- arr !nproc (Enum (NONE, show_waiting_for)) "waiting_for";
  waiting_id  <-- arr !nproc (Byte 0) "waiting_id";
  semas       <-- arr !nsema (Byte 0) "semas";
  semas_max   <-- arr !nsema (Byte 0) "semas_max";
  semas_chan  <-- arr !nsema (Chan.create !nproc (Byte 0)) "semas_chan";
  events      <-- arr !nevent (Bool false) "events";
  bboards     <-- arr !nbboard (Bool false) "bboards";

  (* just for asserts *)
  tasks_created <-- var (Byte 0) "tasks_created";
  semas_created <-- var (Byte 0) "semas_created";

  (* dummy variables for use in arguments *)
  let tid,tid_decl = var (Byte 0) "tid" in (* this is the id we give out for every new task *)
  (* general arguments *)
  let id,_     = var (Byte 0) "id" in
  let name,_   = var (String "") "name" in
  (*let r,_    = var (Enum (SUCCESS, show_return_code)) "r" in*)

  (* macros - used in extracted pml *)
  define "can_run" @@ A1 (id, fun id -> (!status !id == e READY show_status) && (!lock_level == i 0 || !exclusive == !id) && (!partition_mode == e NORMAL show_partition_mode || !id == i 0));

  (* helpers - these get inlined *)
  let task_info id = s "status["^i2s id^s "] = "^e2s (!status id)^s ", waiting_for[] = "^e2s (!waiting_for id)^s ", waiting_id[] = "^i2s (!waiting_id id) in
  let sema_info id = s "semas["^i2s id^s "] = "^i2s (!semas id) in
  let set_waiting id wfor wid = Pml.do_;
    println (s "set_waiting: process "^i2s id^s " will wait for "^i2s wid);
    waiting_for := id, (e wfor show_waiting_for);
    waiting_id  := id, wid;
    status      := id, (e WAITING show_status)
  in
  let set_ready id = Pml.do_;
    println (s "set_ready: process "^i2s id^s " set to ready. "^task_info id);
    waiting_for := id, (e NONE show_waiting_for);
    waiting_id  := id, i 0;
    status      := id, (e READY show_status)
  in
  let is_waiting id wfor wid = !status id == e WAITING show_status && !waiting_for id == e wfor show_waiting_for && !waiting_id id == wid in
  let remove_waiting id = Pml.do_;
    if has_semas then
      _foreach semas (fun j _ ->
          _ift (poll `Any (!semas_chan j) id) (recv `Any (!semas_chan j) id)
        )
    else nop;
    waiting_for := id, e NONE show_waiting_for;
  in

  (* preemption *)
  let mode,_ = var (Enum (COLD_START, show_partition_mode)) "mode" in
  extract "LockPreemption" @@ A0 (
    Pml.do_;
    incr lock_level;
    exclusive := !tid; (* TODO is this really changed if lock_level > 0? if yes, it is probably also restored... *)
  );
  extract "UnlockPreemption" @@ A0 (
    _ift (!lock_level > i 0) (decr lock_level)
  );
  extract "SetPartitionMode" @@ A1 (mode, fun mode ->
      partition_mode := !mode
    );

  (* processes *)
  extract "CreateProcess" @@ A1 (id(*; pri; per; cap]*), fun id ->
      Pml.do_;
      _assert (!status !id == e NOTCREATED show_status);
      status := !id, e STOPPED show_status;
      waiting_for := !id, e NONE show_waiting_for;
      incr tasks_created;
    );
  (* CreateErrorHandler *)
  extract "Start" @@ A1 (id, fun id ->
      Pml.do_;
      _assert (!status !id != e NOTCREATED show_status);
      remove_waiting !id;
      status := !id, e READY show_status;
    );
  extract "Stop" @@ A1 (id, fun id ->
      Pml.do_;
      _assert (!status !id != e NOTCREATED show_status);
      remove_waiting !id;
      status := !id, e STOPPED show_status;
    );
  extract "Suspend" @@ A1 (id, fun id ->
      Pml.do_;
      _assert (!status !id != e NOTCREATED show_status);
      status := !id, e SUSPENDED show_status;
    );
  extract "Resume" @@ A1 (id, fun id ->
      Pml.do_;
      _assert (!status !id != e NOTCREATED show_status);
      _ift (!status !id == e SUSPENDED show_status) (
        _ifte (!waiting_for !id == e NONE show_waiting_for)
          (status := !id, e READY show_status)
          (status := !id, e WAITING show_status)
      );
      status := !id, e SUSPENDED show_status;
    );

  (* semaphores *)
  let cur,_   = var (Byte 0) "cur" in
  let max,_   = var (Byte 0) "max" in
  let queuing,_ = var (Enum (FIFO, show_queuing_discipline)) "queuing" in
  extract "CreateSemaphore" ~id:(4,0,"sema") @@ A5 (name,cur,max,queuing,id, fun name cur max queuing id ->
      Pml.do_;
      println (s "CreateSemaphore: " ^ !name ^s ", "^ i2s !cur ^s ", "^ i2s !max ^s ", "^ e2s !queuing);
      _assert (!queuing == e FIFO show_queuing_discipline);
      semas := !id, !cur;
      semas_max := !id, !max;
      incr semas_created;
    );
  extract "GetSemaphoreId" ~id:(1,0,"sema") @@ A2 (name, id, fun name id -> skip);
  extract "WaitSemaphore" @@ A1 (id, fun id ->
      let id = !id in
      let sema = !semas id in
      let chan = !semas_chan id in
      _if [
        sema == i 0,
        println (s "WaitSema will block: "^sema_info id) >>
        _if [
          full  chan, fail (s "WaitSema: queue is full: "^sema_info id);
          nfull chan, println (s "WaitSema: Process "^i2s !tid^s " put into queue for sema "^i2s id)
        ] >>
        set_waiting !tid SEMA id;
        sema > i 0,
        println (s "WaitSema will go through: "^sema_info id) >>
        incr semas id;
        sema < i 0,
        fail (s "WaitSema: count<0: "^sema_info id)
      ]
    );
  extract "SignalSemaphore" @@ A1 (id, fun id ->
      let id = !id in
      let sema = !semas id in
      let chan = !semas_chan id in
      _if [
        (* no processes waiting on this semaphore -> increase count until max *)
        empty chan,
        println (s "SignalSema: empty queue") >>
        _ift (sema < !semas_max id) (incr semas id);
        nempty chan,
        println (s "SignalSema: "^i2s (len chan)^s " processes in queue for "^sema_info id) >>
        _foreach status (fun j _ ->
            println (s "SignalSema: check if process "^i2s j^s " is waiting. "^task_info j) >>
            _ift (is_waiting j SEMA id && poll `First chan j) (* process is waiting for this semaphore and is at the front of its queue *) (
              println (s "SignalSema: process "^i2s !tid^s " is waking up process "^i2s j) >>
              recv `First chan j >> (* consume msg from queue *)
              set_ready j >>
              break
            )
          )
      ]
    );

  (* events *)
