module type Partitioned =
sig
  include Printable.S
  val same_partition: t -> t -> bool
  val leq: t -> t -> bool
  val join: t -> t -> t
  val is_bot: t -> bool
  (* val bot: unit -> t *)
  val meet: t -> t -> t
  val widen: t -> t -> t
  val narrow: t -> t -> t
end

module type S =
sig
  include Lattice.S
  type elt
  val empty: unit -> t
  val is_empty: t -> bool
  val mem: elt -> t -> bool
  val add: elt -> t -> t
  val singleton: elt -> t
  val remove: elt -> t -> t
  val union: t -> t -> t
  (* val inter: t -> t -> t *)
  val diff: t -> t -> t
  (* val subset: t -> t -> bool *)
  val iter: (elt -> unit) -> t -> unit
  val map: (elt -> elt) -> t -> t
  val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all: (elt -> bool) -> t -> bool
  val exists: (elt -> bool) -> t -> bool
  val filter: (elt -> bool) -> t -> t
  (* val partition: (elt -> bool) -> t -> t * t *)
  val cardinal: t -> int
  val elements: t -> elt list
  val of_list: elt list -> t
  (* val min_elt: t -> elt *)
  (* val max_elt: t -> elt *)
  val choose: t -> elt
  (* val split: elt -> t -> t * bool * t *)
  module E: Partitioned with type t = elt

  val find_partition: elt -> t -> elt
end

module Make (E: Partitioned): S with type elt = E.t =
struct
  module E = E
  module S = SetDomain.Make (E)
  include S

  let name () = "PartitionDomain (" ^ E.name () ^ ")"

  (* assuming no leq between partitions *)
  let leq s t = S.for_all (fun x -> S.exists (fun y -> E.leq x y) t) s

  (* TODO: do joins without requiring bot *)
  (* let join_partitions s = S.map (fun x -> S.fold E.join (S.filter (E.same_partition x) s) (E.bot ())) s
  let join s t = join_partitions (S.union s t) *)
  let join s t =
    let f y (s, acc) =
      let (partition, s') = S.partition (E.same_partition y) s in
      (s', S.add (S.fold E.join partition y) acc)
    in
    let (s', acc) = S.fold f t (s, S.empty ()) in
    union s' acc

  (* adapted from SetDomain.Hoare *)
  let lt x y = E.leq x y && not (E.leq y x)
  let simplify s =
    (* assert (S.for_all (fun x -> not (E.is_bot x)) s); *)
    (* S.filter (fun x -> not (S.exists (lt x) s)) s *)
    S.filter (fun x -> not (E.is_bot x) && not (S.exists (lt x) s)) s

  (* let join s t = join s t |> simplify *)
  let apply_list f s = S.elements s |> f |> S.of_list
  let join_partitions a =
    let rec loop js = function
      | [] -> js
      | x::xs -> let (j,r) = List.fold_left (fun (j,r) x ->
          if E.same_partition x j then E.join x j, r else j, x::r
        ) (x,[]) xs in
        loop (j::js) r
    in
    apply_list (loop []) a
  let product_bot op s t =
    List.map (fun x -> List.filter_map (fun y -> if E.same_partition x y then Some (op x y) else None) (S.elements t)) (S.elements s) |> List.flatten |> fun x -> simplify (S.of_list x)
  let product_widen op s t =
    List.map (fun x -> List.filter_map (fun y -> if E.same_partition x y then op x y else None) (S.elements t)) (S.elements s) |> List.flatten |> fun x -> simplify (S.union t (S.of_list x))
  let meet s t = product_bot E.meet s t |> join_partitions

  let widen s t = product_widen (fun x y -> if E.leq x y then Some (E.widen x y) else None) s t |> join_partitions
  let narrow s t = product_bot (fun x y -> if E.leq y x then E.narrow x y else x) s t |> join_partitions

  let find_partition x s =
    try
      S.choose (S.filter (E.same_partition x) s)
    with
      Not_found -> x

  let of_list s = simplify (S.of_list s) |> join_partitions
  let arbitrary () = QCheck.map ~rev:elements of_list @@ QCheck.small_list (E.arbitrary ())
end

(*
  E.leq x y ==> E.same_partition x y ?
    E.join x y = y (maximal kept)
 *)

module type PartitionMapping =
sig
  include Printable.S
  type e
  val f: e -> t
end

(* module type S2 = S with type elt = E.t *)

module Optimized (P: S) (F: PartitionMapping with type e = P.E.t): S with type elt = P.E.t =
struct
  module E = P.E
  type elt = P.E.t
  include MapDomain.MapBot (
      struct
        include F
        let classify _ = failwith "classify"
        let class_name _ = failwith "class_name"
        let trace_enabled = false
      end
    ) (P)

  let empty = bot
  let is_empty = is_bot

  let elements m = fold (fun k v acc -> P.elements v @ acc) m []
  let choose m = List.hd (elements m)
  let cardinal m = List.length (elements m)
  let exists p m = List.exists p (elements m)
  let for_all p m = List.for_all p (elements m)
  let singleton x = add (F.f x) (P.singleton x) (empty ())
  let of_list l = List.fold_left (fun acc x -> add (F.f x) (P.singleton x) acc) (empty ()) l
  let union = join
  let find_partition x m = P.find_partition x (find (F.f x) m)
  let mem e m = exists (E.leq e) m
  let apply_list f m = of_list (f (elements m))
  let diff a b = apply_list (List.filter (fun x -> not (mem x b))) a
  let add e m = if mem e m then m else join (singleton e) m
  let remove x m =
    let ngreq x y = not (E.leq y x) in
    apply_list (List.filter (ngreq x)) m
  let iter f m = iter (fun k v -> P.iter (fun x -> f x) v) m
  let map f m = apply_list (List.map f) m
  let fold f m a = fold (fun k v acc -> P.fold f v acc) m a
  let filter f m = apply_list (List.filter f) m
end