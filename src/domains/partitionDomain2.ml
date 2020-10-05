module type Partitioned =
sig
  include Printable.S
  val same_partition: t -> t -> bool
  val leq: t -> t -> bool
  val join: t -> t -> t
  val is_bot: t -> bool
  val bot: unit -> t
  val meet: t -> t -> t
  val widen: t -> t -> t
  val narrow: t -> t -> t
end

module type S =
sig
  include SetDomain.S

  val find_partition: elt -> t -> elt
end

module Make (E: Partitioned): S with type elt = E.t =
struct
  module E = E
  module S = SetDomain.Make (E)
  include S

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
  let simplify s = S.filter (fun x -> not (E.is_bot x) && not (S.exists (lt x) s)) s
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
    List.map (fun x -> List.map (fun y -> op x y) (S.elements t)) (S.elements s) |> List.flatten |> fun x -> simplify (S.of_list x)
  let product_widen op s t =
    List.map (fun x -> List.map (fun y -> op x y) (S.elements t)) (S.elements s) |> List.flatten |> fun x -> simplify (S.union t (S.of_list x))
  let meet s t = product_bot E.meet s t |> join_partitions

  let widen s t = product_widen (fun x y -> if E.leq x y then E.widen x y else E.bot ()) s t |> join_partitions
  let narrow s t = product_bot (fun x y -> if E.leq y x then E.narrow x y else x) s t |> join_partitions

  let find_partition x s =
    try
      S.choose (S.filter (E.same_partition x) s)
    with
      Not_found -> x
end

(*
  E.leq x y ==> E.same_partition x y ?
    E.join x y = y (maximal kept)
 *)