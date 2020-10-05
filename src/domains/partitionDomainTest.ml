module type FiniteSetElems =
sig
  type t
  val elems: t list
end

module FiniteSet (E:Printable.S) (Elems:FiniteSetElems with type t = E.t) =
struct
  module E =
  struct
    include E
    let arbitrary () = QCheck.oneofl ~print:(E.short 10) Elems.elems
  end

  include SetDomain.Make (E)
  let name () = "FiniteSet (" ^ E.name () ^ ") ([" ^ (String.concat "; " (List.map (E.short 10) Elems.elems)) ^ "])"
  let top () = of_list Elems.elems
  let is_top x = equal x (top ())
end

module PrintableChar =
struct
  type t = char [@@deriving to_yojson]
  include Printable.Std
  let name () = "char"
  let short _ x = String.make 1 x

  module P =
  struct
    type t' = t
    let name = name
    let short = short
  end
  include Printable.PrintSimple (P)

  let hash = Char.code
  let equal = Char.equal
end

module ArbitraryLattice = FiniteSet (PrintableChar) (
  struct
    type t = char
    let elems = ['a'; 'b'; 'c'; 'd']
  end
)

module PartitionedProperties (D: PartitionDomain2.Partitioned): DomainProperties.S =
struct
  open QCheck

  include DomainProperties.DomainTest (
      struct
        include D
        let top () = failwith "top"
        let is_top _ = failwith "is_top"
        let bot () = failwith "bot"
      end
    )

  (* same is equivalence *)
  let same_refl = make ~name:"same refl" (arb) (fun a -> D.same_partition a a)
  let same_sym = make ~name:"same sym" (pair arb arb) (fun (a, b) -> D.same_partition a b = D.same_partition b a)
  let same_trans = make ~name:"same trans" (triple arb arb arb) (fun (a, b, c) -> (D.same_partition a b && D.same_partition b c) ==> D.same_partition a c)

  (* same is congruence ? *)
  let leq_same = make ~name:"leq same" (pair arb arb) (fun (a, b) -> D.leq a b ==> D.same_partition a b)
  let join_same = make ~name:"join same" (pair arb arb) (fun (a, b) -> assume (D.same_partition a b); D.same_partition a (D.join a b) && D.same_partition b (D.join a b))
  let meet_same = make ~name:"meet same" (pair arb arb) (fun (a, b) -> assume (D.same_partition a b); D.same_partition a (D.meet a b) && D.same_partition b (D.meet a b))
  let widen_same = make ~name:"widen same" (pair arb arb) (fun (a, b) -> assume (D.same_partition a b); D.same_partition a (D.widen a (D.join a b)) && D.same_partition b (D.widen a (D.join a b)))
  let narrow_same = make ~name:"narrow same" (pair arb arb) (fun (a, b) -> assume (D.same_partition a b); D.same_partition a (D.narrow a b) && D.same_partition b (D.narrow a b))

  let tests = [
    same_refl;
    same_sym;
    same_trans;
    leq_same;
    join_same;
    meet_same;
    widen_same;
    narrow_same
  ]
end

module PartitionProperties (D: PartitionDomain2.S): DomainProperties.S =
struct
  module A = DomainProperties.AllNonTop (D)
  module P = PartitionedProperties (D.E)

  let tests = A.tests @ P.tests
end

module Arbitrary1Props = DomainProperties.All (ArbitraryLattice)
module Partition1Props = PartitionProperties (
    PartitionDomain2.Make (
      struct
        include ArbitraryLattice
        let same_partition x y = true
      end
    )
  )

module P =
struct
  include IntDomain.FlatPureIntegers
  (* let arbitrary () = QCheck.map ~rev:Int64.to_int Int64.of_int @@ QCheck.small_int *)
  let arbitrary () = QCheck.oneofl ~print:Int64.to_string [0L; 1L; 2L; 3L]
end

module ArbitraryLattice2 =
struct
  (* module P = IntDomain.FlatPureIntegers *)
  include Lattice.Prod (ArbitraryLattice) (P)
  let same_partition (_, x) (_, y) = P.equal x y
end

(* module Arbitrary2Props = DomainProperties.All (ArbitraryLattice2) *)
module Partition2Props = PartitionProperties (
    PartitionDomain2.Make (ArbitraryLattice2)
  )

module ArbitraryLattice3 =
struct
  (* module P = IntDomain.FlatPureIntegers *)
  include P
  let same_partition x y = P.equal x y
end

(* module Arbitrary3Props = DomainProperties.All (ArbitraryLattice3) *)
module Partition3Props = PartitionProperties (
    PartitionDomain2.Make (ArbitraryLattice3)
  )

module Partition1OptProps = PartitionProperties (
    PartitionDomain2.Optimized (PartitionDomain2.Make (
        struct
          include ArbitraryLattice
          let same_partition x y = true
        end
      )) (
        struct
          include Printable.Unit
          type e = ArbitraryLattice.t
          let f _ = ()
        end
      )
  )

module Partition2OptProps = PartitionProperties (
    PartitionDomain2.Optimized (PartitionDomain2.Make (ArbitraryLattice2)) (
        struct
          include IntDomain.Integers
          type e = ArbitraryLattice2.t
          let f (_, x) = x
        end
      )
  )

module Partition3OptProps = PartitionProperties (
    PartitionDomain2.Optimized (PartitionDomain2.Make (ArbitraryLattice3)) (
        struct
          include IntDomain.Integers
          type e = ArbitraryLattice3.t
          let f x = x
        end
      )
  )
let testsuite = Arbitrary1Props.tests @ Partition1Props.tests @ Partition2Props.tests @ Partition3Props.tests @ Partition1OptProps.tests @ Partition2OptProps.tests @ Partition3OptProps.tests