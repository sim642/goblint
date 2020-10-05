(* open Defaults (* CircInterval needs initialized conf *) *)

let domains: (module Lattice.S) list = [
  (* (module IntDomainProperties.IntegerSet); (* TODO: top properties error *) *)
  (module IntDomain.Lifted); (* not abstraction of IntegerSet *)

  (* TODO: move to intDomains if passing *)
  (module IntDomain.Interval32);
  (module IntDomain.Booleans);

  (* TODO: fix *)
  (* (module IntDomain.CircInterval); *)
  (* (module IntDomain.Enums); *)
  (* (module IntDomain.IntDomTuple); *)

  (* (module ArbitraryLattice);
  (module SetDomain.Hoare (ArbitraryLattice) (struct let topname = "Top" end));
  (* (module PartitionDomain2.Make (
      struct
        include ArbitraryLattice
        let same_partition x y = equal x y
      end
    )); *)
  (module PartitionDomain2.Make (
      struct
        include ArbitraryLattice
        let same_partition x y = true
      end
    ));
  (module PartitionDomain2.Make (
      struct
        include ArbitraryLattice
        let same_partition x y = mem 'a' x = mem 'a' y
      end
    )); *)
]

let nonAssocDomains: (module Lattice.S) list = [
  (module IntDomain.DefExc);
]

let intDomains: (module IntDomain.S) list = [
  (module IntDomain.Flattened);
  (* (module IntDomain.Interval32); *)
  (* (module IntDomain.Booleans); *)
  (* (module IntDomain.CircInterval); *)
  (* (module IntDomain.DefExc); *)
  (* (module IntDomain.Enums); *)
  (* (module IntDomain.IntDomTuple); *)
]

let testsuite =
  List.map (fun d ->
      let module D = (val d: Lattice.S) in
      let module DP = DomainProperties.All (D) in
      DP.tests)
    domains
  |> List.flatten
let nonAssocTestsuite =
  List.map (fun d ->
      let module D = (val d: Lattice.S) in
      let module DP = DomainProperties.AllNonAssoc (D) in
      DP.tests)
    nonAssocDomains
  |> List.flatten
let intTestsuite =
  List.map (fun d ->
      let module D = (val d: IntDomain.S) in
      let module DP = IntDomainProperties.All (D) in
      DP.tests)
    intDomains
  |> List.flatten

let () =
  QCheck_runner.run_tests_main ~argv:Sys.argv (testsuite @ nonAssocTestsuite @ intTestsuite @ PartitionDomainTest.testsuite)
