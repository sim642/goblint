open QCheck

module GenMonad =
struct
  include Gen

  let bind = (>>=) (* for ppx_monadic *)
end

let sequence_gen (gens: 'a Gen.t list): 'a list Gen.t =
  let open GenMonad in
  let f gen acc =
    do_;
    x <-- gen;
    xs <-- acc;
    return @@ x :: xs
  in
  List.fold_right f gens (return [])

let sequence (arbs: 'a arbitrary list): 'a list arbitrary =
  let gens = List.map gen arbs in
  make (sequence_gen gens)