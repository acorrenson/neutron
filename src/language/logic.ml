type logic =
  | Land of logic * logic
  | Lor of logic * logic
  | Limpl of logic * logic
  | Liff of logic * logic
  | Lneg of logic
  | Latom of int

module Literal = struct
  type t = Pos of int | Neg of int
  let compare = compare
end

module Clause = Set.Make(Literal)

module Instance = Set.Make(Clause)

let dump_lit = function
  | Literal.Pos c -> Printf.printf "%d " c
  | Literal.Neg c -> Printf.printf "-%d " c

let dump_clause c =
  print_string "{";
  Clause.iter (dump_lit) c;
  print_string "} "

let dump_cnf c =
  Instance.iter dump_clause c

let cnf f =
  let rec cnf_red sign = function
    | Land (a, b) ->
      if sign then begin
        let ca = cnf_red sign a in
        let cb = cnf_red sign b in
        Instance.union ca cb
      end else cnf_red true (Lor (a, b))
    | Lor (a, b) ->
      if sign then begin
        let ca = cnf_red sign a in
        let cb = cnf_red sign b in
        Instance.(
          fold (fun c1 -> union (map (Clause.union c1) cb)) ca empty)
      end else Instance.union (cnf_red false a) (cnf_red false b)
    | Limpl (a, b) ->
      cnf_red (sign) (Lor (Lneg a, b))
    | Liff (a, b) ->
      let ca = cnf_red sign (Limpl (a, b)) in
      let cb = cnf_red sign (Limpl (b, a)) in
      Instance.union ca cb
    | Lneg a ->
      cnf_red (not sign) a
    | Latom a ->
      Instance.singleton (Clause.singleton (if sign then Pos a else Neg a))
  in
  cnf_red true f

let _ =
  dump_cnf (cnf (Liff (Latom 1, Latom 2)))