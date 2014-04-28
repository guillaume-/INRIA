module Identifier = struct
  type t = string
  let compare = compare
  let of_string s = s
end

module IdentifierSet = struct
  include Set.Make(Identifier)
  let from_list l = List.fold_right add l empty 
end

