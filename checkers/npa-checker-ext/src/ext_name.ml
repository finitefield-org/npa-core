type t = string list

let contains_dot component =
  let rec loop index =
    if index >= String.length component then false
    else if component.[index] = '.' then true
    else loop (index + 1)
  in
  loop 0

let is_ascii_letter char =
  ('A' <= char && char <= 'Z') || ('a' <= char && char <= 'z')

let is_ascii_digit char = '0' <= char && char <= '9'

let is_component_start char = is_ascii_letter char || char = '_'

let is_component_continue char =
  is_ascii_letter char || is_ascii_digit char || char = '_' || char = '\''

let is_component component =
  String.length component > 0
  && is_component_start component.[0]
  &&
  let rec loop index =
    if index >= String.length component then true
    else if is_component_continue component.[index] then loop (index + 1)
    else false
  in
  loop 1

let of_components components =
  if
    components = []
    || List.exists
         (fun component -> component = "" || contains_dot component || not (is_component component))
         components
  then None
  else Some components

let to_string name = String.concat "." name

let components name = name

let equal left right = left = right
