open Std

let file = "Test.v"
(* TODO: match mutliline import statements *)
let import_regexp = Str.regexp "^[ \t]*Require[ \t]+Import[ \t]+\\(.+\\)\\.[\t ]*$"

let rec process_imports s p =
  let open Str in
  try
    let x = search_backward import_regexp s p in
    Printf.printf "\t%d: %s\n" x (matched_string s);
    if x=0 then s
    else process_imports s (x-1)
  with
    Not_found -> s
      
                               
let () =
  let s = Std.input_file file in
  ignore (process_imports s (String.length s))
                
