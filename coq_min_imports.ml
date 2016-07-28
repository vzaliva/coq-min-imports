open Std
open Str
open BatArray
       
(* TODO: match mutliline import statements *)
let import_regexp = Str.regexp "^[ \t]*Require[ \t]+Import[ \t]+\\(.+\\)\\.[\t ]*"

let verbose = ref false
                               
let parse_cmd_line () =
  verbose := exists (String.equal "-cmi-verbose") Sys.argv;
  let fname_regexp = regexp "[A-Za-z_][A-Za-z_']+\\.v" in (* TODO: unicode *)
  let newargs = filter (fun x -> not (BatString.starts_with x "-cmi-") && not (string_match fname_regexp x 0)) Sys.argv in 
  (newargs, filter (fun x -> string_match fname_regexp x 0) Sys.argv)

let rec process_imports s p =
  try
    let x = search_backward import_regexp s p in
    let is = (matched_group 1 s) in
    let isb = group_beginning 1 in
    let ise = group_end 1 in
    let il = Str.split (regexp "[ \t]+") is in
    Printf.printf "\t%d: %s (%d)\n" x is (List.length il);
    if x=0 then s
    else process_imports s (x-1)
  with
    Not_found -> s
      
let process_file fname =
  if !verbose then Printf.printf "Processing %s" fname;
  let s = input_file fname in
  ignore (process_imports s (String.length s))
                               
let () =
  let (args,files) = parse_cmd_line () in
  ignore (map process_file files)
  
                
