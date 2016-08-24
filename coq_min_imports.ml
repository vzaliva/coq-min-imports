open Std
open Str
open BatList
       
(* TODO: match mutliline import statements *)
let import_regexp = Str.regexp "^[ \t]*Require[ \t]+Import[ \t]+\\(.+\\)\\.[\t ]*"

let verbose = ref false
let debug = ref false
let nilstrlst:(string list) = []
let coqargs = ref nilstrlst
let coqcmd = ref "coqc"
                               
let parse_cmd_line () =
  let open BatArray in
  verbose := exists (String.equal "-cmi-verbose") Sys.argv;
  let fname_regexp = regexp "[A-Za-z_][A-Za-z_']+\\.v" in (* TODO: unicode *)
  let newargs = filter (fun x -> not (BatString.starts_with x "-cmi-") && not (string_match fname_regexp x 0)) Sys.argv in 
  (newargs, filter (fun x -> string_match fname_regexp x 0) Sys.argv)

let try_compile s =
  let open BatFile in
  let open BatIO in
  let (out, name) = open_temporary_out ~mode:[`delete_on_exit ; `create] ~suffix:".v" () in
  write_line out s;
  close_out out;
  (* TODO: use fork/execve to make sure arguments are properly passed *)
  let cmd = (!coqcmd) ^ " " ^ (String.concat " " !coqargs) ^ " " ^ name ^ " > /dev/null 2>&1" in
  if !verbose then Printf.printf "Executing: %s\n" cmd;
  let res = BatSys.command cmd in
  (* TODO: Remove generated files *)
  res == 0

let rec process_require pre post lst res =
  match lst with
  | [] -> res
  | x::xs ->
     Printf.printf "*** Trying to remove %s\n" x;
     let nl = ((rev xs)@res) in
     let body = pre ^
                  (if is_empty nl then "" else
                     "Require Import " ^ (String.concat " " nl) ^ ".\n")
                  ^ post in
     if !debug then Printf.printf "\n==================\n %s \n==================\n" body;
     process_require pre post xs
                     (if try_compile body then
                        (if !verbose then Printf.printf "Removing: %s\n" x;
                        res)
                      else
                        (if !verbose then Printf.printf "Not removing: %s\n" x;
                        (cons x res))
                     )
  
let rec process_imports s p =
  try
    let x = search_backward import_regexp s p in
    let is = (matched_group 1 s) in
    let me = match_end () in
    let il = Str.split (regexp "[ \t]+") is in
    Printf.printf "\t%d: %s (%d)\n" x is (List.length il);
    let _ = process_require
              (string_before s x)
              (string_after s me)
              (rev il)
              []
    in
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
  coqargs := tl (Array.to_list args);
  ignore (BatArray.map process_file files)
  
                
