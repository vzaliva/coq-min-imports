open Std
open Str
open BatList
open BatFile
open BatIO

open Dirtools

(* TODO: match mutliline import statements *)
let import_regexp = Str.regexp "^[ \t]*Require[ \t]+Import[ \t]+\\(.+\\)\\.[\t ]*"

let verbose = ref false
let replace = ref false
let debug = ref false

let nilstrlst:(string list) = []
let coqargs = ref nilstrlst
let coqcmd = ref "coqc"

let parse_cmd_line () =
  let open BatArray in
  let flags = [(verbose,"-cmi-verbose") ; (replace, "-cmi-replace") ; (debug,"-cmi-debug") ] in
  ignore (List.map (fun (r,n) -> r:= exists (String.equal n) Sys.argv) flags);
  let fname_regexp = regexp "[A-Za-z_][A-Za-z_']+\\.v" in (* TODO: unicode *)
  let newargs = filter (fun x -> not (BatString.starts_with x "-cmi-") && not (string_match fname_regexp x 0)) Sys.argv in
  (newargs, filter (fun x -> string_match fname_regexp x 0) Sys.argv)

let try_compile s =
  let d = make_tmp_dir 0o755 ~prefix:"coq_min_imports" ~suffix:".tmpdir" in
  let (out, name) = open_temporary_out ~mode:[`create] ~suffix:".v" ~temp_dir:d () in
  write_line out s;
  close_out out;
  (* TODO: use fork/execve to make sure arguments are properly passed *)
  let cmd = (!coqcmd) ^ " " ^ (String.concat " " !coqargs) ^ " " ^ name ^ " > /dev/null 2>&1" in
  if !debug then Printf.printf "Executing: %s\n" cmd;
  let res = BatSys.command cmd in
  rmrf d ;
  (res == 0)

let gen_import lst =
  (if is_empty lst then "" else
     "Require Import " ^ (String.concat " " lst) ^ ".\n")

let rec process_require pre post lst res =
  match lst with
  | [] -> res
  | x::xs ->
     let nl = ((rev xs)@res) in
     let body = pre ^ (gen_import nl) ^ post in
     if !debug then Printf.printf "\n==================\n %s \n==================\n" body;
     process_require pre post xs
                     (if try_compile body then
                        (if !verbose then Printf.printf "\t-%s\n" x;
                         res)
                      else
                        (if !verbose then Printf.printf "\t+%s\n" x;
                         (cons x res))
                     )

let rec process_imports s p saved =
  if p<0 then
    (s,saved)
  else
    try
      let x = search_backward import_regexp s p in
      let is = (matched_group 1 s) in
      let me = match_end () in
      let il = Str.split (regexp "[ \t]+") is in
      let pre = (string_before s x) in
      let post = (string_after s me) in
      let il' = process_require pre post (rev il) [] in
      let saved' = length il - length il' in
      let s' = if saved > 0 then s else pre ^ gen_import il' ^ post in
      process_imports s' (x-1) (saved+saved')
    with
      Not_found -> (s, saved)

let process_file fname =
  if !verbose then Printf.printf "Processing %s\n" fname;
  let s = input_file fname in
  let (s',saved) = process_imports s (String.length s) 0 in
  if saved>0 then
    let dumpf fn txt =
      let out = open_out ~mode:[`create ; `trunc] fn in
      write_line out txt;
      close_out out in
    if !replace then
      let backup_fname = fname ^ ".bak" in
      (if !verbose then Printf.printf "Removing %d imports from %s (saving %s)\n" saved fname backup_fname) ; Sys.rename fname backup_fname ; dumpf fname s'
    else
      let new_fname = fname ^ ".new" in
      (if !verbose then Printf.printf "Writing modified copy of %s as %s with %d imports removed\n" fname new_fname saved) ; dumpf new_fname s'
  else
    (if !verbose then Printf.printf "Nothing to remove in %s\n" fname)

let () =
  let (args,files) = parse_cmd_line () in
  if Array.length files = 0 then
    (Printf.printf "Usage: coq_min_imports <coq_flags> <files...>\n" ; exit 1)
  else
    (coqargs := tl (Array.to_list args); ignore (BatArray.map process_file files))
