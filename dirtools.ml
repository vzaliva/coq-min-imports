open Unix

(* Create temporary directory and returns name. Could raise Unix_error. *)
let rec make_tmp_dir ?root ?max_retries:(r=10) ?prefix ?suffix dir_perm  =
  let open Option in
  let root' =  default (Filename.get_temp_dir_name ()) root
  and prefix' =  default "" prefix
  and suffix' =  default "" suffix in
  let d = Filename.temp_file ~temp_dir:root' prefix' suffix' in
  try
    unlink d; mkdir d dir_perm; d
  with
    Unix_error (err, fun_name, arg) ->
    if r>0 then
      make_tmp_dir ?root ~max_retries:(r-1) ?prefix ?suffix dir_perm
    else
      (* re-raise last exception *)
      raise (Unix_error (err, fun_name, arg))


(* Remove directory along with all it's contents recursively. Inspired by https://ocaml.org/learn/tutorials/if_statements_loops_and_recursion.html but we try to minimize the number of open file handes at price of keeping a queue of directories to be removed in memory.
 *)
let rec rmrf path =
  let readdir_no_ex dirh =
    try
      Some (readdir dirh)
    with
      End_of_file -> None
  in
  let dirh = opendir path in
  let rec scan () =
    let filename = readdir_no_ex dirh in
    match filename with
      None -> []
    | Some "." -> scan ()
    | Some ".." -> scan ()
    | Some filename ->
       let pathname = path ^ "/" ^ filename in
       let stat = lstat pathname in
       if stat.st_kind = S_DIR then
         pathname :: (scan ())
       else
         (unlink pathname ; scan ())
  in
  let subdirs = scan () in
  closedir dirh ;
  ignore (List.map rmrf subdirs) ;
  rmdir path

