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
      make_tmp_dir ~root:root' ~max_retries:(r-1) ?prefix ?suffix dir_perm
    else
      (* re-raise last exception *)
      raise (Unix_error (err, fun_name, arg))

(* Remove directory along with all it's contents recursively *)
(* hacky placeholder. Replace with proper implementation. Some samples:
https://ocaml.org/learn/tutorials/if_statements_loops_and_recursion.html#Recursion *)
let rmrf dirname =
  let res = system ("rm -rf " ^ dirname) in
  match res with
  | WEXITED e -> if e!=0 then ignore (Unix_error (EUNKNOWNERR e, "rmrf", dirname))
  | WSIGNALED e -> ignore (Unix_error (EINTR, "rmrf", dirname))
  | WSTOPPED e -> ignore (Unix_error (EINTR, "rmrf", dirname))


