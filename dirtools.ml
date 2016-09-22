(* Create temporary directory. Could raise Unix_error. *)
let rec make_tmp_dir ?root ?max_retries:(r=10) dir_perm prefix suffix  =
  let root_dir =  match root with
    | Some v -> v
    | None -> Filename.get_temp_dir_name ()
  in
  let open Unix in
  let d = Filename.temp_file ~temp_dir:root_dir prefix suffix in
  try
    unlink d; mkdir d dir_perm; d
  with
    Unix_error (err, fun_name, arg) ->
    if r>0 then
      make_tmp_dir ~root:root_dir dir_perm prefix suffix ~max_retries:(r-1)
    else
      (* re-raise last exception *)
      raise (Unix_error (err, fun_name, arg))

