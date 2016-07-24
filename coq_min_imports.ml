open Std

let file = "Test.v"

let () =
  let c = Std.input_file file in
  print_endline c
