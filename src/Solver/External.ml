let call_external script cmd linenum =
  let (c_in, c_out) = Unix.open_process "/usr/bin/python scripts/ggt_z3.py" in
  output_string c_out cmd;
  flush c_out;
  let rec loop o linenum =
    if linenum = 0 then o
    else (
      try
        let l = input_line c_in in
        loop (o @ [l]) (linenum - 1)
      with End_of_file ->
        ignore (Unix.close_process (c_in,c_out));
        o)
  in loop [] linenum
