let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let result = Ext_cli.run args in
  print_string result.stdout;
  prerr_string result.stderr;
  exit result.code
