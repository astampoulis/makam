let error loc s =
  Printf.printf "\n!! Error in %s:\n   %s\n\n%!" (UChannel.string_of_span loc) s
;;

let info_header loc type_s =
  Printf.printf "\n-- %s in %s:\n" type_s (UChannel.string_of_span loc)
;;

let info loc type_s s =
  if s = "" then
    (Printf.printf "\n-- %s in %s.\n\n%!" type_s (UChannel.string_of_span loc))
  else
    (Printf.printf "\n-- %s in %s:\n%s\n\n%!" type_s (UChannel.string_of_span loc) s)
;;
