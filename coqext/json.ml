open Json_type;;

let obj = Object [ "x", Int 1;
                   "y", Int 2 ];;
let meh = Json_io.string_of_json obj;;

Printf.printf "%s\n" meh ;;




