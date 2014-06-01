open Websocket
(* open Util *)

module YS = Yojson.Safe
module F = Format
module S = String

let (>>=) = Lwt.bind

let ps_file = ref ""
let disallow_save = ref false
let server_name = ref "localhost"

(* ----------------------------------------------------------------------- *)
(** {Handlers for different commands} *)

let process_unknown s =
  F.printf "unknown command: %s\n%!" s;
  Lwt.return (Frame.of_string "Unknown command")

let process_eval mode scmds =
  let return_msg s =
    let res = `Assoc [("cmd", `String "setGoal"); ("arg", `String s)] in
    Lwt.return (Frame.of_string (YS.to_string res))
  in
  let _ = F.flush_str_formatter () in
  let fmt = F.str_formatter in
  match mode with
  | "nonparam" ->
    let open NonParamAnalyze in
    begin try
      let res = analyze_from_string scmds in
      F.fprintf fmt "%a\n" pp_result_info res;
      F.fprintf fmt "%a\n" pp_result res;
      let s = F.flush_str_formatter () in
      return_msg s
    with
      NonParamInput.InvalidAssumption err ->
        F.fprintf fmt "Invalid assumption: %s\n" err;
      let s = F.flush_str_formatter () in
      return_msg s
    end
  | "param" ->
      let open Z3_Solver in
      begin try
        let res = ParamAnalyze.analyze_from_string F.err_formatter scmds in
        F.fprintf fmt "%a\n" pp_result res;
        let s = F.flush_str_formatter () in
        return_msg s
      with
        ParamInput.InvalidAssumption err ->
          F.fprintf fmt "Invalid assumption: %s\n" err;
          let s = F.flush_str_formatter () in
          return_msg s
      end
    | "interactive" ->
      let open InteractiveAnalyze in
      begin try
        let res = analyze_unbounded_from_string scmds in
        F.fprintf fmt "%a\n" Z3_Solver.pp_result res;
        let s = F.flush_str_formatter () in
        return_msg s
      with
        InteractiveInput.InvalidAssumption err ->
          F.fprintf fmt "Invalid assumption: %s\n" err;
          let s = F.flush_str_formatter () in
          return_msg s
      end
    | s when S.sub s 0 (S.length "interactive_") = "interactive_" ->
      let pref = "interactive_" in
      let remainder = S.sub s (S.length pref) (S.length s - S.length pref) in
      let bound = try int_of_string remainder with Failure _ -> 3 in
      let open InteractiveAnalyze in
      begin try
        F.printf "bound set to %i\n" bound;
        let res = analyze_bounded_from_string scmds bound in
        F.fprintf fmt "%a\n" Z3_Solver.pp_result res;
        let s = F.flush_str_formatter () in
        return_msg s
      with
        InteractiveInput.InvalidAssumption err ->
          F.fprintf fmt "Invalid assumption: %s\n" err;
        let s = F.flush_str_formatter () in
        return_msg s
      end
  | _ -> 
    return_msg "unknown mode"


(* ----------------------------------------------------------------------- *)
(** {Frame processing and server setup} *)

let process_frame frame =
  let inp = Frame.content frame in
  F.printf "Command: ``%s''\n%!" inp;
  match YS.from_string inp with
  | `Assoc l ->
     (try
        (let get k = List.assoc k l in
         match get "cmd" with
         | `String "eval" ->
           begin match get "mode", get "cmds" with
           | `String mode, `String cmds ->
             begin try
               process_eval mode cmds
             with
               _ ->
                 let res = `Assoc [("cmd", `String "setGoal"); ("arg", `String "Unknown error")] in
                 Lwt.return (Frame.of_string (YS.to_string res))
             end
           | _ -> process_unknown inp
           end
         | _              -> process_unknown inp)
      with Not_found -> process_unknown inp)
  | _ -> process_unknown inp

let run_server node service =
  let rec zoocrypt_serve uri (stream, push) =
    Lwt_stream.next stream >>= fun frame ->
    process_frame frame >>= fun frame' ->
    Lwt.wrap (fun () -> push (Some frame')) >>= fun () ->
    zoocrypt_serve uri (stream, push)
  in
  Lwt_io_ext.sockaddr_of_dns node service >>= fun sa ->
  Lwt.return (establish_server sa zoocrypt_serve)

let rec wait_forever () =
  Lwt_unix.sleep 1000.0 >>= wait_forever

(* ----------------------------------------------------------------------- *)
(** {Argument handling} *)

let main =
  let speclist =
    Arg.align
      [ ("-nosave", Arg.Set disallow_save, " disallow to save file");
        ("-s", Arg.Set_string server_name, " bind to this servername (default: localhost)")]
  in
  let usage_msg = "Usage: " ^ Sys.argv.(0) in
  let parse_args s = if !ps_file = "" then ps_file := s else failwith "can only serve one file" in
  Arg.parse speclist parse_args usage_msg;

  (* start server *)
  print_endline "Open the following URL in your browser (websocket support required):\n";
  print_endline ("    file://"^Sys.getcwd ()^"/web/index.html\n\n");
  Lwt_main.run (run_server !server_name "9998" >>= fun _ -> wait_forever ())
