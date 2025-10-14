let uuid_monotonic =
  let now_ms () = Int64.of_float (Unix.gettimeofday () *. 1000.) in
  Uuidm.v7_monotonic_gen ~now_ms (Random.State.make_self_init ())

let rec uuid () : Uuidm.t =
  match uuid_monotonic () with
  | None ->
      (* Too many UUIDs generated in a ms *)
      Unix.sleepf 1e-3;
      uuid ()
  | Some uuid -> uuid
