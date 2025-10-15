open Vernacexpr
open Lens

let proof_end_admitted_lens =
  {
    get_opt = (function Admitted -> Some Admitted | _ -> None);
    set_opt = (fun _ -> function Admitted -> Some Admitted | _ -> None);
  }

let proof_end_proved_lens =
  {
    get_opt = (function Proved (flag, name) -> Some (flag, name) | _ -> None);
    set_opt =
      (fun _ -> function Proved (f, n) -> Some (Proved (f, n)) | _ -> None);
  }
