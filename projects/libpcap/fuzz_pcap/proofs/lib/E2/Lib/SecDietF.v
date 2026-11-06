(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module SzSecF.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 rec walkPf (t : constr) (k : int) (vs : constr list) (pend : constr list) : constr :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Prod b body =>
        if Int.equal k 0 then Constr.Unsafe.substnl pend 0 (Constr.Binder.type b)
        else (match vs with
              | v :: vs' => walkPf body (Int.sub k 1) vs' (v :: pend)
              | [] => SecDiet.SzSec.fail_msg "SzSecF: fewer Section variables than the pattern says"
              end)
    | _ =>
        (* [comment removed for export] *)
        let (t', _) := SecDiet.SzSec.walk (Constr.Unsafe.substnl pend 0 t) (String.make k (Char.of_int 118)) 0 vs [] in
        match Constr.Unsafe.kind (Std.eval_hnf t') with
        | Constr.Unsafe.Prod b _ => Constr.Binder.type b
        | _ => SecDiet.SzSec.fail_msg "SzSecF.ty: the statement has fewer binders than the pattern"
        end
    end.
  (* [comment removed for export] *)
  Ltac2 ty (stmt : constr) (k : int) : unit :=
    Control.enter (fun () =>
      let a := walkPf (Std.eval_hnf stmt) k (SecDiet.SzSec.last_hyps k) [] in
      Control.refine (fun () => a)).
  (* [comment removed for export] *)
  Ltac2 tyC (stmt : constr) (k : int) : unit :=
    Control.enter (fun () =>
      let a := walkPf (Std.eval_hnf stmt) k (SecDiet.SzSec.last_hyps k) [] in
      let (t, _) := SecDiet.SzSec.walk stmt (String.make k (Char.of_int 118)) 0 (SecDiet.SzSec.last_hyps k) [] in
      let b := match Constr.Unsafe.kind (Std.eval_hnf t) with
               | Constr.Unsafe.Prod bb _ => Constr.Binder.type bb
               | _ => SecDiet.SzSec.fail_msg "SzSecF.tyC: fewer binders" end in
      if Constr.equal a b then Control.refine (fun () => a)
      else SecDiet.SzSec.fail_msg "SzSecF.tyC: MISMATCH with SecDiet.SzSec.ty").
End SzSecF.
