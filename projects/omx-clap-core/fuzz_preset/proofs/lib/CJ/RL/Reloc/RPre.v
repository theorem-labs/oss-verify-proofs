(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Stdlib Require Import ZArith Zify Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import LiaTuning Ceil.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac2 rec rl_sec_prefix (hs : (ident * constr option * constr) list) (acc : (ident * constr option * constr) list) :=
  match hs with
  | [] => acc
  | h :: tl => let (id, _, _) := h in if zt_is_local id then acc else rl_sec_prefix tl (h :: acc)
  end.

(* [comment removed for export] *)
Ltac2 rl_keep_refs () : Std.reference list :=
  [reference:(RelSym); reference:(ZFact); reference:(CodeAtT); reference:(CodeAt); reference:(RelCode); reference:(RelNear);
   reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt); reference:(not); reference:(iff)].
Ltac2 rl_is_kept (c : constant) (l : Std.reference list) : bool :=
  List.exist (fun r => match r with Std.ConstRef c2 => Constant.equal c c2 | _ => false end) l.

Ltac2 rl_pre () : unit :=
  let keep := rl_keep_refs () in
  let hs := rl_sec_prefix (Control.hyps ()) [] in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => let hd := match Constr.Unsafe.kind ty with Constr.Unsafe.App f _ => f | _ => ty end in
                match Constr.Unsafe.kind hd with
                | Constr.Unsafe.Constant c _ => if rl_is_kept c keep then None else if zt_is_prop ty then Some id else None
                | _ => None
                end
      end) hs in
  match ids with [] => () | _ :: _ => match Control.case (fun () => Std.clear ids) with Val _ => () | Err _ => () end end.
Ltac rl_pre := ltac2:(Control.enter rl_pre).

(* [comment removed for export] *)
Ltac rl_zify_pre_hook := rl_pre; nat_diet; ceil_saturate.
