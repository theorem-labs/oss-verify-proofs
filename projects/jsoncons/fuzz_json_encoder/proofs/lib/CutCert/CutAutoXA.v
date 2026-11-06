(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CAXA.
Record xsumA : Type := XSA {
  xa_x : CAX.xsum;                                       (* [comment removed for export] *)
  xa_frames : list expr -> list (expr * Z * Z)           (* [comment removed for export] *)
}.
Definition xs_cs (x : xsumA) : CA.callsum := CAX.xs_cs (xa_x x).

Definition kept_of (hd : CH.hdecl) (SC : list (Z * Z * Z)) (GLO GHI : Z) (x : xsumA) (regs : list expr) (cells : list kentry) (csp : Z) (BLk : CA.blocks) : list kentry :=
  List.filter (CHA.keepc_chk hd SC GLO GHI cells (CAX.xs_scr (xa_x x)) csp BLk (xa_frames x regs) (CAX.xs_wregs (xa_x x) regs)) cells.

Definition ret_tmpl_xa (hd : CH.hdecl) (SC : list (Z * Z * Z)) (GLO GHI : Z) (xa : xsumA) (src : CC.cutpoint) (BL : CA.blocks) (nxsrc : nat) (ps : SR.post_spec)
  : option (CC.cutpoint * CA.blocks) :=
  let x := xa_x xa in
  let regs := CA.ps_reglist ps in
  let cells := SR.ps_cells ps in
  let nx := Nat.max nxsrc (CA.ps_bound ps) in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      let csp := snd (split_lit (nth 2 regs (ELit 0))) in
      let ng := CAX.xs_ng x in
      let regs1 := APC.sr_fresh regs APC.caller_saved (nx + ng) in
      let regs2 := match CAX.xs_a0 x regs nx with Some e => sr_upd regs1 10 e | None => regs1 end in
      let BLk := CAX.xs_keep x regs BL in
      let '(news, BL') := CAX.xs_new x regs cells nx BLk in
      Some (CC.CP ra regs2 (news ++ kept_of hd SC GLO GHI xa regs cells csp BLk) (nx + ng + APC.NCS) (CAX.xs_F x (CC.cp_F src)) [] (APC.esub (CC.cp_meas src) (ELit 1)), BL')
  | _ => None
  end.
End CAXA.
