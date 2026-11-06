(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutAutoD.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SAS.
Definition ret_fs (WIN ERRNO : Z) (rpos' : expr) (src : CC.cutpoint) (BL : CAD.blocks) (nxsrc : nat) (ps : SR.post_spec) : option (CC.cutpoint * CAD.blocks) :=
  let regs := CAD.ps_reglist ps in
  let nx := Nat.max nxsrc (CAD.ps_bound ps) in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      let regs1 := APC.sr_fresh regs APC.caller_saved nx in
      let '(spb, spo) := split_lit (nth 2 regs (ELit 0)) in
      let '(fb, fo) := split_lit (nth 10 regs (ELit 0)) in
      let kn1 := APC.kn_havoc (APC.kn_havoc (APC.kn_havoc (SR.ps_cells ps) fb (fo + 8) (ELit 8)) spb (spo - WIN) (ELit WIN)) (ELit 0) ERRNO (ELit 4) in
      let kn := KWord (SA fb (fo + 8)) 8 rpos' :: KUnk (SA spb (spo - WIN)) (ELit WIN) :: kn1 in
      Some (CC.CP ra regs1 kn (nx + APC.NCS) (CC.cp_F src) [] (APC.esub (CC.cp_meas src) (ELit 1)), BL)
  | _ => None
  end.
End SAS.
