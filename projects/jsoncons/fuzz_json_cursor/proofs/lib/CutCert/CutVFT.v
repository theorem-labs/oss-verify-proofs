(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore SegRun SegPlan.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutHeap CutAuto CutHeap2 CutHeapA CutOps CutOpsD CutAutoD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module CVFT.
Definition ret_tmpl_vfA (hd : CH.hdecl) (SC : list (Z * Z * Z)) (GLO GHI : Z) (SCRc : Z) (src : CC.cutpoint) (BL : CA.blocks) (nxsrc : nat) (ps : SR.post_spec)
  : option (CC.cutpoint * CA.blocks) :=
  let regs := CA.ps_reglist ps in
  let cells := SR.ps_cells ps in
  let nx := Nat.max nxsrc (CA.ps_bound ps) in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      let csp := snd (split_lit (nth 2 regs (ELit 0))) in
      Some (CC.CP ra (APC.sr_fresh regs APC.caller_saved nx) (List.filter (CHA.keepc_chk hd SC GLO GHI cells SCRc csp [] [] []) cells)
                  (nx + APC.NCS) (CC.cp_F src) [] (APC.esub (CC.cp_meas src) (ELit 1)), BL)
  | _ => None
  end.

Definition kept (hd : CH.hdecl) (SC : list (Z * Z * Z)) (GLO GHI SCRc csp : Z) (wregs : list SGP.region) (cells : list kentry) : list kentry :=
  List.filter (CHA.keepc_chk hd SC GLO GHI cells SCRc csp [] [] wregs) cells.

Definition ret_scxA (hd : CH.hdecl) (SC : list (Z * Z * Z)) (GLO GHI : Z) (F2 : list (expr * Z * expr)) (lmin : bool)
           (src : CC.cutpoint) (BL : CA.blocks) (nxsrc : nat) (ps : SR.post_spec) : option (CC.cutpoint * CA.blocks) :=
  let regs := CA.ps_reglist ps in
  let cells := SR.ps_cells ps in
  let nx := Nat.max nxsrc (CA.ps_bound ps) in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      let csp := snd (split_lit (nth 2 regs (ELit 0))) in
      let '(fb, fo) := split_lit (nth 10 regs (ELit 0)) in
      let wregs := [(fb, fo + 8, ELit 8)] in
      let regs1 := APC.sr_fresh regs APC.caller_saved (nx + 1) in
      let a0v := nth 10 regs1 (ELit 0) in
      let regs2 := if lmin then sr_upd regs1 10 (ELit 9223372036854775808) else regs1 in
      let news := KWord (SA fb (fo + 8)) 8 (EVar nx) :: (if lmin then [] else [KRange (DAS.nmin_of a0v) 0 0]) in
      Some (CC.CP ra regs2 (news ++ kept hd SC GLO GHI 80 csp wregs cells) (nx + 1 + APC.NCS) (if lmin then CC.cp_F src else F2) [] (APC.esub (CC.cp_meas src) (ELit 1)), BL)
  | _ => None
  end.

Definition ret_fsA (hd : CH.hdecl) (SC : list (Z * Z * Z)) (GLO GHI : Z) (WIN : Z)
           (src : CC.cutpoint) (BL : CA.blocks) (nxsrc : nat) (ps : SR.post_spec) : option (CC.cutpoint * CA.blocks) :=
  let regs := CA.ps_reglist ps in
  let cells := SR.ps_cells ps in
  let nx := Nat.max nxsrc (CA.ps_bound ps) in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      let csp := snd (split_lit (nth 2 regs (ELit 0))) in
      let '(fb, fo) := split_lit (nth 10 regs (ELit 0)) in
      let wregs := [(fb, fo + 8, ELit 8); (EVar 4, -164, ELit 4)] in
      let regs1 := APC.sr_fresh regs APC.caller_saved (nx + 1) in
      Some (CC.CP ra regs1 (KWord (SA fb (fo + 8)) 8 (EVar nx) :: kept hd SC GLO GHI WIN csp wregs cells) (nx + 1 + APC.NCS) (CC.cp_F src) [] (APC.esub (CC.cp_meas src) (ELit 1)), BL)
  | _ => None
  end.
End CVFT.
