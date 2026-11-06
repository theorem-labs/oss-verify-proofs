(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CAX.
Record xsum : Type := XSUM {
  xs_pc : Z;                                             (* [comment removed for export] *)
  xs_scr : Z;                                            (* [comment removed for export] *)
  xs_ng : nat;                                           (* [comment removed for export] *)
  xs_a0 : list expr -> nat -> option expr;               (* [comment removed for export] *)
  xs_wregs : list expr -> list SGP.region;               (* [comment removed for export] *)
  xs_keep : list expr -> CA.blocks -> CA.blocks;         (* [comment removed for export] *)
  xs_new : list expr -> list kentry -> nat -> CA.blocks -> list kentry * CA.blocks;
                                                         (* [comment removed for export] *)
  xs_F : list SGP.region -> list SGP.region              (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition xs_cs (x : xsum) : CA.callsum :=
  CA.CSUM (xs_pc x) (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None (xs_scr x) false false.

Definition kept_of (hd : CH.hdecl) (x : xsum) (regs : list expr) (cells : list kentry) (csp : Z) (BLk : CA.blocks) : list kentry :=
  List.filter (CH2.keepc_chk hd cells (xs_scr x) csp BLk (xs_wregs x regs)) cells.

Definition ret_tmpl_x (hd : CH.hdecl) (x : xsum) (src : CC.cutpoint) (BL : CA.blocks) (nxsrc : nat) (ps : SR.post_spec) : option (CC.cutpoint * CA.blocks) :=
  let regs := CA.ps_reglist ps in
  let cells := SR.ps_cells ps in
  let nx := Nat.max nxsrc (CA.ps_bound ps) in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      let csp := snd (split_lit (nth 2 regs (ELit 0))) in
      let ng := xs_ng x in
      let regs1 := APC.sr_fresh regs APC.caller_saved (nx + ng) in
      let regs2 := match xs_a0 x regs nx with Some e => sr_upd regs1 10 e | None => regs1 end in
      let BLk := xs_keep x regs BL in
      let '(news, BL') := xs_new x regs cells nx BLk in
      Some (CC.CP ra regs2 (news ++ kept_of hd x regs cells csp BLk) (nx + ng + APC.NCS) (xs_F x (CC.cp_F src)) [] (APC.esub (CC.cp_meas src) (ELit 1)), BL')
  | _ => None
  end.

(* [comment removed for export] *)
Definition cell_at (cells : list kentry) (b : expr) (k : Z) (w : nat) : option expr :=
  match List.find (fun X => match X with KWord (SA b' k') w' _ => (expr_eqb b b' && Z.eqb k k' && Nat.eqb w w')%bool | _ => false end) cells with
  | Some (KWord _ _ v) => Some v
  | _ => None
  end.
End CAX.
