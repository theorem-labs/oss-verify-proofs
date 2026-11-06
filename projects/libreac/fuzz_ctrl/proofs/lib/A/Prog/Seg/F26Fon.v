(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names changed; 256 of its 289 lines of code are new or changed and 363 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F26.v; 35 of its 92 lines of code are new or changed and 232 lines of the source are left out. *)
(* lib/A/Prog/Seg/F26Fon.v -- route (C) twin of f26_evt_F of lib/A/Prog/Seg/F26F.v (not in this delivery; BASE below) (a Theorem Labs lane 12:52Z twin rule: an ADDITIVE
   beside-file; lib/A/Prog/Seg/F26F.v (not in this delivery) stays byte-identical).  Writer: a Theorem Labs lane, for glue stage seg_F26.
   proves no function (kind: segment lemma).

   BASE: Seg/F26F.v (not in this delivery) at a Theorem Labs lane's fold a working branch 4bae33fdf54 (blob 720d2b24318), not the
   blob d3bc29f291a of a working branch: the two differ only in the fold's full qualification of the MState lemmas
   (A.Tk.UL.MState.unsigned_lit / ret_pc_fold / ret_pc_even), which this file keeps.

   THE CHANGE, and only it: f26_evt_F's premise `shadow_rw m` is REMOVED, and its callee premise
   reac_ports_unknown_contract_F becomes reac_ports_unknown_contract_F_on (LANDED.md (a working note, not in this delivery): a Theorem Labs lane
   d4f70537e6f, proof a Theorem Labs lane 4038362e590 reac_ports_unknown_F_holds_on).  Why removed, not narrowed: the run
   0x825f4 -> 0x82604 is two register moves and the call; it reads and stores no shadow byte itself, and its only
   use of `shadow_rw m` in f26_evt_F was to feed the callee's premise, which the _on contract drops (the callee reads
   its shadow bytes from `addressable` and the runtime cells).  The post is unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts F24 F26.
(* Last: StepF's step / if_false / finish (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr, as F26.v does. *)
Import YK11.
Local Open Scope Z_scope.

Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.

(* ---- f26_evt_F with no shadow premise, on the callee's route (C) contract. ---- *)
Lemma f26_evt_F_on :
  forall (RNG : ExecF.footprint),
    reac_ports_unknown_contract_F_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi uk lo : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 (phi + 18) -> a0 = Z_to_bv 64 uk ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    stk rsegs m lo spv -> lo + 16 <= spv ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    (phi + 38 <= spv - 16 \/ spv <= phi + 18) ->
    asan_cells m -> addressable m (phi + 18) 20 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(spv - 16, spv)] x) ->
    ExecF.rng RNG (spv - 16) 16 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (phi + 18) 20 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 18 + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if RP.pu_decl bs then 4 * RP.pu_nunk bs 12 else -1))
                       (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 uk) s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x82604) fc None m' (seg_rom rsegs) /\
         munch [(spv - 16, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825f4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG PU ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m spv phi uk lo bs -> -> -> Hphi1 Hphi2 Hspv Hstk Hlo Hlen Hbs Hdjp HAC HADp HOUT
    RFR RGOT RCK RP20 RSH.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  step. step. step. step.
  eapply ExecF.evtF_cut.
  { eapply PU with (p := phi + 18) (c := 0) (bs := bs) (lo := lo) (RNG := RNG).
    - first [rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
      lia | reflexivity].
    - first [rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
      lia | reflexivity].
    - rewrite Hspu. exact Hstk.
    - rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros _. split; [lia|]. split; [exact Hlen|]. split; [exact Hbs|].
      rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros HC. exfalso. apply HC. reflexivity.
    - exact HAC.
    - intros HC. exfalso. apply HC. reflexivity.
    - intros _. exact HADp.
    - intros x Hx. unfold reac_ports_unknown_W. rewrite Hspu. cbn [Z.eqb app].
      unfold REAC_PORTS_UNKNOWN_FRAME. exact (HOUT x Hx).
    - rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. exact RFR.
    - exact RGOT.
    - exact RCK.
    - intros _. split; [exact RP20 | exact RSH].
    - intros HC. exfalso. apply HC. reflexivity. }
  intros ms' PO. unfold reac_ports_unknown_post in PO.
  destruct PO as (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' & -> & MUc & WMc & STc & _ & _).
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ ?pcx _ _ _ _) =>
      replace pcx with (Z_to_bv 64 0x82604)
        by (symmetry; first [ rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_fold;
          apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_even; lia
                            | apply bv_eq; vm_compute; reflexivity
                            | vm_compute; reflexivity ])
  end.
  assert (Eok : RP.pu_ok (phi + 18) bs = RP.pu_decl bs) by (apply b7_pu_ok; lia).
  rewrite Eok.
  apply ExecF.evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
  split; [|exact WMc].
  unfold reac_ports_unknown_W in MUc. rewrite Hspu in MUc. cbn [Z.eqb app] in MUc.
  unfold REAC_PORTS_UNKNOWN_FRAME in MUc. exact MUc.
Qed.
