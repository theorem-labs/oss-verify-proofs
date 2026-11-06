(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 417 of its 446 lines of code are new or changed and 367 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P10.v; 23 of its 84 lines of code are new or changed and 385 lines of the source are left out. *)
(* lib/A/Prog/Seg/P10F_on.v -- route (C): the region form of Seg/P10F.v's (not in this delivery) p10_evt_F, for the image-A glue stage
   seg_P10 (lib/A/ACtlG/P10.v).  Written by a Theorem Labs lane under a Theorem Labs lane's standing consent (12:55Z,
   relayed by a Theorem Labs lane) for beside-files <S>F_on.v; Seg/P10F.v (not in this delivery) itself is byte-identical.  rule 24: no function
   proved.

   SOURCE.  Seg/P10F.v (not in this delivery) at a Theorem Labs lane's fold a working branch 4bae33fdf54 (blob 77baaf12b29): the
   lemma p10_evt_F, its statement and its proof, with exactly two changes:
   - the callee premise HPUF : reac_ports_unknown_contract_F becomes HPUF_on : reac_ports_unknown_contract_F_on
     (lib/A/Prog/reac_ports_unknown_c.v 5c6c0bd6556 (the blob this tree had at release c5e779efe8c), a Theorem Labs lane d4f70537e6f; proved by a Theorem Labs lane's
     reac_ports_unknownF.reac_ports_unknown_F_holds_on, 4038362e590);
   - the premise `shadow_rw m` is DROPPED (and its intro HSW): the run reads and stores no shadow byte itself, and
     its one use was the callee's shadow premise, which reac_ports_unknown_contract_F_on drops (R = none: the
     callee's checks read the shadow of c through addressable m c 1 and the runtime cells).
   The post is unchanged (it states no shadow fact).  The corollary p10_evt_of_F and the pin p10_evt_of_F_verbatim
   stay in Seg/P10F.v (they state the old form). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs P1 P7 P8 P9 P10.
(* Last: StepF's step / if_true / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Section CallFOn.
(* The callee's footprint contract in its region form, in the position of P10F.v's Section Hypothesis HPUF. *)
Hypothesis HPUF_on : reac_ports_unknown_contract_F_on.

Lemma p10_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c lo : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) -> 0 < c < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 c)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_UNKNOWN_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    addressable m c 1 -> wr_at rsegs m c 1 ->
    (c + 1 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= c) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME, bv_unsigned sp); (c, c + 1)] x) ->
    ExecF.rng RNG (A + 280) 8 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME) REAC_PORTS_UNKNOWN_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG c 1 -> ExecF.rng RNG (shadow_addr c) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a2' a3' a4' a5' a6' a7' t0' t1' t2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c60) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       (Z_to_bv 64 c) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c60) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME, bv_unsigned sp); (c, c + 1)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' c [Z_to_bv 8 0])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c4c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c lo -> -> -> Hc H280 HST Hlo HAC Hadc Hwrc Hsep Hout R280 RFR RGOT RCELL Rc Rcsh.
  assert (HL280 : ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 c))).
  { pose proof (bytes_at_ov_read rsegs m (A + 280) (le8 (Z_to_bv 64 c)) 0 8 H280
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  (* v1.9: the walk takes the NEW-only `beq` where v1.8 fell through its `bne`. *)
  step. (* 81c4c beq a0,s2,81c54 (NEW-only; taken, a0 = s2 = -1; the NEW-only 81c50 j 82bf4 is not reached) *)
  if_true.
  step. (* 81c54 li a0,0 *)
  step. (* 81c58 ld a1,280(s1) *)
  step. (* 81c5c jal reac_ports_unknown *)
  pose proof HPUF_on as HP. unfold reac_ports_unknown_contract_F_on, REAC_PORTS_UNKNOWN in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (p := 0) (c := c) (lo := lo) (bs := repeat (Z_to_bv 8 0) 20).
    all: rewrite ?Hcu.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; exfalso; apply HH; reflexivity).
    - intros _. split; [exact Hwrc|]. split; [intros HH; exfalso; apply HH; reflexivity | exact Hsep].
    - intros _. exact Hadc.
    - rewrite (pu_W_eq (bv_unsigned sp) c ltac:(lia)). exact Hout.
    - intros _. split; [exact Rc | exact Rcsh]. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' & E & MU & WM & ST' & MIi & Hbyte).
  subst ms'.
  rewrite (pu_W_eq (bv_unsigned sp) c ltac:(lia)) in MU.
  rewrite pu_ok_p0 in Hbyte |- *. cbv iota in Hbyte |- *.
  replace (ret_pc (Z_to_bv 64 0x81c60)) with (Z_to_bv 64 0x81c60)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  do 9 eexists. exists m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact ST' | exact (Hbyte ltac:(lia))].
Qed.

End CallFOn.
