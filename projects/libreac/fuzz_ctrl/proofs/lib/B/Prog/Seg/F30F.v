(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 2169 of its 2293 lines of code are new or changed and 887 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F30.v; 72 of its 209 lines of code are new or changed and 2156 lines of the source are left out. *)
(* Footprint (ExecF.evtF) twins of the segment-F30 machine runs of lib/B/Prog/Seg/F30.v (fuzz_ctrl
   LLVMFuzzerTestOneInput, asan-ubsan image B). Bridge input for the cgif-form walk only.
   rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F30.v f30s_evt (:356), f30s_evt_ro (:585) at
     a working branch 3803efccea0 (blob d2349dd89bf7b15316e376f97e695d42605b62f1);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c),
         lib/B/MemNormF.v blob 99f8b314301ceb0f253f1a6c8165b488b23ce218 (taken by path from dba073859bd);
   compare: f30s_evt_of_F (evtF_evt + rng_all) re-derives F30.f30s_evt verbatim.
   f30s_evt already stops AT the entry 0x837c4 of reac_ctrl_classify_box_frame with ra = 0x82af8, so it IS the
   pre stretch of the segment's one call and needs no further split; the stretch after the return pc 0x82af8 is
   empty (0x82af8 is the next cut, segment F31's entry).
   F30.f30_cl_ro (:709) has NO twin here: it is not a stretch of this segment's own code but the
   reac_ctrl_classify_box_frame contract restated over ro_agree memory, i.e. a runtime/program callee contract,
   and route (a) gives one owner per callee contract (a Theorem Labs lane 22:28Z) with no `_F` stepping through a callee. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require BzBridge MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c bcmp_wrap_c memcmp_c
  reac_ctrl_parse_c reac_ctrl_classify_box_frame_c reac_ctrl_classify_box_frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F30.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* ---- The run 0x82abc -> the classify callee's entry 0x837c4 (F30.v:356-422), in footprint form. *)
Lemma f30s_evt_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S3 V O U PHI LEN : Z) (c56 c57 c58 c59 c60 c66 : byte) (vb : list byte) (RNG : footprint),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 S3 -> s2v = Z_to_bv 64 PHI -> s4v = Z_to_bv 64 LEN ->
    0 <= A /\ A + 272 <= 2 ^ 64 -> 0 <= S3 /\ S3 + 67 <= 2 ^ 64 -> 0 <= V /\ V + 4 <= 2 ^ 64 ->
    0 <= O < 2 ^ 64 -> 0 <= U < 2 ^ 64 -> 0 <= PHI < 2 ^ 64 -> 0 <= LEN < 2 ^ 64 ->
    (S3 + 67 <= V \/ V + 4 <= S3) -> (S3 + 67 <= A + 192 \/ A + 272 <= S3) ->
    (V + 4 <= A + 192 \/ A + 272 <= V) ->
    rw_cells rsegs m (S3 + 56) [C1 c56] -> rw_cells rsegs m (S3 + 57) [C1 c57] ->
    rw_cells rsegs m (S3 + 58) [C1 c58] -> rw_cells rsegs m (S3 + 59) [C1 c59] ->
    rw_cells rsegs m (S3 + 60) [C1 c60] -> rw_cells rsegs m (S3 + 66) [C1 c66] ->
    rw_cells rsegs m V [CB 4 vb] -> length vb = 4%nat ->
    ro_cells rsegs m (A + 192) [C8 (Z_to_bv 64 V)] ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 O)] ->
    ro_cells rsegs m (A + 264) [C8 (Z_to_bv 64 U)] ->
    mem_inv rsegs m ->
    rng RNG (S3 + 56) 5 -> rng RNG (S3 + 66) 1 ->
    rng RNG (A + 192) 8 -> rng RNG (A + 216) 8 -> rng RNG (A + 264) 8 -> rng RNG V 4 ->
    evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x82af8) sp gp tp t0 t1 t2 s0 s1v
                       (Z_to_bv 64 PHI) (Z_to_bv 64 LEN) (Z_to_bv 64 U) (Z_to_bv 64 O) (Z_to_bv 64 V)
                       a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x837c4) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 61); (S3 + 66, S3 + 67); (V, V + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         (exists vb', rw_cells rsegs m' V [CB 4 vb'] /\ length vb' = 4%nat) /\
         (exists b, mrd rsegs m' (wa (S3 + 56)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 57)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 58)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 59)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 60)) = Some b /\ bv_signed b = 4) /\
         (exists b, mrd rsegs m' (wa (S3 + 66)) = Some b /\ bv_signed b = 4))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S3 V O U PHI LEN c56 c57 c58 c59 c60 c66 vb RNG -> -> -> ->
    [HA0 HA1] [HS0 HS1] [HV0 HV1] HO HU HPHI HLEN Hd1 Hd2 Hd3
    H56 H57 H58 H59 H60 H66 HV Hvb H192 H216 H264 HMI
    R56 R66 R192 R216 R264 RV.
  pose proof (munch_refl [(S3 + 56, S3 + 61); (S3 + 66, S3 + 67); (V, V + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. try (rewrite f30_le1_byte). try mem_after_store.
  step. try (rewrite f30_le1_byte). try mem_after_store.
  step. try (rewrite f30_le1_byte). try mem_after_store.
  step. try (rewrite f30_le1_byte). try mem_after_store.
  step.
  step. try (rewrite f30_le1_byte). try mem_after_store.
  step. try (rewrite f30_le1_byte). try mem_after_store.
  step. step. step.
  step. step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  repeat match goal with
  | H : rw_cells rsegs ?mm ?a [C4 ?w] |- _ => apply f30_rw4 in H
  end.
  split.
  { match goal with H : rw_cells rsegs ?mm V [CB 4 ?bs] |- _ => exists bs; split; [exact H|] end.
    apply length_le4. }
  repeat match goal with
  | H : rw_cells rsegs ?mm ?a [C1 ?b] |- _ => apply f30_rw1 in H; apply f30_cell_byte in H
  end.
  repeat (split; [match goal with H : mrd rsegs _ (wa _) = Some _ |- _ =>
                    eexists; split; [exact H | vm_compute; reflexivity] end |]);
  match goal with H : mrd rsegs _ (wa _) = Some _ |- _ =>
    eexists; split; [exact H | vm_compute; reflexivity] end.
Qed.

Lemma f30s_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S3 V O U PHI LEN : Z) (c56 c57 c58 c59 c60 c66 : byte) (vb : list byte),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 S3 -> s2v = Z_to_bv 64 PHI -> s4v = Z_to_bv 64 LEN ->
    0 <= A /\ A + 272 <= 2 ^ 64 -> 0 <= S3 /\ S3 + 67 <= 2 ^ 64 -> 0 <= V /\ V + 4 <= 2 ^ 64 ->
    0 <= O < 2 ^ 64 -> 0 <= U < 2 ^ 64 -> 0 <= PHI < 2 ^ 64 -> 0 <= LEN < 2 ^ 64 ->
    (S3 + 67 <= V \/ V + 4 <= S3) -> (S3 + 67 <= A + 192 \/ A + 272 <= S3) ->
    (V + 4 <= A + 192 \/ A + 272 <= V) ->
    rw_cells rsegs m (S3 + 56) [C1 c56] -> rw_cells rsegs m (S3 + 57) [C1 c57] ->
    rw_cells rsegs m (S3 + 58) [C1 c58] -> rw_cells rsegs m (S3 + 59) [C1 c59] ->
    rw_cells rsegs m (S3 + 60) [C1 c60] -> rw_cells rsegs m (S3 + 66) [C1 c66] ->
    rw_cells rsegs m V [CB 4 vb] -> length vb = 4%nat ->
    ro_cells rsegs m (A + 192) [C8 (Z_to_bv 64 V)] ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 O)] ->
    ro_cells rsegs m (A + 264) [C8 (Z_to_bv 64 U)] ->
    mem_inv rsegs m ->
    LE.evt rsegs
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x82af8) sp gp tp t0 t1 t2 s0 s1v
                       (Z_to_bv 64 PHI) (Z_to_bv 64 LEN) (Z_to_bv 64 U) (Z_to_bv 64 O) (Z_to_bv 64 V)
                       a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x837c4) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 61); (S3 + 66, S3 + 67); (V, V + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         (exists vb', rw_cells rsegs m' V [CB 4 vb'] /\ length vb' = 4%nat) /\
         (exists b, mrd rsegs m' (wa (S3 + 56)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 57)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 58)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 59)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 60)) = Some b /\ bv_signed b = 4) /\
         (exists b, mrd rsegs m' (wa (S3 + 66)) = Some b /\ bv_signed b = 4))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S3 V O U PHI LEN c56 c57 c58 c59 c60 c66 vb E1 E3 E2 E4
    HA HS HV HO HU HPHI HLEN Hd1 Hd2 Hd3 H56 H57 H58 H59 H60 H66 HVc Hvb H192 H216 H264 HMI.
  destruct HA as (HA0 & HA1). destruct HS as (HS0 & HS1).
  apply (evtF_evt rsegs RNG_all).
  eapply f30s_evt_F; try eassumption; try (split; eassumption); apply rng_all; lia.
Qed.
Definition f30s_evt_src_check : ltac:(let T := type of F30.f30s_evt in exact T) := f30s_evt_of_F.

(* f30s_evt_ro in footprint form (F30.v:585-656): the run is taken on the normalized memory and
   MemNormF.evtF_normalize_ro carries it back to the cut's own memory. *)
Lemma f30s_evt_ro_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S3 V O U PHI LEN : Z) (c56 c57 c58 c59 c60 c66 : byte) (vb : list byte) (RNG : footprint),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 S3 -> s2v = Z_to_bv 64 PHI -> s4v = Z_to_bv 64 LEN ->
    0 <= A /\ A + 272 <= 2 ^ 64 -> 0 <= S3 /\ S3 + 67 <= 2 ^ 64 -> 0 <= V /\ V + 4 <= 2 ^ 64 ->
    0 <= O < 2 ^ 64 -> 0 <= U < 2 ^ 64 -> 0 <= PHI < 2 ^ 64 -> 0 <= LEN < 2 ^ 64 ->
    (S3 + 67 <= V \/ V + 4 <= S3) -> (S3 + 67 <= A + 192 \/ A + 272 <= S3) ->
    (V + 4 <= A + 192 \/ A + 272 <= V) ->
    rw_cells rsegs m (S3 + 56) [C1 c56] -> rw_cells rsegs m (S3 + 57) [C1 c57] ->
    rw_cells rsegs m (S3 + 58) [C1 c58] -> rw_cells rsegs m (S3 + 59) [C1 c59] ->
    rw_cells rsegs m (S3 + 60) [C1 c60] -> rw_cells rsegs m (S3 + 66) [C1 c66] ->
    rw_cells rsegs m V [CB 4 vb] -> length vb = 4%nat ->
    ro_cells rsegs m (A + 192) [C8 (Z_to_bv 64 V)] ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 O)] ->
    ro_cells rsegs m (A + 264) [C8 (Z_to_bv 64 U)] ->
    ro_agree rsegs m -> LOWMEM_END <= S3 -> AC.GT <= V ->
    rng RNG (S3 + 56) 5 -> rng RNG (S3 + 66) 1 ->
    rng RNG (A + 192) 8 -> rng RNG (A + 216) 8 -> rng RNG (A + 264) 8 -> rng RNG V 4 ->
    evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x82af8) sp gp tp t0 t1 t2 s0 s1v
                       (Z_to_bv 64 PHI) (Z_to_bv 64 LEN) (Z_to_bv 64 U) (Z_to_bv 64 O) (Z_to_bv 64 V)
                       a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x837c4) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 61); (S3 + 66, S3 + 67); (V, V + 4)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         (exists vb', rw_cells rsegs m' V [CB 4 vb'] /\ length vb' = 4%nat) /\
         (exists b, mrd rsegs m' (wa (S3 + 56)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 57)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 58)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 59)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 60)) = Some b /\ bv_signed b = 4) /\
         (exists b, mrd rsegs m' (wa (S3 + 66)) = Some b /\ bv_signed b = 4))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S3 V O U PHI LEN c56 c57 c58 c59 c60 c66 vb RNG E1 E3 E2 E4
    HA HS HV HO HU HPHI HLEN Hd1 Hd2 Hd3 H56 H57 H58 H59 H60 H66 HVc Hvb H192 H216 H264 HRO HS3 HVg
    R56 R66 R192 R216 R264 RV.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HS3g : AC.GT <= S3) by (unfold LOWMEM_END, AC.GT in *; lia).
  pose proof (f30s_evt_F ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 Fr fc (normalize rsegs m) A S3 V O U PHI LEN c56 c57 c58 c59 c60 c66 vb RNG E1 E3 E2 E4
    HA HS HV HO HU HPHI HLEN Hd1 Hd2 Hd3
    (f30_rwc_norm m _ _ HRO H56 ltac:(lia) ltac:(cbn; lia)) (f30_rwc_norm m _ _ HRO H57 ltac:(lia) ltac:(cbn; lia))
    (f30_rwc_norm m _ _ HRO H58 ltac:(lia) ltac:(cbn; lia)) (f30_rwc_norm m _ _ HRO H59 ltac:(lia) ltac:(cbn; lia))
    (f30_rwc_norm m _ _ HRO H60 ltac:(lia) ltac:(cbn; lia)) (f30_rwc_norm m _ _ HRO H66 ltac:(lia) ltac:(cbn; lia))
    (f30_rwc_norm m _ _ HRO HVc HVg ltac:(cbn; lia)) Hvb
    (f30_roc_norm m _ _ HRO H192) (f30_roc_norm m _ _ HRO H216) (f30_roc_norm m _ _ HRO H264)
    (mem_inv_normalize rsegs m) R56 R66 R192 R216 R264 RV) as HC.
  pose proof (MemNormF.evtF_normalize_ro RNG _ _ _ _ _ _ m (seg_rom rsegs) HRO HC) as HN.
  eapply evtF_mono; [exact HN|].
  intros ms (s0' & (m0' & E & MU & WM & MI' & (vb' & Hv' & Hvl') & B56 & B57 & B58 & B59 & B60 & B66) &
             Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists memX. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exists vb'; split; [exact (f30_rwc_back memX m0' _ _ Hmr Hv') | exact Hvl']|].
  repeat match goal with
  | H : exists b, mrd rsegs m0' ?a = Some b /\ _ |- _ =>
      let b := fresh "b" in let Hb := fresh "Hb" in let Hs := fresh "Hs" in
      destruct H as (b & Hb & Hs); rewrite <- (mrd_rel rsegs memX m0' a Hmr) in Hb
  end.
  repeat (split; [eexists; split; eassumption|]).
  eexists; split; eassumption.
Qed.
