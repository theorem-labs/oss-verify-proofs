(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 1535 of its 1667 lines of code are new or changed and 879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F32.v, with its module paths and module names changed; 259 of its 503 lines of code are new or changed and 1423 lines of the source are left out. *)
(* Footprint (ExecF.evtF) twins of the segment-F32 machine runs of lib/B/Prog/Seg/F32.v (fuzz_ctrl
   LLVMFuzzerTestOneInput, asan-ubsan image B). Bridge input for the cgif-form walk only.
   rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F32.v f32e_evt (:326), f32n_evt (:364), f32m1_evt (:382), f32m2_evt (:419),
     f32c_evt (:506) at a working branch 3803efccea0
     (blob 8aab0c37ec89d36b19fc634c9d3d4d1fba56b8fa);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f32e_evt_of_F, f32n_evt_of_F, f32m1_evt_of_F, f32m2_evt_of_F (evtF_evt + rng_all) re-derive the
     source statements verbatim. f32c_evt calls reac_box_catalogue (jal at 0x82bc8), so it is split:
     f32c_evt_pre_F re-runs F32.v:558-646 (0x82b5c up to the callee entry, ra = 0x82bcc) and f32c_evt_post_F
     re-runs F32.v:667-734 (from the return pc 0x82bcc to the exit cut 0x82bcc, no step). No callee contract is
     stated here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib RcModel RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F32.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.ShadowRwOnT B.Prog.MemMono.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* The shadow byte of an application address is inside the footprint bounds. *)
Lemma f32F_sh_rng : forall x, 0 <= x -> x < APPMEM_END ->
  0 <= Z.shiftr x 3 + ASAN_K /\ Z.shiftr x 3 + ASAN_K + 1 <= 2 ^ 64.
Proof.
  intros x H0 H1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold ASAN_K, APPMEM_END in *. split; Z.div_mod_to_equations; lia.
Qed.

(* ===================== 0x82b38 -> 0x82b5c: the event-word checks ===================== *)

(* F32.v:326-361. Reads the spills [A+184] and [A+192] and the 4 bytes of the event word; writes nothing. *)
Lemma f32e_evt_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (A tf sm E e : Z) (RNG : footprint),
    s1 = Z_to_bv 64 A -> s9 = Z_to_bv 64 sm -> bv_eqb a0 (Z_to_bv 64 0) = false ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= E -> E + 4 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 tf)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 E)) ->
    bytes_at rsegs m E (le4 (Z_to_bv 64 e)) ->
    (tf = 0 \/ tf = 1) -> (sm = 0 \/ sm = 1) -> (tf = 1 \/ sm = 1) -> 0 <= e <= 5 ->
    rng RNG (A + 184) 8 -> rng RNG (A + 192) 8 -> rng RNG E 4 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 5) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b38) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m A tf sm E e RNG -> -> H0 HA0 HA1 HE0 HE1 H184 H192 HEv Htf Hsm Hor He R184 R192 RE.
  pose proof (f32_rd8 m (A + 184) (Z_to_bv 64 tf) H184) as R184'.
  pose proof (f32_rd8 m (A + 192) (Z_to_bv 64 E) H192) as R192'.
  pose proof (f32_rd4 m E (Z_to_bv 64 e) HEv) as RE'.
  destruct Htf as [Etf|Etf]; destruct Hsm as [Esm|Esm]; subst tf; subst sm;
    try (exfalso; destruct Hor as [Hc|Hc]; discriminate Hc).
  all: step; rewrite H0; cbv iota;
       step; step; step;
       step; if_false;
       step; step;
       rewrite (RcClassifyLib.cl_sx32 e) by lia;
       step; step;
       rewrite (f32_ltu_lit 5 e) by lia; if_false;
       apply evtF_done; reflexivity.
Qed.

Lemma f32e_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (A tf sm E e : Z),
    s1 = Z_to_bv 64 A -> s9 = Z_to_bv 64 sm -> bv_eqb a0 (Z_to_bv 64 0) = false ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= E -> E + 4 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 tf)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 E)) ->
    bytes_at rsegs m E (le4 (Z_to_bv 64 e)) ->
    (tf = 0 \/ tf = 1) -> (sm = 0 \/ sm = 1) -> (tf = 1 \/ sm = 1) -> 0 <= e <= 5 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 5) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b38) fcr None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). eapply f32e_evt_F; try eassumption; apply rng_all; lia.
Qed.
Definition f32e_evt_src_check : ltac:(let T := type of F32.f32e_evt in exact T) := f32e_evt_of_F.

(* ===================== 0x82b5c with k <> 9 ===================== *)

(* F32.v:364-378. No memory access. *)
Lemma f32n_evt_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (k : Z) (RNG : footprint),
    s8 = Z_to_bv 64 k -> 0 <= k < 2 ^ 64 -> k <> 9 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 9) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                              (Z_to_bv 64 k) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros. subst s8. step. step.
  rewrite (f32_eqb_lit k 9) by lia. if_true.
  apply evtF_done. reflexivity.
Qed.

Lemma f32n_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (k : Z),
    s8 = Z_to_bv 64 k -> 0 <= k < 2 ^ 64 -> k <> 9 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 9) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                              (Z_to_bv 64 k) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). eapply f32n_evt_F; eassumption.
Qed.
Definition f32n_evt_src_check : ltac:(let T := type of F32.f32n_evt in exact T) := f32n_evt_of_F.

(* ===================== 0x82b5c with k = 9: the two block-marker checks ===================== *)

(* F32.v:382-416. Reads the byte Phi+16 and its shadow byte. *)
Lemma f32m1_evt_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (phi : Z) (b16 : byte) (RNG : footprint),
    s2 = Z_to_bv 64 phi -> s8 = Z_to_bv 64 9 -> s10 = Z_to_bv 64 ASAN_K ->
    0 < phi -> phi + 50 <= APPMEM_END ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [b16] -> bv_unsigned b16 <> 205 ->
    rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 -> rng RNG (phi + 16) 1 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (zxb b16) (Z_to_bv 64 205) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m phi b16 RNG -> -> -> Hp0 Hp1 Hsh Hb Hne Rsh Rb.
  unfold APPMEM_END in Hp1.
  pose proof (f32_rd1 m _ _ Hsh) as RDsh. pose proof (f32_rd1 m _ _ Hb) as RDb.
  pose proof (bv_unsigned_in_range 8 b16) as Rb8. unfold bv_modulus in Rb8.
  change (2 ^ Z.of_N 8) with 256 in Rb8.
  step. step. rewrite (f32_eqb_lit 9 9) by lia. if_false.
  step. rewrite (f32_eqb_lit phi 0) by lia. if_false.
  step. step. rewrite (f32_ltu_m17 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 16)) by lia.
  step. step. step. if_false.
  step. step. step.
  unfold zxb. rewrite (f32_eqb_lit (bv_unsigned b16) 205) by lia. if_true.
  apply evtF_done. reflexivity.
Qed.

Lemma f32m1_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (phi : Z) (b16 : byte),
    s2 = Z_to_bv 64 phi -> s8 = Z_to_bv 64 9 -> s10 = Z_to_bv 64 ASAN_K ->
    0 < phi -> phi + 50 <= APPMEM_END ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [b16] -> bv_unsigned b16 <> 205 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (zxb b16) (Z_to_bv 64 205) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m phi b16 E2 E8 E10 Hp0 Hp1 Hsh Hb Hne.
  pose proof (f32F_sh_rng (phi + 16) ltac:(lia) ltac:(unfold APPMEM_END in *; lia)) as (S1 & S2).
  apply (evtF_evt rsegs RNG_all). eapply f32m1_evt_F; try eassumption;
    apply rng_all; unfold APPMEM_END in *; lia.
Qed.
Definition f32m1_evt_src_check : ltac:(let T := type of F32.f32m1_evt in exact T) := f32m1_evt_of_F.

(* F32.v:419-459. Reads the bytes Phi+16 and Phi+17 and their shadow bytes. *)
Lemma f32m2_evt_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (phi : Z) (b17 : byte) (RNG : footprint),
    s2 = Z_to_bv 64 phi -> s8 = Z_to_bv 64 9 -> s10 = Z_to_bv 64 ASAN_K ->
    0 < phi -> phi + 50 <= APPMEM_END ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [Z_to_bv 8 205] ->
    bytes_at rsegs m (Z.shiftr (phi + 17) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 17) [b17] -> bv_unsigned b17 <> 234 ->
    rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 -> rng RNG (phi + 16) 1 ->
    rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 -> rng RNG (phi + 17) 1 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (zxb b17) (Z_to_bv 64 234) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m phi b17 RNG -> -> -> Hp0 Hp1 Hsh16 Hb16 Hsh17 Hb17 Hne Rsh16 Rb16 Rsh17 Rb17.
  unfold APPMEM_END in Hp1.
  pose proof (f32_rd1 m _ _ Hsh16) as RDsh16. pose proof (f32_rd1 m _ _ Hb16) as RDb16.
  pose proof (f32_rd1 m _ _ Hsh17) as RDsh17. pose proof (f32_rd1 m _ _ Hb17) as RDb17.
  pose proof (bv_unsigned_in_range 8 b17) as Rb. unfold bv_modulus in Rb.
  change (2 ^ Z.of_N 8) with 256 in Rb.
  step. step. rewrite (f32_eqb_lit 9 9) by lia. if_false.
  step. rewrite (f32_eqb_lit phi 0) by lia. if_false.
  step. step. rewrite (f32_ltu_m17 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 16)) by lia.
  step. step. step. if_false.
  step. step. step. rewrite (RcClassifyLib.cl_zxb_eqb (Z_to_bv 8 205) 205) by lia. if_false.
  step. step. rewrite (f32_ltu_m18 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 17)) by lia.
  step. step. step. if_false.
  step. step. step.
  unfold zxb. rewrite (f32_eqb_lit (bv_unsigned b17) 234) by lia. if_true.
  apply evtF_done. reflexivity.
Qed.

Lemma f32m2_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (phi : Z) (b17 : byte),
    s2 = Z_to_bv 64 phi -> s8 = Z_to_bv 64 9 -> s10 = Z_to_bv 64 ASAN_K ->
    0 < phi -> phi + 50 <= APPMEM_END ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [Z_to_bv 8 205] ->
    bytes_at rsegs m (Z.shiftr (phi + 17) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 17) [b17] -> bv_unsigned b17 <> 234 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (zxb b17) (Z_to_bv 64 234) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m phi b17 E2 E8 E10 Hp0 Hp1 Hsh16 Hb16 Hsh17 Hb17 Hne.
  pose proof (f32F_sh_rng (phi + 16) ltac:(lia) ltac:(unfold APPMEM_END in *; lia)) as (S1 & S2).
  pose proof (f32F_sh_rng (phi + 17) ltac:(lia) ltac:(unfold APPMEM_END in *; lia)) as (S3 & S4).
  apply (evtF_evt rsegs RNG_all). eapply f32m2_evt_F; try eassumption;
    apply rng_all; unfold APPMEM_END in *; lia.
Qed.
Definition f32m2_evt_src_check : ltac:(let T := type of F32.f32m2_evt in exact T) := f32m2_evt_of_F.

(* ===================== 0x82b5c -> the reac_box_catalogue call, split at the jal ===================== *)

(* Route (C) (a Theorem Labs lane 09:20Z; form a Theorem Labs lane 09:38Z, amendment 10:34Z): f32c_evt_pre_F with its shadow facts narrowed.
   Measured from f32c_evt_pre_F's proof: its premise `shadow_rw m` (HSW) has ONE use, HSW2, the post's shadow_rw m2
   (writable and readable bytes of the whole shadow carried across the two stores); it is not an access.  The run's
   memory accesses are the `rng` ranges: the two instrumented checks read the shadow bytes Z.shiftr (phi + 16) 3 +
   ASAN_K and Z.shiftr (phi + 17) 3 + ASAN_K and the app bytes phi + 16, phi + 17 (each by its bytes_at premise),
   0x82bb8 sb zero,4(s3) stores the shadow byte Sfr fr + 4 (writable by wr_at m (Sfr fr + 4) 1), the spill load
   reads [A + 160, A + 168) (bytes_at), 0x82bc0 sd zero,0(s7) stores [fr + 32, fr + 40) (wr_at m (fr + 32) 8).  No
   read or store goes through `shadow_rw m`, so the premise is DROPPED.  The post's `shadow_rw m2` becomes
   `forall P, shadow_rw_on P m -> shadow_rw_on P m2`: the two stores only add or replace bytes
   (ShadowRwOnT.shadow_rw_on_mem_mono, MemMono.rd_mono_write). *)
Lemma f32c_evt_pre_F_on :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (A fr phi lo spv : Z) (RNG : footprint),
    s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 phi -> s3 = Z_to_bv 64 (Sfr fr) -> s8 = Z_to_bv 64 9 ->
    s10 = Z_to_bv 64 ASAN_K -> sp = Z_to_bv 64 spv ->
    0 < phi -> phi + 50 <= APPMEM_END -> 0 <= A -> A + 448 <= 2 ^ 64 ->
    AC.GT <= fr -> fr mod 32 = 0 -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    HIGHMEM_BEG <= lo -> lo + 16 <= spv -> spv <= APPMEM_END -> spv <= A ->
    (fr + FRAME_BYTES <= spv - 16 \/ spv <= fr) ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [Z_to_bv 8 205] ->
    bytes_at rsegs m (Z.shiftr (phi + 17) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 17) [Z_to_bv 8 234] ->
    bytes_at rsegs m (A + 160) (le8 (Z_to_bv 64 (fr + 32))) ->
    wr_at rsegs m (fr + 32) 8 -> wr_at rsegs m (Sfr fr + 4) 1 ->
    stk rsegs m lo spv -> asan_cells m ->
    rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 -> rng RNG (phi + 16) 1 ->
    rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 -> rng RNG (phi + 17) 1 ->
    rng RNG (Sfr fr + 4) 1 -> rng RNG (A + 160) 8 -> rng RNG (fr + 32) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' : word) (m2 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82bcc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr + 32)) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (fr + 32)) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 CATc.REAC_BOX_CATALOGUE) fcr None m2 (seg_rom rsegs)
         /\ munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m2
         /\ wmono rsegs m m2 /\ stk rsegs m2 lo spv /\ asan_cells m2
         /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m2)
         /\ wr_at rsegs m2 (fr + 32) 8 /\ addressable m2 (fr + 32) 8
         /\ bytes_at rsegs m2 (Sfr fr + 4) [Z_to_bv 8 0]
         /\ (forall bs, bytes_at rsegs m (Sfr fr) bs -> length bs = 392%nat ->
               bytes_at rsegs m2 (Sfr fr) (upd_bytes bs 4 [Z_to_bv 8 0])))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m A fr phi lo spv RNG -> -> -> -> -> -> Hp0 Hp1 HA0 HA1 HGT Hfm Happ Hlo Hlo16 Hspe HAsp Hdisj
    Hsh16 Hb16 Hsh17 Hb17 H160 HWR8 HWR1 HST HAC
    Rsh16 Rb16 Rsh17 Rb17 Rsh4 R160 Rc8.
  unfold APPMEM_END in Hp1, Hspe. unfold AC.GT in HGT. unfold HIGHMEM_BEG in Hlo.
  pose proof (f32_rd1 m _ _ Hsh16) as RDsh16. pose proof (f32_rd1 m _ _ Hb16) as RDb16.
  pose proof (f32_rd1 m _ _ Hsh17) as RDsh17. pose proof (f32_rd1 m _ _ Hb17) as RDb17.
  pose proof (f32_rd8 m _ _ H160) as RD160.
  assert (Hc8 : forall a, fr + 32 <= a < fr + 40 -> app_mem a) by (intros a Ha; apply Happ; lia).
  assert (Hcapp : app_mem (fr + 32)) by (apply Hc8; lia).
  assert (Hshc : shadow_addr (fr + 32) = Sfr fr + 4)
    by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
  assert (HshIS : in_shadow (Sfr fr + 4)) by (rewrite <- Hshc; apply shadow_of_app; exact Hcapp).
  assert (HshB : 2147450880 <= Sfr fr + 4 < 17594333495296)
    by (pose proof HshIS as Hs;
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs; lia).
  assert (Hfrb : fr + FRAME_BYTES <= 140737488355328)
    by (pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha;
        unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha; lia).
  step. step. rewrite (f32_eqb_lit 9 9) by lia. if_false.
  step. rewrite (f32_eqb_lit phi 0) by lia. if_false.
  step. step. rewrite (f32_ltu_m17 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 16)) by lia.
  step. step. step. if_false.
  step. step. step. rewrite (RcClassifyLib.cl_zxb_eqb (Z_to_bv 8 205) 205) by lia. if_false.
  step. step. rewrite (f32_ltu_m18 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 17)) by lia.
  step. step. step. if_false.
  step. step. step. rewrite (RcClassifyLib.cl_zxb_eqb (Z_to_bv 8 234) 234) by lia. if_false.
  (* 0x82bb8 sb zero,4(s3) *)
  pose proof (f32_store_ok m (Sfr fr + 4) 1 1%nat HWR1 ltac:(cbn; lia)) as ST1.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      replace bs with [Z_to_bv 8 0] by (vm_compute; reflexivity)
  end.
  set (m1 := write_to_mem m (Z_to_bv 64 (Sfr fr + 4)) [Z_to_bv 8 0]) in *.
  assert (MU1 : munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m1).
  { unfold m1. apply (munch_write _ m m (Sfr fr + 4) [Z_to_bv 8 0] (munch_refl _ m));
      [lia | cbn [length]; lia | cbn [inside length]; lia]. }
  assert (WM1 : wmono rsegs m m1) by (unfold m1; apply (wmono_write rsegs m m); apply wmono_refl).
  assert (HB1 : bytes_at rsegs m1 (Sfr fr + 4) [Z_to_bv 8 0])
    by (unfold m1; apply bytes_at_write_same; cbn [length]; lia).
  assert (ST1' : stk rsegs m1 lo spv)
    by (unfold m1; apply (stk_write rsegs m lo spv (Sfr fr + 4) [Z_to_bv 8 0] HST); cbn [length]; lia).
  assert (WR81 : wr_at rsegs m1 (fr + 32) 8) by (unfold m1; apply wr_at_write; exact HWR8).
  assert (RD160' : ov_read_bytes rsegs m1 (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 (fr + 32)))).
  { apply f32_rd8. unfold m1. apply (bytes_at_write_other rsegs m (Sfr fr + 4) [Z_to_bv 8 0]);
      [exact H160 | lia | cbn [length]; lia | cbn [length]; rewrite length_le8;
       unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in *; lia]. }
  step.
  (* 0x82bc0 sd zero,0(s7) *)
  pose proof (f32_store_ok m1 (fr + 32) 8 8%nat WR81 ltac:(cbn; lia)) as ST2.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      replace bs with (le8 (Z_to_bv 64 0)) by (vm_compute; reflexivity)
  end.
  set (m2 := write_to_mem m1 (Z_to_bv 64 (fr + 32)) (le8 (Z_to_bv 64 0))) in *.
  assert (MU2 : munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m2).
  { unfold m2. apply (munch_write _ m m1 (fr + 32) (le8 (Z_to_bv 64 0)) MU1);
      [lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]. }
  assert (WM2 : wmono rsegs m m2) by (unfold m2; apply (wmono_write rsegs m m1); exact WM1).
  assert (ST2' : stk rsegs m2 lo spv)
    by (unfold m2; apply (stk_write rsegs m1 lo spv (fr + 32) (le8 (Z_to_bv 64 0)) ST1');
        [lia | rewrite length_le8; lia]).
  assert (WR82 : wr_at rsegs m2 (fr + 32) 8) by (unfold m2; apply wr_at_write; exact WR81).
  assert (HB2 : bytes_at rsegs m2 (Sfr fr + 4) [Z_to_bv 8 0]).
  { unfold m2. apply (bytes_at_write_other rsegs m1 (fr + 32) (le8 (Z_to_bv 64 0)));
      [exact HB1 | lia | rewrite length_le8; lia |
       cbn [length]; rewrite length_le8;
       unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in *; lia]. }
  assert (HoutW2 : forall x, 0 <= x < 6283264 ->
            outside [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] x).
  { intros x Hx. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (HAC2 : asan_cells m2) by (apply (f32_cells_keep _ m m2 HAC MU2 HoutW2)).
  (* every region of m: the two stores only add or replace bytes *)
  assert (HSW2 : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m2).
  { intros P HP. apply (B.ShadowRwOnT.shadow_rw_on_mem_mono P m m2 HP WM2).
    unfold m2, m1. apply B.Prog.MemMono.rd_mono_write, B.Prog.MemMono.rd_mono_write, B.Prog.MemMono.rd_mono_refl. }
  assert (HADR : addressable m2 (fr + 32) 8).
  { split; [lia|]. split; [lia|].
    split; [pose proof (Happ (fr + 39) ltac:(lia)) as Ha;
            unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *; lia|].
    intros i Hi. split; [apply Hc8; lia|].
    exists (Z_to_bv 8 0). split.
    - replace (shadow_addr (fr + 32 + i)) with (Sfr fr + 4).
      + destruct HB2 as (_ & _ & HB2b). pose proof (HB2b 0%nat ltac:(cbn; lia)) as HH.
        cbn [Z.of_nat nth_error] in HH. rewrite Z.add_0_r in HH. exact HH.
      + unfold Sfr, shadow_addr. replace (fr + 32 + i) with (fr + 4 * 8 + i) by lia.
        replace (fr + 4 * 8 + i) with ((fr / 8 + 4) * 8 + i) by (Z.div_mod_to_equations; lia).
        rewrite Z.div_add_l by lia. rewrite (Z.div_small i 8) by lia. lia.
    - unfold shadow_ok. left. reflexivity. }
  assert (HTR : forall bs, bytes_at rsegs m (Sfr fr) bs -> length bs = 392%nat ->
            bytes_at rsegs m2 (Sfr fr) (upd_bytes bs 4 [Z_to_bv 8 0])).
  { intros bs Hbs Hl.
    assert (Hin1 : bytes_at rsegs m1 (Sfr fr) (upd_bytes bs 4 [Z_to_bv 8 0])).
    { unfold m1. apply (bytes_at_write_inside rsegs m (Sfr fr) bs 4 [Z_to_bv 8 0] Hbs);
        [lia | cbn [length]; lia]. }
    assert (Hlen' : length (upd_bytes bs 4 [Z_to_bv 8 0]) = 392%nat)
      by (rewrite upd_bytes_length; [exact Hl | cbn [length]; lia]).
    unfold m2. apply (bytes_at_write_other rsegs m1 (fr + 32) (le8 (Z_to_bv 64 0)));
      [exact Hin1 | lia | rewrite length_le8; lia |
       rewrite Hlen', length_le8;
       pose proof (f32_frsh_shadow fr (Sfr fr) Happ ltac:(lia)) as Hs0;
       pose proof (f32_frsh_shadow fr (Sfr fr + 391) Happ ltac:(lia)) as Hs1;
       unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
         APPMEM_END in Hs0, Hs1, Hcapp |- *; lia]. }
  (* 0x82bc4 mv a0,s7; 0x82bc8 jal reac_box_catalogue *)
  step. step.
  apply evtF_done.
  do 2 eexists. exists m2.
  split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2'|]. split; [exact HAC2|].
  split; [exact HSW2|]. split; [exact WR82|]. split; [exact HADR|].
  split; [exact HB2 | exact HTR].
Qed.

(* F32.v:558-646: the two instrumented checks pass, the shadow byte S(fr)+4 is zeroed, the count variable
   [fr+32, fr+40) is zeroed, the count pointer is loaded into s7 and moved to a0, and 0x82bc8 jal stops AT the
   callee entry with ra = 0x82bcc.  Route (C): proved from f32c_evt_pre_F_on, statement unchanged. *)
Lemma f32c_evt_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (A fr phi lo spv : Z) (RNG : footprint),
    s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 phi -> s3 = Z_to_bv 64 (Sfr fr) -> s8 = Z_to_bv 64 9 ->
    s10 = Z_to_bv 64 ASAN_K -> sp = Z_to_bv 64 spv ->
    0 < phi -> phi + 50 <= APPMEM_END -> 0 <= A -> A + 448 <= 2 ^ 64 ->
    AC.GT <= fr -> fr mod 32 = 0 -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    HIGHMEM_BEG <= lo -> lo + 16 <= spv -> spv <= APPMEM_END -> spv <= A ->
    (fr + FRAME_BYTES <= spv - 16 \/ spv <= fr) ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [Z_to_bv 8 205] ->
    bytes_at rsegs m (Z.shiftr (phi + 17) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 17) [Z_to_bv 8 234] ->
    bytes_at rsegs m (A + 160) (le8 (Z_to_bv 64 (fr + 32))) ->
    wr_at rsegs m (fr + 32) 8 -> wr_at rsegs m (Sfr fr + 4) 1 ->
    stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 -> rng RNG (phi + 16) 1 ->
    rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 -> rng RNG (phi + 17) 1 ->
    rng RNG (Sfr fr + 4) 1 -> rng RNG (A + 160) 8 -> rng RNG (fr + 32) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' : word) (m2 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82bcc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr + 32)) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (fr + 32)) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 CATc.REAC_BOX_CATALOGUE) fcr None m2 (seg_rom rsegs)
         /\ munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m2
         /\ wmono rsegs m m2 /\ stk rsegs m2 lo spv /\ asan_cells m2 /\ shadow_rw m2
         /\ wr_at rsegs m2 (fr + 32) 8 /\ addressable m2 (fr + 32) 8
         /\ bytes_at rsegs m2 (Sfr fr + 4) [Z_to_bv 8 0]
         /\ (forall bs, bytes_at rsegs m (Sfr fr) bs -> length bs = 392%nat ->
               bytes_at rsegs m2 (Sfr fr) (upd_bytes bs 4 [Z_to_bv 8 0])))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m A fr phi lo spv RNG E1 E2 E3 E8 E10 Esp Hp0 Hp1 HA0 HA1 HGT Hfm Happ Hlo Hlo16 Hspe HAsp Hdisj
    Hsh16 Hb16 Hsh17 Hb17 H160 HWR8 HWR1 HST HAC HSW
    Rsh16 Rb16 Rsh17 Rb17 Rsh4 R160 Rc8.
  eapply evtF_mono;
    [exact (f32c_evt_pre_F_on ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 Fr fcr m A fr phi lo spv RNG E1 E2 E3 E8 E10 Esp Hp0 Hp1 HA0 HA1 HGT Hfm Happ Hlo Hlo16
              Hspe HAsp Hdisj Hsh16 Hb16 Hsh17 Hb17 H160 HWR8 HWR1 HST HAC
              Rsh16 Rb16 Rsh17 Rb17 Rsh4 R160 Rc8)|].
  intros ms' (a1' & a2' & m2 & E & MU & WM & ST & AC & SW & Rest).
  exists a1', a2', m2. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
  split; [exact AC|].
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m2 (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))|].
  exact Rest.
Qed.

(* From the return pc 0x82bcc to the exit cut 0x82bcc (F32.v:667-734): no step. The premises are the state the
   pre stretch leaves (over m and m2) plus the reac_box_catalogue post facts (over m2 and m3). *)
Lemma f32c_evt_post_F :
  forall (sp gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m m2 m3 : word -> option byte) (fr lo spv : Z) (RNG : footprint),
    AC.GT <= fr -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    HIGHMEM_BEG <= lo -> lo + 16 <= spv -> spv <= APPMEM_END ->
    (fr + FRAME_BYTES <= spv - 16 \/ spv <= fr) ->
    shadow_rw m ->
    munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m2 ->
    wmono rsegs m m2 -> bytes_at rsegs m2 (Sfr fr + 4) [Z_to_bv 8 0] ->
    (forall bs, bytes_at rsegs m (Sfr fr) bs -> length bs = 392%nat ->
       bytes_at rsegs m2 (Sfr fr) (upd_bytes bs 4 [Z_to_bv 8 0])) ->
    munch [(spv - 16, spv); (fr + 32, fr + 32 + 8)] m2 m3 ->
    wmono rsegs m2 m3 -> stk rsegs m3 lo spv ->
    bytes_at rsegs m3 (fr + 32) (le8 (Z_to_bv 64 11)) ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1'' a2'' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CATc.BOX_CATALOGUE) a1'' a2'' a3 a4 a5 a6 a7 s2 s3 s4
                       s5 s6 (Z_to_bv 64 (fr + 32)) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x82bcc) fcr None m' (seg_rom rsegs)
         /\ munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' lo spv
         /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
         /\ (forall a, in_shadow a -> exists b, mrd rsegs m' (wa a) = Some b)
         /\ (forall bs, bytes_at rsegs m (Sfr fr) bs -> length bs = Z.to_nat FRAME_SHADOW ->
               exists bs', bytes_at rsegs m' (Sfr fr) bs' /\ length bs' = Z.to_nat FRAME_SHADOW))
      (MS (mkR (Z_to_bv 64 0x82bcc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CATc.BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 (fr + 32)) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82bcc) fcr None m3 (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros sp gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m m2 m3 fr lo spv RNG HGT Happ Hlo Hlo16 Hspe Hdisj HSW MU2 WM2 HB2 HTR MU3 WM3 ST3 HCb.
  unfold AC.GT in HGT. unfold HIGHMEM_BEG in Hlo. unfold APPMEM_END in Hspe.
  assert (Hfrb : fr + FRAME_BYTES <= 140737488355328)
    by (pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha;
        unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha; lia).
  assert (Hc8 : forall a, fr + 32 <= a < fr + 40 -> app_mem a) by (intros a Ha; apply Happ; lia).
  assert (Hcapp : app_mem (fr + 32)) by (apply Hc8; lia).
  assert (MUall : munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m3).
  { apply (munch_trans _ m m2 m3 MU2).
    apply (munch_weaken [(spv - 16, spv); (fr + 32, fr + 32 + 8)]); [|exact MU3].
    intros x Hx. cbn [outside] in Hx |- *. split; [lia|]. split; [lia | exact I]. }
  assert (WMall : wmono rsegs m m3) by (apply (wmono_trans rsegs m m2 m3 WM2 WM3)).
  assert (HmrdW3 : forall x, 0 <= x < 2 ^ 64 ->
            ~ (Sfr fr + 4 <= x < Sfr fr + 5) -> ~ (fr + 32 <= x < fr + 40) -> ~ (spv - 16 <= x < spv) ->
            mrd rsegs m3 (wa x) = mrd rsegs m (wa x)).
  { intros x Hx H1 H2 H3. apply (f32_mrd_munch _ m m3 x MUall Hx).
    cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  apply evtF_done.
  eexists _, _, _, m3. split; [reflexivity|].
  split; [exact MUall|]. split; [exact WMall|].
  split; [exact ST3|].
  split; [exact HCb|].
  split.
  { intros a Hin. destruct (Z.eq_dec a (Sfr fr + 4)) as [->|Hne].
    - destruct (in_shadow_range (Sfr fr + 4) Hin) as (Hr0 & Hr1).
      assert (Hb : exists b, mrd rsegs m2 (wa (Sfr fr + 4)) = Some b).
      { exists (Z_to_bv 8 0). destruct HB2 as (_ & _ & HB2b). pose proof (HB2b 0%nat ltac:(cbn; lia)) as HH.
        cbn [Z.of_nat nth_error] in HH. rewrite Z.add_0_r in HH. exact HH. }
      destruct Hb as (b & Hb). exists b.
      rewrite (f32_mrd_munch _ m2 m3 (Sfr fr + 4) MU3); [exact Hb | lia |].
      cbn [outside]. split; [|split; [|exact I]].
      + intros Hc. apply (app_not_shadow (Sfr fr + 4)); [|exact Hin].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
      + intros Hc. assert (Hc' : fr + 32 <= Sfr fr + 4 < fr + 40) by lia.
        exact (app_not_shadow (Sfr fr + 4) (Hc8 _ Hc') Hin).
    - destruct (HSW a Hin) as (_ & b & Hb). exists b.
      rewrite HmrdW3; [exact Hb | | lia | |].
      + pose proof (in_shadow_range a Hin). lia.
      + intros Hc. exact (app_not_shadow a (Hc8 a Hc) Hin).
      + intros Hc. apply (app_not_shadow a); [|exact Hin].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
  { intros bs Hbs Hl. change (Z.to_nat FRAME_SHADOW) with 392%nat in Hl |- *.
    exists (upd_bytes bs 4 [Z_to_bv 8 0]).
    split; [|rewrite upd_bytes_length; [exact Hl | cbn [length]; lia]].
    pose proof (HTR bs Hbs Hl) as Hin2.
    assert (Hlen' : length (upd_bytes bs 4 [Z_to_bv 8 0]) = 392%nat)
      by (rewrite upd_bytes_length; [exact Hl | cbn [length]; lia]).
    eapply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 32, fr + 32 + 8)] m2 m3);
      [exact Hin2 | exact MU3 |].
    rewrite Hlen'. cbn [disjoint_from].
    pose proof (f32_frsh_shadow fr (Sfr fr) Happ ltac:(lia)) as Hs0.
    pose proof (f32_frsh_shadow fr (Sfr fr + 391) Happ ltac:(lia)) as Hs1.
    pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Hlast.
    pose proof (Happ fr ltac:(lia)) as Hfirst.
    unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
      in Hs0, Hs1, Hcapp, Hlast, Hfirst |- *.
    repeat split; first [exact I | lia]. }
Qed.
