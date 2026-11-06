(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg ABase AQConst ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit AKit2 AKitQ.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_aenqueue.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation acache24 t := (t + 2128) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition enq_new_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt24 b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells asegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Lemma enqueue_new_spec : forall (full : bool) (t lst b : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt24 spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->

  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] ->
  u32arr asegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt24 <= 16 -> nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (enq_new_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt24 b lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4123c) fc None m (seg_rom asegs)).
Proof.
  intros until chunks. intros ST CEIL LO MI -> -> -> -> QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RSTK RT RB RL. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  carve_frame 64%nat ST.
  destruct full.
  -
    destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1).
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].

    lstep.
    step. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read asegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].
    step. step. zstep.
    step.

    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [exfalso; lia|].
    step. step. zstep. step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  -
    pose proof FULL as NB0. clear FULL.
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [|exfalso; lia].

    lstep.
    step. if_cases K2'; zify_cond K2'; [exfalso; lia|].
    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read asegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].
    step. step. zstep.
    step.

    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [|exfalso; lia].
    step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.

Definition enq_append_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C nb fst lst qb hm n nx bsz cnt lo : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 (qb + n))]
    /\ rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
    /\ u64arr asegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
    /\ (exists bs, rw_cells asegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs]).

Lemma enqueue_append_spec : forall (C lst cnt : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (hs : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 C -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> qb + n < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 ->
  rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)] ->
  0 <= cnt < Q_BATCH -> 0 <= bsz -> bsz + n < 2^63 -> 0 <= nx < 2^64 ->
  u64arr asegs m (lst + 24) hs -> length hs = Z.to_nat cnt ->
  (exists bs, rw_cells asegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (Q_BATCH_BYTES - 24 - 8 * cnt)) bs]) ->
  iclr C 32 -> C + 32 <= ATOP -> AIMG_HI <= lst -> lst + Q_BATCH_BYTES <= ATOP ->
  (C + 32 <= lst \/ lst + Q_BATCH_BYTES <= C) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG C 32 -> rng RNG lst Q_BATCH_BYTES ->
  evtF asegs RNG (enq_append_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C nb fst lst qb hm n nx bsz cnt lo hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4123c) fc None m (seg_rom asegs)).
Proof.
  intros until hs. intros ST CEIL LO MI -> -> -> QC NB QB QBN N HM FST LB CNT BSZ BSZN NX LA LEN LJ C0 C1 L0 L1 DJ RIMG RSTK RC RL. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  destruct LJ as [junkt LJ]. pose proof (stk_of_cb _ _ _ _ LJ ltac:(lia)) as TJ. clear LJ junkt.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0; [exfalso; lia|].
  step. step. step. step. if_cases K1; zify_cond K1; [|exfalso; lia].
  step. if_cases K2; zify_cond K2; [exfalso; lia|].
  step. zstep.
  replace (Z.shiftl cnt 3) with (8 * cnt) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. zstep.
  step. step.

  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split asegs mm (lst + 24 + 8 * cnt) (lst + 24 + 8 * cnt + 8) _ TJ ltac:(lia)) as [TJ0 TJ1];
    destruct (stk_cb mm _ _ TJ0 ltac:(lia)) as [junk8 E8] end.
  clear TJ TJ0. replace (Z.to_nat (lst + 24 + 8 * cnt + 8 - (lst + 24 + 8 * cnt))) with 8%nat in E8 by lia.
  replace (lst + 24 + 8 * cnt) with (lst + 8 * cnt + 24) in E8 by lia.
  step.
  step.
  step. zstep. step.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  unfold enq_append_post. finish.
  - eapply u64arr_snoc; [exact LA|]. rewrite LEN. replace (lst + 24 + 8 * Z.of_nat (Z.to_nat cnt)) with (lst + 8 * cnt + 24) by lia. exact E8.
  - lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TJ1 ltac:(lia)) as [bs Hbs] end.
    exists bs. replace (lst + 24 + 8 * cnt + (8192 - 24 - 8 * cnt) - (lst + 24 + 8 * cnt + 8)) with (8192 - 24 - 8 * (cnt + 1)) in Hbs by lia.
    replace (lst + 24 + 8 * cnt + 8) with (lst + 24 + 8 * (cnt + 1)) in Hbs by lia. exact Hbs.
Qed.
End CANSEC1.
End F_aenqueue.

Module F_aenqueueR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation acache24 t := (t + 2128) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition enq_to_refill_post (ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41390) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2
                  (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 0xd6458) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a2 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41b70) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma enqueue_to_refill_spec : forall (full : bool) (t lst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP /\ rng RNG lst Q_BATCH_BYTES
   else nb = 0) ->

  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (enq_to_refill_post ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4123c) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> QC NB LST FULL CR T0 T1 TAL DTL RSTK RT. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  destruct full.
  -
    destruct FULL as (NB1 & LB & L0 & L1 & RL).
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].
    lstep.
    step. if_cases K2; zify_cond K2; [|exfalso; lia].
    zstep. step. step.
    step. step. step. step. step. step.
    step. step. step.
    step.
    unfold enq_to_refill_post. finish. exact FR.
  -
    pose proof FULL as NB0. clear FULL.
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [|exfalso; lia].
    lstep.
    step. if_cases K2'; zify_cond K2'; [|exfalso; lia].
    zstep. step. step.
    step. step. step. step. step. step.
    step. step. step.
    step.
    unfold enq_to_refill_post. finish. exact FR.
Qed.

Definition enq_from_refill_post (full : bool) (vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom asegs)
    /\ munch [(t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + 64)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells asegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Lemma enqueue_from_refill_spec : forall (full : bool) (t lst b : Z) RNG
    (ra0 sp gp tp t0 t1 t2 vra v0 v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word) (j0 : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 < 2^64 ->
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 8 j0; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->

  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng RNG (bv_unsigned sp) 64 -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (enq_from_refill_post full vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt b lo maxc csz m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41390) fc None m (seg_rom asegs)).
Proof.
  intros until j0. intros ST CEIL LO SP64 MI FR QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RSTK RT RB RL. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.

  step.
  step. if_cases KR; zify_cond KR; [exfalso; lia|].
  step. step. step.
  lstep.
  step. step.
  destruct full.
  -
    destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1).

    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].
    step. step. zstep.
    step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [exfalso; lia|].
    step. step. zstep. step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  -
    pose proof FULL as NB0. clear FULL.
    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].
    step. step. zstep.
    step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [|exfalso; lia].
    step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.
End CANSEC1.
End F_aenqueueR.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_aenqueue.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation acache24 t := (t + 2128) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition enq_new_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt24 b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells bsegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells bsegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr bsegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells bsegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Lemma enqueue_new_spec : forall (full : bool) (t lst b : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt24 spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->

  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache24 t) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt24 <= 16 -> nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (enq_new_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt24 b lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41bcc) fc None m (seg_rom bsegs)).
Proof.
  intros until chunks. intros ST CEIL LO MI -> -> -> -> QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RSTK RT RB RL. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  carve_frame 64%nat ST.
  destruct full.
  -
    destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1).
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].

    lstep.
    step. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read bsegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].
    step. step. zstep.
    step.

    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [exfalso; lia|].
    step. step. zstep. step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  -
    pose proof FULL as NB0. clear FULL.
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [|exfalso; lia].

    lstep.
    step. if_cases K2'; zify_cond K2'; [exfalso; lia|].
    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read bsegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].
    step. step. zstep.
    step.

    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [|exfalso; lia].
    step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.

Definition enq_append_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C nb fst lst qb hm n nx bsz cnt lo : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 (qb + n))]
    /\ rw_cells bsegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
    /\ u64arr bsegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
    /\ (exists bs, rw_cells bsegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs]).

Lemma enqueue_append_spec : forall (C lst cnt : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (hs : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 C -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells bsegs m C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> qb + n < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 ->
  rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)] ->
  0 <= cnt < Q_BATCH -> 0 <= bsz -> bsz + n < 2^63 -> 0 <= nx < 2^64 ->
  u64arr bsegs m (lst + 24) hs -> length hs = Z.to_nat cnt ->
  (exists bs, rw_cells bsegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (Q_BATCH_BYTES - 24 - 8 * cnt)) bs]) ->
  iclr C 32 -> C + 32 <= ATOP -> AIMG_HI <= lst -> lst + Q_BATCH_BYTES <= ATOP ->
  (C + 32 <= lst \/ lst + Q_BATCH_BYTES <= C) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG C 32 -> rng RNG lst Q_BATCH_BYTES ->
  evtF bsegs RNG (enq_append_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C nb fst lst qb hm n nx bsz cnt lo hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41bcc) fc None m (seg_rom bsegs)).
Proof.
  intros until hs. intros ST CEIL LO MI -> -> -> QC NB QB QBN N HM FST LB CNT BSZ BSZN NX LA LEN LJ C0 C1 L0 L1 DJ RIMG RSTK RC RL. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  destruct LJ as [junkt LJ]. pose proof (stk_of_cb _ _ _ _ LJ ltac:(lia)) as TJ. clear LJ junkt.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0; [exfalso; lia|].
  step. step. step. step. if_cases K1; zify_cond K1; [|exfalso; lia].
  step. if_cases K2; zify_cond K2; [exfalso; lia|].
  step. zstep.
  replace (Z.shiftl cnt 3) with (8 * cnt) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. zstep.
  step. step.

  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split bsegs mm (lst + 24 + 8 * cnt) (lst + 24 + 8 * cnt + 8) _ TJ ltac:(lia)) as [TJ0 TJ1];
    destruct (stk_cb mm _ _ TJ0 ltac:(lia)) as [junk8 E8] end.
  clear TJ TJ0. replace (Z.to_nat (lst + 24 + 8 * cnt + 8 - (lst + 24 + 8 * cnt))) with 8%nat in E8 by lia.
  replace (lst + 24 + 8 * cnt) with (lst + 8 * cnt + 24) in E8 by lia.
  step.
  step.
  step. zstep. step.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  unfold enq_append_post. finish.
  - eapply u64arr_snoc; [exact LA|]. rewrite LEN. replace (lst + 24 + 8 * Z.of_nat (Z.to_nat cnt)) with (lst + 8 * cnt + 24) by lia. exact E8.
  - lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TJ1 ltac:(lia)) as [bs Hbs] end.
    exists bs. replace (lst + 24 + 8 * cnt + (8192 - 24 - 8 * cnt) - (lst + 24 + 8 * cnt + 8)) with (8192 - 24 - 8 * (cnt + 1)) in Hbs by lia.
    replace (lst + 24 + 8 * cnt + 8) with (lst + 24 + 8 * (cnt + 1)) in Hbs by lia. exact Hbs.
Qed.
End CANSEC1.
End F_aenqueue.

Module F_aenqueueR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation acache24 t := (t + 2128) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition enq_to_refill_post (ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41d20) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2
                  (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 0xd8618) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a2 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x42500) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells bsegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma enqueue_to_refill_spec : forall (full : bool) (t lst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (maxc csz : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP /\ rng RNG lst Q_BATCH_BYTES
   else nb = 0) ->

  rw_cells bsegs m (acache24 t) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (enq_to_refill_post ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41bcc) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> QC NB LST FULL CR T0 T1 TAL DTL RSTK RT. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  destruct full.
  -
    destruct FULL as (NB1 & LB & L0 & L1 & RL).
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].
    lstep.
    step. if_cases K2; zify_cond K2; [|exfalso; lia].
    zstep. step. step.
    step. step. step. step. step. step.
    step. step. step.
    step.
    unfold enq_to_refill_post. finish. exact FR.
  -
    pose proof FULL as NB0. clear FULL.
    do 8 step.
    step.
    step. if_cases K0; zify_cond K0; [|exfalso; lia].
    lstep.
    step. if_cases K2'; zify_cond K2'; [|exfalso; lia].
    zstep. step. step.
    step. step. step. step. step. step.
    step. step. step.
    step.
    unfold enq_to_refill_post. finish. exact FR.
Qed.

Definition enq_from_refill_post (full : bool) (vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom bsegs)
    /\ munch [(t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + 64)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells bsegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells bsegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr bsegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells bsegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Lemma enqueue_from_refill_spec : forall (full : bool) (t lst b : Z) RNG
    (ra0 sp gp tp t0 t1 t2 vra v0 v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word) (j0 : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 < 2^64 ->
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 8 j0; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->

  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache24 t) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng RNG (bv_unsigned sp) 64 -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (enq_from_refill_post full vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt b lo maxc csz m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41d20) fc None m (seg_rom bsegs)).
Proof.
  intros until j0. intros ST CEIL LO SP64 MI FR QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RSTK RT RB RL. band_lin.
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.

  step.
  step. if_cases KR; zify_cond KR; [exfalso; lia|].
  step. step. step.
  lstep.
  step. step.
  destruct full.
  -
    destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1).

    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].
    step. step. zstep.
    step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [exfalso; lia|].
    step. step. zstep. step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  -
    pose proof FULL as NB0. clear FULL.
    zstep. zstep.
    step.
    zstep. zstep.
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.
    pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.
    step. step.
    step. zstep. zstep. zstep. zstep.
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].
    step. step. zstep.
    step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.
    step. if_cases K4; zify_cond K4; [|exfalso; lia].
    step.
    step. step.
    step. zstep. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.
End CANSEC1.
End F_aenqueueR.
End TwinB.
