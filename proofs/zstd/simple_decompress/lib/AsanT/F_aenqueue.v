(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Notation acache24 t := (t + 2128) (only parsing).       (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 spacebeg)] ->
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
        F (Z_to_bv 64 0x37db8) fc None m (seg_rom bsegs)).
Proof.
  intros until chunks. intros ST CEIL LO MI -> -> -> -> QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RSTK RT RB RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  carve_frame 64%nat ST.
  destruct full.
  - (* [comment removed for export] *)
    destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1).
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read bsegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep. step.                   (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [|exfalso; lia].        (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2'; zify_cond K2'; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read bsegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [|exfalso; lia].        (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.

(* [comment removed for export] *)
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
  iclr C 32 -> C + 32 <= ATOP -> AIMG_HI <= lst -> lst + Q_BATCH_BYTES <= ATOP ->        (* [comment removed for export] *)
  (C + 32 <= lst \/ lst + Q_BATCH_BYTES <= C) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG C 32 -> rng RNG lst Q_BATCH_BYTES ->
  evtF bsegs RNG (enq_append_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C nb fst lst qb hm n nx bsz cnt lo hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37db8) fc None m (seg_rom bsegs)).
Proof.
  intros until hs. intros ST CEIL LO MI -> -> -> QC NB QB QBN N HM FST LB CNT BSZ BSZN NX LA LEN LJ C0 C1 L0 L1 DJ RIMG RSTK RC RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  destruct LJ as [junkt LJ]. pose proof (stk_of_cb _ _ _ _ LJ ltac:(lia)) as TJ. clear LJ junkt.
  carve_frame 64%nat ST.
  do 8 step.                                   (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
  step. step. step. step. if_cases K1; zify_cond K1; [|exfalso; lia].   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; [exfalso; lia|].          (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  replace (Z.shiftl cnt 3) with (8 * cnt) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split bsegs mm (lst + 24 + 8 * cnt) (lst + 24 + 8 * cnt + 8) _ TJ ltac:(lia)) as [TJ0 TJ1];
    destruct (stk_cb mm _ _ TJ0 ltac:(lia)) as [junk8 E8] end.
  clear TJ TJ0. replace (Z.to_nat (lst + 24 + 8 * cnt + 8 - (lst + 24 + 8 * cnt))) with 8%nat in E8 by lia.
  replace (lst + 24 + 8 * cnt) with (lst + 8 * cnt + 24) in E8 by lia.
  step.                                        (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. zstep. step.                           (* [comment removed for export] *)
  do 9 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold enq_append_post. finish.
  - eapply u64arr_snoc; [exact LA|]. rewrite LEN. replace (lst + 24 + 8 * Z.of_nat (Z.to_nat cnt)) with (lst + 8 * cnt + 24) by lia. exact E8.
  - lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TJ1 ltac:(lia)) as [bs Hbs] end.
    exists bs. replace (lst + 24 + 8 * cnt + (8192 - 24 - 8 * cnt) - (lst + 24 + 8 * cnt + 8)) with (8192 - 24 - 8 * (cnt + 1)) in Hbs by lia.
    replace (lst + 24 + 8 * cnt + 8) with (lst + 24 + 8 * (cnt + 1)) in Hbs by lia. exact Hbs.
Qed.
End CANSEC1.
