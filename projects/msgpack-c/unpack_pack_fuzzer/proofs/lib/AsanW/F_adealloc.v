(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg ABase AQConst ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit AKit2 AKitQ F_afree_s.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_adealloc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S b1 actx lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xd6458) (Z_to_bv 64 hm) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 S)
                  a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x40f14) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 18446744069414584320)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat.

Lemma dealloc_spec : forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 1 ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->

  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF asegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3c98c) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros ST CEIL LO MI TP -> -> -> HD UW B1 B13 N AL H0 H1 HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RSTK RCTX RT RH. band_lin.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  do 4 step. zstep. do 5 step.
  carve_frame 64%nat ST.
  do 9 step.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].
  do 6 step. zstep. step.
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.
  zstep. zstep. step. step. step.
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.

  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.
  zstep. rewrite (byte0_of_word 2 b1) by lia.
  step. if_lit.
  zstep. zstep. zstep.
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.
  step. if_lit.
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.
  lstep. zstep. rewrite B13.
  step. if_lit.
  zstep. step. step. if_lit.
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.
  aload STATS 4 (t + 2800 + 32).
  aload STATS 3 (t + 2800 + 24).
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.
  astore STATS 3.
  astore STATS 4.
  step. step. step. step.
  do 10 step.
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End CANSEC1.
End F_adealloc.

Module F_adealloc_entry.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import F_adealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Lemma dealloc_spec_D : forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->

  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF asegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros ST CEIL LO MI TP -> -> -> -> -> -> HD UW B1 B13 N AL H0 H1 HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RSTK RCTX RT RH. band_lin.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 9 step.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].
  do 6 step. zstep. step.
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.
  zstep. zstep. step. step. step.
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.

  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.
  zstep. rewrite (byte0_of_word 2 b1) by lia.
  step. if_lit.
  zstep. zstep. zstep.
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.
  step. if_lit.
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.
  lstep. zstep. rewrite B13.
  step. if_lit.
  zstep. step. step. if_lit.
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.
  aload STATS 4 (t + 2800 + 32).
  aload STATS 3 (t + 2800 + 24).
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.
  astore STATS 3.
  astore STATS 4.
  step. step. step. step.
  do 10 step.
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End CANSEC1.
End F_adealloc_entry.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_adealloc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S b1 actx lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xd8618) (Z_to_bv 64 hm) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 S)
                  a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x418a4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 18446744069414584320)]
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat.

Lemma dealloc_spec : forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 1 ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->

  rw_cells bsegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF bsegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d31c) fc None m (seg_rom bsegs)).
Proof.
  intros until sj. intros ST CEIL LO MI TP -> -> -> HD UW B1 B13 N AL H0 H1 HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RSTK RCTX RT RH. band_lin.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  do 4 step. zstep. do 5 step.
  carve_frame 64%nat ST.
  do 9 step.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].
  do 6 step. zstep. step.
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.
  zstep. zstep. step. step. step.
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.

  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.
  zstep. rewrite (byte0_of_word 2 b1) by lia.
  step. if_lit.
  zstep. zstep. zstep.
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.
  step. if_lit.
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.
  lstep. zstep. rewrite B13.
  step. if_lit.
  zstep. step. step. if_lit.
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.
  aload STATS 4 (t + 2800 + 32).
  aload STATS 3 (t + 2800 + 24).
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.
  astore STATS 3.
  astore STATS 4.
  step. step. step. step.
  do 10 step.
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End CANSEC1.
End F_adealloc.

Module F_adealloc_entry.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import F_adealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Lemma dealloc_spec_D : forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->

  rw_cells bsegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF bsegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until sj. intros ST CEIL LO MI TP -> -> -> -> -> -> HD UW B1 B13 N AL H0 H1 HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RSTK RCTX RT RH. band_lin.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 9 step.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].
  do 6 step. zstep. step.
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.
  zstep. zstep. step. step. step.
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.

  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.
  zstep. rewrite (byte0_of_word 2 b1) by lia.
  step. if_lit.
  zstep. zstep. zstep.
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.
  step. if_lit.
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.
  lstep. zstep. rewrite B13.
  step. if_lit.
  zstep. step. step. if_lit.
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.
  aload STATS 4 (t + 2800 + 32).
  aload STATS 3 (t + 2800 + 24).
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.
  astore STATS 3.
  astore STATS 4.
  step. step. step. step.
  do 10 step.
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End CANSEC1.
End F_adealloc_entry.
End TwinB.
