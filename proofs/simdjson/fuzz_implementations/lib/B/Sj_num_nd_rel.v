(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_pro Sj_num_lm_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section NDREL.
  Variables (f fl : Z) (m0 : mem).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis FLO : (0x6e0000 <= f /\ f + 1024 < 2^62)%Z.
  Hypothesis FLR : (0 < fl /\ fl + 1 < 2^62)%Z.
  Variable Q : machine_state -> Prop.

  Lemma nd_rel1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc h0 h1 (mm : mem),
    rw_cells bsegs mm f [CB 8 h0; CB 24 h1] ->
    mem_inv bsegs mm -> munch [(f, f + 8)]%Z m0 mm -> wmono bsegs m0 mm ->
    (forall (mm' : mem), rw_cells bsegs mm' f [C8 (Z_to_bv 64 1172321806); CB 24 h1] ->
       mem_inv bsegs mm' -> munch [(f, f + 8)]%Z m0 mm' -> wmono bsegs m0 mm' ->
       evt bsegs Q (MS (mkR (Z_to_bv 64 0xfb6d8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 128) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 S) s4 s5 s6 s7 s8
                        (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x883a0) fc None mm' (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 1172321806) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 S) s4 s5 s6 s7 s8 (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfb6c4) fc None mm (seg_rom bsegs)).
  Proof using FLO.
    intros until mm. intros HDR MI MU WM HK.
    awalk ltac:(fun pc => lazymatch pc with
      | 0x883a0%Z => first [ eapply evt_eq; [| eapply HK; eassumption]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_rel2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (mm : mem),
    ro_cells bsegs mm (f + 1016) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs mm fl [C1 (Z_to_bv 8 1)] ->
    mem_inv bsegs mm -> munch [(fl, fl + 1)]%Z m0 mm -> wmono bsegs m0 mm ->
    (forall (mm' : mem), rw_cells bsegs mm' fl [C1 (Z_to_bv 8 0)] ->
       mem_inv bsegs mm' -> munch [(fl, fl + 1)]%Z m0 mm' -> wmono bsegs m0 mm' ->
       evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xfb6f0) fc None mm' (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfb6d8) fc None mm (seg_rom bsegs)).
  Proof using FLO FLR.
    intros until mm. intros LAST FLAG MI MU WM HK.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xfb6f0%Z => first [ eapply evt_eq; [| eapply HK; eassumption]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End NDREL.

Section NDLEAVE.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 160 - d)%Z.
  Hypothesis ROOM : (lo + NDCB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Variable Q : machine_state -> Prop.

  Lemma nd_leave : forall jsp jh (r0 r1 : word) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
    rw_cells bsegs mm spq [CB 56 jsp] ->
    rw_cells bsegs mm (spq + 56) [CB (Z.to_nat d) jh] ->
    rw_cells bsegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk bsegs mm lo spq ->
    (forall yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6, stk bsegs mm lo SP ->
       evt bsegs Q (MS (mkR ra sp gp tp yt0 yt1 yt2 s0 s1 r0 r1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                       F (ret_pc ra) fc None mm (seg_rom bsegs))) ->
    evt bsegs Q
      (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 r1 r0 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xfb6f0) fc None mm (seg_rom bsegs)).
  Proof using SPQ ROOM TOP.
    intros until mm. intros SPILL HIGHc SAVED ST KRET.
    destruct SPQ as [Hd Hspq]. unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LM_SAVED in SAVED.
    do 18 zstep.
    eapply evt_eq; [| eapply KRET].
    - num_st_eq.
    - pose proof (stk_release bsegs mm lo spq _ ST SPILL ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 56) with 56%Z in S1.
      pose proof (stk_release bsegs mm lo (spq + 56) _ S1 HIGHc ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
      replace (spq + 56 + Z.of_nat (Z.to_nat d + 0))%Z with (SP + -104)%Z in S3 by lia.
      pose proof (stk_release bsegs mm lo (SP + -104) _ S3 SAVED ltac:(lia)) as S4. cbn [cells_size csize Nat.add] in S4.
      replace (SP + -104 + Z.of_nat 104)%Z with SP in S4 by lia. exact S4.
  Qed.
End NDLEAVE.
