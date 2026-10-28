(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Definition fcb_saved (E : fcbenv) : list cell :=
  [C8 (q_s11 E); C8 (q_s10 E); C8 (q_s9 E); C8 (q_s8 E); C8 (q_s7 E); C8 (q_s6 E); C8 (q_s5 E); C8 (q_s4 E); C8 (q_s3 E); C8 (q_s2 E); C8 (q_s1 E);
   C8 (q_s0 E); C8 (q_ra E)].

Section FCBREL.
  Variables (f fl : Z) (m0 : mem).
  Hypothesis FLO : (0x6e0000 <= f /\ f + 1024 < 2^62)%Z.
  Hypothesis FLR : (0 < fl /\ fl + 1 < 2^62)%Z.
  Variable Q : machine_state -> Prop.

  Lemma fcb_rel2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (mm : mem),
    ro_cells bsegs mm (f + 1016) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs mm fl [C1 (Z_to_bv 8 1)] ->
    mem_inv bsegs mm -> munch [(fl, fl + 1)]%Z m0 mm -> wmono bsegs m0 mm ->
    (forall (mm' : mem), rw_cells bsegs mm' fl [C1 (Z_to_bv 8 0)] ->
       mem_inv bsegs mm' -> munch [(fl, fl + 1)]%Z m0 mm' -> wmono bsegs m0 mm' ->
       evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xf8c40) fc None mm' (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xf8c38) fc None mm (seg_rom bsegs)).
  Proof using FLO FLR.
    intros until mm. intros LAST FLAG MI MU WM HK.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xf8c40%Z => first [ eapply evt_eq; [| eapply HK; eassumption]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End FCBREL.

Section FCBLEAVE.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variable Q : machine_state -> Prop.
  Notation SP := (q_SP E).
  Notation spq := (q_spq E).

  Lemma fcb_leave : forall jsp jh (r0 r1 : word) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
    rw_cells bsegs mm spq [CB 152 jsp] ->
    rw_cells bsegs mm (spq + 152) [CB (Z.to_nat (SP - 256 - spq)) jh] ->
    rw_cells bsegs mm (SP + -104) (fcb_saved E) ->
    stk bsegs mm (q_lo E) spq ->
    (forall yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6, stk bsegs mm (q_lo E) SP ->
       evt bsegs Q (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) yt0 yt1 yt2 (q_s0 E) (q_s1 E) r0 r1 ya2 ya3 ya4 ya5 ya6 ya7
                            (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) yt3 yt4 yt5 yt6)
                       F (ret_pc (q_ra E)) fc None mm (seg_rom bsegs))) ->
    evt bsegs Q
      (MS (mkR xra (Z_to_bv 64 spq) (q_gp E) (q_tp E) xt0 xt1 xt2 (q_sp E) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 r0 r1 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xf8c40) fc None mm (seg_rom bsegs)).
  Proof using OK.
    intros until mm. intros SPILL HIGHc SAVED ST KRET.
    pose proof OK as OK'. fcb_env OK'. destruct SPQ as [Hspq _]. unfold fcb_saved in SAVED.
    do 18 zstep.
    eapply evt_eq; [| eapply KRET].
    - num_st_eq.
    - pose proof (stk_release bsegs mm (q_lo E) spq _ ST SPILL ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 152) with 152%Z in S1.
      pose proof (stk_release bsegs mm (q_lo E) (spq + 152) _ S1 HIGHc ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
      replace (spq + 152 + Z.of_nat (Z.to_nat (SP - 256 - spq) + 0))%Z with (SP + -104)%Z in S3 by lia.
      pose proof (stk_release bsegs mm (q_lo E) (SP + -104) _ S3 SAVED ltac:(lia)) as S4. cbn [cells_size csize Nat.add] in S4.
      replace (SP + -104 + Z.of_nat 104)%Z with SP in S4 by lia. exact S4.
  Qed.
End FCBLEAVE.
