(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_pro Sj_num_lm_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FCREL.
  Variables (f fl : Z) (m0 : mem).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6d2000 <= f /\ f + 1024 < 2^62)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 < 2^62)%Z.
  Hypothesis FLR : (0 < fl /\ fl + 1 < 2^62)%Z.
  Variable Q : machine_state -> Prop.

  Lemma fc_rel1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc h0 h1 jp (mm : mem),
    rw_cells asegs mm f [CB 8 h0; CB 24 h1] -> rw_cells asegs mm (f / 8 + 2147450956) [CB 9 jp] ->
    mem_inv asegs mm -> munch [(f, f + 8); (f / 8 + 2147450956, f / 8 + 2147450965)]%Z m0 mm -> wmono asegs m0 mm ->
    (forall jp' (mm' : mem), rw_cells asegs mm' f [C8 (Z_to_bv 64 1172321806); CB 24 h1] -> rw_cells asegs mm' (f / 8 + 2147450956) [CB 9 jp'] ->
       mem_inv asegs mm' -> munch [(f, f + 8); (f / 8 + 2147450956, f / 8 + 2147450965)]%Z m0 mm' -> wmono asegs m0 mm' ->
       evt asegs Q (MS (mkR (Z_to_bv 64 0xeb470) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 128) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 S) s5 s6 s7 s8 s9
                        s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x881e4) fc None mm' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 S) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xeb42c) fc None mm (seg_rom asegs)).
  Proof using F64 FLO FSH FS0.
    intros until mm. intros HDR SHP MI MU WM HK.
    apply (rw_cells_split_CB asegs _ _ [] 9 jp [] (repeat 1%nat 9)) in SHP; [| reflexivity]. cbn [app] in SHP. rewrite app_nil_r in SHP.
    cbn [mk_CB_cells repeat] in SHP.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    pose proof (f64_8 f F64) as F8.
    awalk ltac:(fun pc => lazymatch pc with
      | 0x881e4%Z => first [ pose proof (rw_cells_merge_all _ _ _ SHP) as SHP'; eapply evt_eq; [| eapply HK; eassumption]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_rel2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (mm : mem),
    ro_cells asegs mm (f + 1016) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs mm fl [C1 (Z_to_bv 8 1)] ->
    mem_inv asegs mm -> munch [(fl, fl + 1)]%Z m0 mm -> wmono asegs m0 mm ->
    (forall (mm' : mem), rw_cells asegs mm' fl [C1 (Z_to_bv 8 0)] ->
       mem_inv asegs mm' -> munch [(fl, fl + 1)]%Z m0 mm' -> wmono asegs m0 mm' ->
       evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xeb488) fc None mm' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xeb470) fc None mm (seg_rom asegs)).
  Proof using F64 FLO FSH FS0 FLR.
    intros until mm. intros LAST FLAG MI MU WM HK.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xeb488%Z => first [ eapply evt_eq; [| eapply HK; eassumption]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End FCREL.

Section FCLEAVE.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 192 - d)%Z.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Variable Q : machine_state -> Prop.

  Lemma fc_leave : forall jsp jh (r0 r1 : word) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
    rw_cells asegs mm spq [CB 88 jsp] ->
    rw_cells asegs mm (spq + 88) [CB (Z.to_nat d) jh] ->
    rw_cells asegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs mm lo spq ->
    (forall yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6, stk asegs mm lo SP ->
       evt asegs Q (MS (mkR ra sp gp tp yt0 yt1 yt2 s0 s1 r0 r1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                       F (ret_pc ra) fc None mm (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 r1 r0 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xeb488) fc None mm (seg_rom asegs)).
  Proof using SPQ ROOM TOP.
    intros until mm. intros SPILL HIGHc SAVED ST KRET.
    destruct SPQ as [Hd Hspq]. unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LM_SAVED in SAVED.
    do 18 zstep.
    eapply evt_eq; [| eapply KRET].
    - num_st_eq.
    - pose proof (stk_release asegs mm lo spq _ ST SPILL ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 88) with 88%Z in S1.
      pose proof (stk_release asegs mm lo (spq + 88) _ S1 HIGHc ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
      replace (spq + 88 + Z.of_nat (Z.to_nat d + 0))%Z with (SP + -104)%Z in S3 by lia.
      pose proof (stk_release asegs mm lo (SP + -104) _ S3 SAVED ltac:(lia)) as S4. cbn [cells_size csize Nat.add] in S4.
      replace (SP + -104 + Z.of_nat 104)%Z with SP in S4 by lia. exact S4.
  Qed.
End FCLEAVE.
