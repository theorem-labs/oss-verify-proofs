(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_pro Sj_num_lm_kit Sj_num_lm_runs.
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

Section LMLEAVE2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 224 - d)%Z.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Variable Q : machine_state -> Prop.

  Lemma lm_leave2 : forall (spill : list cell) jh (res : word) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
    rw_cells bsegs mm spq spill -> cells_size spill = 120%nat ->
    rw_cells bsegs mm (spq + 120) [CB (Z.to_nat d) jh] ->
    rw_cells bsegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk bsegs mm lo spq ->
    (forall yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6, stk bsegs mm lo SP ->
       evt bsegs Q (MS (mkR ra sp gp tp yt0 yt1 yt2 s0 s1 res ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                       F (ret_pc ra) fc None mm (seg_rom bsegs))) ->
    evt bsegs Q
      (MS (mkR (Z_to_bv 64 0xedb04) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 res xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xedb04) fc None mm (seg_rom bsegs)).
  Proof using SPQ ROOM TOP.
    intros until mm. intros SPILL SPSZ HIGHc SAVED ST KRET.
    destruct SPQ as [Hd Hspq]. unfold LMB_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LM_SAVED in SAVED.
    do 18 zstep.
    eapply evt_eq; [| eapply KRET].
    - num_st_eq.
    - pose proof (stk_release bsegs mm lo spq _ ST SPILL ltac:(lia)) as S2. rewrite SPSZ in S2. change (Z.of_nat 120) with 120%Z in S2.
      pose proof (stk_release bsegs mm lo (spq + 120) _ S2 HIGHc ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
      replace (spq + 120 + Z.of_nat (Z.to_nat d + 0))%Z with (SP + -104)%Z in S3 by lia.
      pose proof (stk_release bsegs mm lo (SP + -104) _ S3 SAVED ltac:(lia)) as S4. cbn [cells_size csize Nat.add] in S4.
      replace (SP + -104 + Z.of_nat 104)%Z with SP in S4 by lia. exact S4.
  Qed.
End LMLEAVE2.

Section LMLEAVE1.
  Variables (sp gp tp : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 224 - d)%Z.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6cd000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Notation W3 := [(f, f + 8); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.

  Definition lm_free_k (res : word) : Prop :=
    forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 h' jz' (mm : mem),
      rw_cells bsegs mm f [C8 (Z_to_bv 64 1172321806); CB 24 h'] ->
      rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz'] ->
      mem_inv bsegs mm -> munch W3 m0 mm -> wmono bsegs m0 mm ->
      evt bsegs Q
        (MS (mkR (Z_to_bv 64 0xedb04) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 f) (Z_to_bv 64 1184) xa2 xa3 xa4 xa5 xa6 xa7
                 xs2 (Z_to_bv 64 S) (Z_to_bv 64 X) xs5 xs6 (Z_to_bv 64 2147450880) res xs9 xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x64ecc) fc None mm (seg_rom bsegs)).

  Lemma lm_leave1 : forall (res : word), lm_free_k res -> forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs5 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 ja jb h0 h1 jz (mm : mem),
    rw_cells bsegs mm spq [CB 48 ja; C8 (Z_to_bv 64 f); CB 64 jb] ->
    rw_cells bsegs mm f [CB 8 h0; CB 24 h1] ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    mem_inv bsegs mm -> munch W3 m0 mm -> wmono bsegs m0 mm ->
    evt bsegs Q
      (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 f) xa6 xa7
               xs2 (Z_to_bv 64 S) (Z_to_bv 64 X) xs5 xs6 (Z_to_bv 64 2147450880) res xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xed9e8) fc None mm (seg_rom bsegs)).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0.
    intros res KC. intros until mm. intros SPILL HDR SHZ MI MU WM.
    destruct SPQ as [Hd Hspq]. unfold LMB_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    astep.
    num_cur_mem ltac:(fun m1 => eapply (lm_run5 f m1 ltac:(lia) Q); [exact SHZ | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI SHZ; intros jz' mm' SHZ MI MU' WM'; transport_after_call bsegs m1 mm' MU' WM'; clear MU' WM').
    awalk ltac:(fun pc => lazymatch pc with 0xedaf8%Z => idtac end).
    astep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    astep. astep.
    eapply evt_eq; [| eapply KC; [exact HDR | exact SHZ | exact MI | exact MU | exact WM]].
    num_st_eq.
  Qed.
End LMLEAVE1.
