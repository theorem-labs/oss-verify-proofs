(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_pro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMLEAVE2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 256 - d)%Z.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Variable Q : machine_state -> Prop.

  Lemma lm_leave2 : forall (spill : list cell) jl jh (res : word) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
    rw_cells asegs mm spq [CB 16 jl] -> rw_cells asegs mm (spq + 16) spill -> cells_size spill = 136%nat ->
    rw_cells asegs mm (spq + 152) [CB (Z.to_nat d) jh] ->
    rw_cells asegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs mm lo spq ->
    (forall yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6, stk asegs mm lo SP ->
       evt asegs Q (MS (mkR ra sp gp tp yt0 yt1 yt2 s0 s1 res ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                       F (ret_pc ra) fc None mm (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR (Z_to_bv 64 0xe2abc) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 res xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xe2abc) fc None mm (seg_rom asegs)).
  Proof using SPQ ROOM TOP.
    intros until mm. intros LOWc SPILL SPSZ HIGHc SAVED ST KRET.
    destruct SPQ as [Hd Hspq]. unfold LMA_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LM_SAVED in SAVED.
    do 18 zstep.
    eapply evt_eq; [| eapply KRET].
    - num_st_eq.
    - pose proof (stk_release asegs mm lo spq _ ST LOWc ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 16) with 16%Z in S1.
      pose proof (stk_release asegs mm lo (spq + 16) _ S1 SPILL ltac:(lia)) as S2. rewrite SPSZ in S2. change (Z.of_nat 136) with 136%Z in S2.
      replace (spq + 16 + 136)%Z with (spq + 152)%Z in S2 by lia.
      pose proof (stk_release asegs mm lo (spq + 152) _ S2 HIGHc ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
      replace (spq + 152 + Z.of_nat (Z.to_nat d + 0))%Z with (SP + -104)%Z in S3 by lia.
      pose proof (stk_release asegs mm lo (SP + -104) _ S3 SAVED ltac:(lia)) as S4. cbn [cells_size csize Nat.add] in S4.
      replace (SP + -104 + Z.of_nat 104)%Z with SP in S4 by lia. exact S4.
  Qed.
End LMLEAVE2.

Section LMLEAVE1.
  Variables (sp gp tp s2 s4 s5 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 256 - d)%Z.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6c2000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Notation W3 := [(f, f + 8); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.

  Definition lm_free_k : Prop :=
    forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (res : word) xt3 xt4 xt5 xt6 h' jz' (mm : mem),
      rw_cells asegs mm f [C8 (Z_to_bv 64 1172321806); CB 24 h'] ->
      rw_cells asegs mm (f / 8 + 2147450884) (mk_CB_cells (repeat 1%nat 63) jz') ->
      mem_inv asegs mm -> munch W3 m0 mm -> wmono asegs m0 mm ->
      evt asegs Q
        (MS (mkR (Z_to_bv 64 0xe2abc) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 f) (Z_to_bv 64 1184) xa2 xa3 xa4 xa5 xa6 xa7
                 s2 xs3 s4 s5 res s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x6572c) fc None mm (seg_rom asegs)).

  Ltac cells_forget H k :=
    let j := fresh "j" in let Hf := fresh "Hf" in
    destruct (rw_cells_forget asegs _ _ _ H) as [j Hf]; cbn [cells_size csize Nat.add] in Hf; clear H;
    apply (rw_cells_split_CB asegs _ _ [] k j [] (repeat 1%nat k)) in Hf; [| reflexivity]; cbn [app] in Hf; rewrite ?app_nil_r in Hf; rename Hf into H.

  Lemma lm_leave1 : lm_free_k -> forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (res : word) xt3 xt4 xt5 xt6 ja0 ja1 h jz (mm : mem),
    rw_cells asegs mm (spq + 16) [CB 56 ja0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 64 ja1] ->
    rw_cells asegs mm f [CB 8 (firstn 8 h); CB 24 (skipn 8 h)] ->
    rw_cells asegs mm (f / 8 + 2147450884) (mk_CB_cells (repeat 1%nat 63) jz) ->
    mem_inv asegs mm -> munch W3 m0 mm -> wmono asegs m0 mm ->
    evt asegs Q
      (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 (Z_to_bv 64 S) s4 s5 res s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xe299c) fc None mm (seg_rom asegs)).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0.
    intros KC. intros until mm. intros SPILL HDR SHZ MI MU WM.
    destruct SPQ as [Hd Hspq]. unfold LMA_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    cbn [mk_CB_cells repeat] in SHZ.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    awalk ltac:(fun pc => lazymatch pc with 0xe2ab4%Z => idtac end).
    astep. astep.
    cells_forget SHZ 63%nat.
    eapply evt_eq; [| eapply KC; [exact HDR | exact SHZ | exact MI | exact MU | exact WM]].
    num_st_eq.
  Qed.
End LMLEAVE1.
