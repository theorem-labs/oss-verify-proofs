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

Section LMPRO2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 256 - d)%Z.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.

  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6d2000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis XR : (0 <= X /\ X + 504 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Notation W2 := [(spq + 16, spq + 152); (f, f + 32); (S, S + 148)]%Z.

  Definition lm_c34_k : Prop :=
    forall xra xt0 xt1 xt2 xa4 xa5 xa7 xt3 xt5 xt6 ja0 ja1 jb0 jb1 jb2 h jz jzi (mm : mem),
      rw_cells asegs mm (spq + 16) [CB 56 ja0; C8 (Z_to_bv 64 f); CB 40 ja1; C8 (Z_to_bv 64 X); CB 8 jb0; CB 8 jb1; CB 8 jb2] ->
      rw_cells asegs mm f [CB 32 h] ->
      rw_cells asegs mm (f / 8 + 2147450884) (mk_CB_cells (repeat 1%nat 63) jz) ->
      rw_cells asegs mm (f / 8 + 2147450956) (mk_CB_cells (repeat 1%nat 63) jzi) ->
      mem_inv asegs mm -> munch W2 m0 mm -> wmono asegs m0 mm ->
      evt asegs Q
        (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-13)) (Z_to_bv 64 ((X + 496) / 8)) (Z_to_bv 64 (-14))
                 xa4 xa5 (Z_to_bv 64 (-8)) xa7 (Z_to_bv 64 f) (Z_to_bv 64 S) s4 (Z_to_bv 64 0x2fc20) s6 s7 s8 (Z_to_bv 64 5) (Z_to_bv 64 2147450880) s11
                 xt3 (Z_to_bv 64 X) xt5 xt6)
            F (Z_to_bv 64 0xee86c) fc None mm (seg_rom asegs)).

  Ltac cells_forget H k :=
    let j := fresh "j" in let Hf := fresh "Hf" in
    destruct (rw_cells_forget asegs _ _ _ H) as [j Hf]; cbn [cells_size csize Nat.add] in Hf; clear H;
    apply (rw_cells_split_CB asegs _ _ [] k j [] (repeat 1%nat k)) in Hf; [| reflexivity]; cbn [app] in Hf; rewrite ?app_nil_r in Hf; rename Hf into H.

  Lemma lm_poison : lm_c34_k -> forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 ja jb0 jb1 jb2 h jsh0 jz jsh1 jzi jsh2 (mm : mem),
    rw_cells asegs mm (spq + 16) [CB 104 ja; C8 (Z_to_bv 64 X); CB 8 jb0; CB 8 jb1; CB 8 jb2] ->
    rw_cells asegs mm f (mk_CB_cells [8;8;8;8]%nat h) ->
    rw_cells asegs mm S (mk_CB_cells (repeat 1%nat 4) jsh0) ->
    rw_cells asegs mm (f / 8 + 2147450884) (mk_CB_cells (repeat 1%nat 63) jz) ->
    rw_cells asegs mm (f / 8 + 2147450947) (mk_CB_cells (repeat 1%nat 9) jsh1) ->
    rw_cells asegs mm (f / 8 + 2147450956) (mk_CB_cells (repeat 1%nat 63) jzi) ->
    rw_cells asegs mm (f / 8 + 2147451019) (mk_CB_cells (repeat 1%nat 9) jsh2) ->
    mem_inv asegs mm -> munch W2 m0 mm -> wmono asegs m0 mm ->
    evt asegs Q
      (MS (mkR (Z_to_bv 64 0xee598) (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 f) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 (Z_to_bv 64 0x2fc20) s6 s7 s8 (Z_to_bv 64 5) (Z_to_bv 64 2147450880) s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xee598) fc None mm (seg_rom asegs)).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0 XR.
    intros KC. intros until mm. intros SPILL HDR SH0 SHZ SH1 SHZI SH2 MI MU WM.
    destruct SPQ as [Hd Hspq]. unfold LMA_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    cbn [mk_CB_cells repeat] in HDR, SH0, SHZ, SH1, SHZI, SH2.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    astep. astep. astep. astep.
    if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    awalk ltac:(fun pc => lazymatch pc with 0xee86c%Z => idtac end).
    cells_forget SHZ 63%nat. cells_forget SHZI 63%nat.
    destruct (rw_cells_forget asegs _ _ _ HDR) as [h' HDR']. cbn [cells_size csize Nat.add] in HDR'.
    eapply evt_eq; [| eapply KC; [exact SPILL | exact HDR' | exact SHZ | exact SHZI | exact MI | exact MU | exact WM]].
    num_st_eq.
  Qed.
End LMPRO2.
