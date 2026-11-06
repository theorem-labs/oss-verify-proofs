(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
Section CANSEC1. Context {rc : runConstT}.
Definition ARSI : Z := 0xafd04.          (* [comment removed for export] *)
Definition AMEMSET_FN : Z := 0x7fe90.    (* [comment removed for export] *)

Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - 8192.
  Hypothesis LOC : ATOP <= lo.
  Hypothesis SPT : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.

  (* [comment removed for export] *)
  Definition RSIFR (j1 j2 : list byte) : list cell :=
    [CB 8 j1; C8 (Z_to_bv 64 2147450880); CB 8 j2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma rsi_a1 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m -> rt_got m -> rt_shbase m ->
    evtF bsegs RNG (fun ms' => exists m' j1 j2,
        ms' = MS (mkR (Z_to_bv 64 0xafd64) (Z_to_bv 64 (SP + -128)) gp tp t0 t1 t2 (Z_to_bv 64 AVEC) s1 (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 AMEMSET_FN) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 128, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -128) (RSIFR j1 j2) /\ stk bsegs m' lo (SP + -128))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AVEC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 ARSI) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB. unfold ARSI, AMEMSET_FN, AVEC in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 128, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. carve_frame 128%nat ST.
    steps_to 0x7fe90.
    apply evtF_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact FR0| exact ST].
  Qed.
  (* [comment removed for export] *)
  Definition shz (X : Z) (m : amem) : Prop := rw_cells bsegs m (shad X) [C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Definition simdjson_statics (m : amem) : Prop :=
       rw_cells bsegs m 0x6ad860 guard1 /\ rw_cells bsegs m 0x6ad880 [C8 (Z_to_bv 64 0x6ad8c0); C8 (Z_to_bv 64 1)] /\ rw_cells bsegs m 0x6ad8a0 guard1
    /\ rw_cells bsegs m 0x6ad8c0 [C8 (Z_to_bv 64 AFALLBACK)]
    /\ rw_cells bsegs m AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT); C8 (Z_to_bv 64 0x28420); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0x28620); C8 (Z_to_bv 64 0x1f); C4 w0]
    /\ rw_cells bsegs m 0x6ad940 guard1.
  Definition shz7 (m : amem) : Prop :=
    shz 0x6ad8c0 m /\ shz 0x6ad8e0 m /\ shz 0x16c340 m /\ shz 0x6ad908 m /\ shz 0x6ad768 m /\ shz 0x6ad770 m /\ shz 0x6ad760 m.
  (* [comment removed for export] *)
  Definition RSI_IMGW : list (Z * Z) :=
    [(0x6ad860, 0x6ad862); (0x6ad880, 0x6ad890); (0x6ad8a0, 0x6ad8a2); (0x6ad8c0, 0x6ad8c8); (0x6ad8e0, 0x6ad90c); (0x6ad940, 0x6ad942)].
  (* [comment removed for export] *)
  Definition shc (X : Z) (m : amem) : Prop := rw_cells bsegs m (Z.shiftr X 3 + 2147450880) [C1 (Z_to_bv 8 0)].
  Definition shs5 (m : amem) : Prop := shc (SP + -216) m /\ shc (SP + -208) m /\ shc (SP + -200) m /\ shc (SP + -192) m /\ shc (SP + -184) m.
  Hypothesis RSS : rng RNG (Z.shiftr (SP + -216) 3 + 2147450880) 5.

  (* [comment removed for export] *)
  Definition EBFR (j : list byte) : list cell :=
    [CB 32 j; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 (AVEC + 16)); C8 (Z_to_bv 64 0x6ad8c8); C8 (Z_to_bv 64 0x6ad8c0);
     C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 0xafe20)].
  (* [comment removed for export] *)
  Definition SBFR (j : list byte) : list cell :=
    [CB 8 j; C8 (Z_to_bv 64 0x6ad8c0); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 2148326125); C8 (Z_to_bv 64 0x6ad8c0);
     C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb3078)].

  (* [comment removed for export] *)
  Lemma rsi_a2 : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j1 j2,
    stk bsegs m lo (SP + -128) -> mem_inv bsegs m -> rt_got m -> rt_shbase m ->
    rw_cells bsegs m (SP + -128) (RSIFR j1 j2) ->
    rw_cells bsegs m AVEC [C8 w0; C8 w0; C8 w0] ->
    rw_cells bsegs m 0x6ad860 guard0 -> rw_cells bsegs m 0x6ad880 [C8 w0; C8 w0] -> rw_cells bsegs m 0x6ad8a0 guard0 ->
    rw_cells bsegs m 0x6ad8c0 [C8 w0] ->
    rw_cells bsegs m AFALLBACK [C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C4 w0] -> rw_cells bsegs m 0x6ad940 guard0 ->
    rw_cells bsegs m AVTAB_SRS [C8 (Z_to_bv 64 ASRS_FN)] ->
    shz7 m -> shs5 m ->
    evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) j js,
        ms' = MS (mkR (Z_to_bv 64 0xb3368) (Z_to_bv 64 (SP + -288)) gp tp y5 y6 y7 (Z_to_bv 64 (SP + -192)) (Z_to_bv 64 1) (Z_to_bv 64 8) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 (SP + -216)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (SP + -192) 3 + 2147450880)) (Z_to_bv 64 2147450880)
                     (Z_to_bv 64 2148326126) (Z_to_bv 64 0) (Z_to_bv 64 (-8)) (Z_to_bv 64 0) (Z_to_bv 64 2148326168) (Z_to_bv 64 2148326125) y28 y29 y30 y31)
                 FR (Z_to_bv 64 0x16adc4) fc None m' (seg_rom bsegs)
        /\ munch ((SP - 304, SP - 128) :: RSI_IMGW) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo (SP + -288)
        /\ rw_cells bsegs m' (SP + -288) (SBFR js)
        /\ rw_cells bsegs m' (SP + -224) (EBFR j)
        /\ rw_cells bsegs m' (SP + -128) (RSIFR j1 j2)
        /\ rw_cells bsegs m' AVEC [C8 w0; C8 w0; C8 w0] /\ simdjson_statics m'
        /\ rw_cells bsegs m' AVTAB_SRS [C8 (Z_to_bv 64 ASRS_FN)] /\ shz7 m' /\ shs5 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp t0 t1 t2 (Z_to_bv 64 AVEC) s1 (Z_to_bv 64 AVEC) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xafd64) fc None m (seg_rom bsegs)).
  Proof.
    intros until j2. intros ST MI GOT SHB FRR VEC G1 IL G2 ARR SGL G3 VT (S1 & S2 & S3 & S4 & S5 & S6 & S7) (T0 & T1 & T2 & T3 & T4).
    unfold shz7, shs5, simdjson_statics, EBFR, SBFR, RSIFR, RSI_IMGW, shz, shc, AVEC, AFALLBACK, AFALLBACK_VT, AVTAB_SRS, ASRS_FN, guard0, guard1, w0 in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    change (shad 0x6ad8c0) with 2148326168 in *. change (shad 0x6ad8e0) with 2148326172 in *. change (shad 0x16c340) with 2147637352 in *. change (shad 0x6ad908) with 2148326177 in *. change (shad 0x6ad768) with 2148326125 in *. change (shad 0x6ad770) with 2148326126 in *. change (shad 0x6ad760) with 2148326124 in *.
    assert (BSS : 2148344832 <= Z.shiftr (SP + -216) 3 + 2147450880 /\ Z.shiftr (SP + -184) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -208) 3 = Z.shiftr (SP + -216) 3 + 1 /\ Z.shiftr (SP + -200) 3 = Z.shiftr (SP + -216) 3 + 2
                  /\ Z.shiftr (SP + -192) 3 = Z.shiftr (SP + -216) 3 + 3 /\ Z.shiftr (SP + -184) 3 = Z.shiftr (SP + -216) 3 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 304, SP - 128); (0x6ad860, 0x6ad862); (0x6ad880, 0x6ad890); (0x6ad8a0, 0x6ad8a2); (0x6ad8c0, 0x6ad8c8); (0x6ad8e0, 0x6ad90c); (0x6ad940, 0x6ad942)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    zstep. (* [comment removed for export] *)
    zstep. carve_frame 16%nat ST.
    steps_to 0xb4970. release_frame FR0 ST (SP + -128).        (* [comment removed for export] *)
    steps_to 0xb45e4. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xe8d34. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xe8db8. release_frame FR1 ST (SP + -144).
    steps_to 0xb466c. release_frame FR0 ST (SP + -128).
    steps_to 0xb4674. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xb46d4. release_frame FR0 ST (SP + -128).
    steps_to 0xb4584. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xe881c. zstep. carve_frame 16%nat ST.
    steps_to 0xe884c. release_frame FR1 ST (SP + -144).
    steps_to 0xb45d0. release_frame FR0 ST (SP + -128).
    steps_to 0xb2fc0. zstep. carve_frame 96%nat ST.             (* [comment removed for export] *)
    steps_to 0xb32f0. zstep. carve_frame 64%nat ST.             (* [comment removed for export] *)
    steps_to 0xb37ac. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xb37c4. release_frame FR2 ST (SP + -288).         (* [comment removed for export] *)
    steps_to 0x16adc4.
    apply evtF_done. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact FRR|]. split; [exact VEC|].
    split. { split; [exact G1|]. split; [exact IL|]. split; [exact G2|]. split; [exact ARR|]. split; [exact SGL| exact G3]. }
    split; [exact VT|]. split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact T0|]. split; [exact T1|]. split; [exact T2|]. split; [exact T3| exact T4].
  Qed.
End S.
End CANSEC1.
