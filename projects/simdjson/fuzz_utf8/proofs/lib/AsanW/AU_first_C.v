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
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface F_apoison F_annot.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac AU_first_A.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.

Ltac bt := let K := fresh "K" in if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
Ltac bf := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (V : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - 8192.
  Hypothesis LOC : ATOP <= lo.
  Hypothesis SPT : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis VH : ablk V (V + 8).
  Hypothesis V16 : V mod 16 = 0.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RV : rng RNG V 8.
  Hypothesis RSV : rng RNG (Z.shiftr V 3 + 2147450880) 1.
  Hypothesis RSS : rng RNG (Z.shiftr (SP + -160) 3 + 2147450880) 4.

  (* [comment removed for export] *)
  Definition shc (X : Z) (m : amem) : Prop := rw_cells asegs m (Z.shiftr X 3 + 2147450880) [C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Definition EBFR2 (c0 c1 c2 c3 : word) : list cell :=
    [C8 c0; C8 c1; C8 c2; C8 c3; C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 2148319912); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 0x6a1540);
     C8 (Z_to_bv 64 0x6a1548); C8 (Z_to_bv 64 0x6a1540); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 0xaff40)].
  Definition SWFR (j : list byte) : list cell :=
    [CB 8 j; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 0x6a1540); C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb0148)].
  Definition shc5 (m : amem) : Prop := shc V m /\ shc (SP + -160) m /\ shc (SP + -152) m /\ shc (SP + -144) m /\ shc (SP + -136) m.

  Ltac prep7 :=
    change (shad 0x6a1540) with 2148319912 in *; change (shad 0x6a1560) with 2148319916 in *; change (shad 0x160400) with 2147631232 in *;
    change (shad 0x6a1588) with 2148319921 in *; change (shad 0x6a13e8) with 2148319869 in *; change (shad 0x6a13f0) with 2148319870 in *;
    change (shad 0x6a13e0) with 2148319868 in *.

  (* [comment removed for export] *)
  Lemma rsi_c1 : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j (jv : list byte),
    stk asegs m lo (SP + -176) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m (SP + -176) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb00e8)] ->
    rw_cells asegs m (SP + -160) (EBFR j) ->
    rw_cells asegs m V [CB 8 jv] ->
    rw_cells asegs m AVEC [C8 w0; C8 w0; C8 w0] -> rw_cells asegs m 0x6a1540 [C8 (Z_to_bv 64 AFALLBACK)] ->
    shz7 m -> shc5 m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) j2,
        ms' = MS (mkR (Z_to_bv 64 0xb2ffc) (Z_to_bv 64 (SP + -208)) gp tp y5 y6 y7 (Z_to_bv 64 (SP + -160)) (Z_to_bv 64 AVEC)
                     (Z_to_bv 64 V) (Z_to_bv 64 0) (Z_to_bv 64 0) y13 y14 y15 y16 y17
                     (Z_to_bv 64 V) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148319869) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (Z_to_bv 64 AMEMCPY) fc None m' (seg_rom asegs)
        /\ munch [(SP - 224, SP - 128); (V, V + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -208)
        /\ rw_cells asegs m' (SP + -208) (SWFR j2)
        /\ rw_cells asegs m' (SP + -160) (EBFR2 (Z_to_bv 64 V) (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)))
        /\ rw_cells asegs m' V [C8 (Z_to_bv 64 AFALLBACK)]
        /\ rw_cells asegs m' AVEC [C8 w0; C8 w0; C8 w0] /\ rw_cells asegs m' 0x6a1540 [C8 (Z_to_bv 64 AFALLBACK)]
        /\ shz7 m' /\ shc5 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -176)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 0x6a1540) (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 2148319869) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb31f0) fc None m (seg_rom asegs)).
  Proof.
    intros until jv. intros ST MI GOT SHB FR1 FR0 VB VEC ARR (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3).
    unfold shc5, shz7, shc, shz, EBFR, EBFR2, SWFR, AVEC, AFALLBACK, AMEMCPY, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148338688 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148338688 <= Z.shiftr (SP + -160) 3 + 2147450880 /\ Z.shiftr (SP + -136) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -152) 3 = Z.shiftr (SP + -160) 3 + 1 /\ Z.shiftr (SP + -144) 3 = Z.shiftr (SP + -160) 3 + 2 /\ Z.shiftr (SP + -136) 3 = Z.shiftr (SP + -160) 3 + 3)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 224, SP - 128); (V, V + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply (rw_cells_split_CB asegs _ _ [] 32 j _ [8;8;8;8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    steps_to 0xb31fc. release_frame FR1 ST (SP + -160).
    steps_to 0xb2f78. zstep. carve_frame 48%nat ST.             (* [comment removed for export] *)
    steps_to 0xb2d88. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xb2dfc. release_frame FR2 ST (SP + -208).
    steps_to 0x7fba8. rewrite ?Z.sub_0_r.
    apply evtF_done. do 14 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact VB|]. split; [exact VEC|]. split; [exact ARR|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2| exact T3].
  Qed.

  (* [comment removed for export] *)
  Lemma rsi_c2 : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j2,
    stk asegs m lo (SP + -208) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m (SP + -208) (SWFR j2) ->
    rw_cells asegs m (SP + -160) (EBFR2 (Z_to_bv 64 V) (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8))) ->
    rw_cells asegs m AVEC [C8 w0; C8 w0; C8 w0] ->
    shz7 m -> shc5 m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = MS (mkR (Z_to_bv 64 0xb3268) (Z_to_bv 64 (SP + -176)) gp tp y5 y6 y7 (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 0x6a1540)
                     (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)) y14 y15 y16 y17
                     (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 2148319869) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (Z_to_bv 64 AANNOT) fc None m' (seg_rom asegs)
        /\ munch [(SP - 224, SP - 128); (AVEC, AVEC + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -176)
        /\ rw_cells asegs m' (SP + -176) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb0148)]
        /\ rw_cells asegs m' (SP + -160) (EBFR2 w0 w0 w0 w0)
        /\ rw_cells asegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
        /\ shz7 m' /\ shc5 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -208)) gp tp t0 t1 t2 (Z_to_bv 64 (SP + -160)) (Z_to_bv 64 AVEC)
               (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 V) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148319869) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb2ffc) fc None m (seg_rom asegs)).
  Proof.
    intros until j2. intros ST MI GOT SHB FR1 FR0 VEC (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3).
    unfold shc5, shz7, shc, shz, EBFR2, SWFR, RSIFR, AVEC, AFALLBACK, AMEMCPY, AANNOT, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148338688 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148338688 <= Z.shiftr (SP + -160) 3 + 2147450880 /\ Z.shiftr (SP + -136) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -152) 3 = Z.shiftr (SP + -160) 3 + 1 /\ Z.shiftr (SP + -144) 3 = Z.shiftr (SP + -160) 3 + 2 /\ Z.shiftr (SP + -136) 3 = Z.shiftr (SP + -160) 3 + 3)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 224, SP - 128); (6951904, 6951904 + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xb3094. replace (V + 8 - V) with 8 by lia. change (bv_signed (Z_to_bv 64 8)) with 8. change (Z.shiftr 8 3) with 1.
    steps_to 0xb30b0. release_frame FR1 ST (SP + -160).
    steps_to 0xb320c. zstep. carve_frame 16%nat ST.
    steps_to 0xb323c. zstep. bf. (* [comment removed for export] *)
    steps_to 0x83990.
    apply evtF_done. do 12 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact VEC|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2| exact T3].
  Qed.

  (* [comment removed for export] *)
  Lemma rsi_c3 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j,
    stk asegs m lo (SP + -176) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m (SP + -176) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb0148)] ->
    rw_cells asegs m (SP + -160) (EBFR2 w0 w0 w0 w0) ->
    rw_cells asegs m (SP + -64) (RSIFR ra s0 s1 s2 s3 s4 s5 j) ->
    rw_cells asegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    shz7 m -> shc5 m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(SP - 224, SP); (AVEC, AVEC + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo SP
        /\ rw_cells asegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
        /\ shz7 m' /\ shc5 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -176)) gp tp t0 t1 t2 (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 0x6a1540)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 2148319869) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb3268) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros ST MI GOT SHB FR1 FR0 FRR VEC (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3).
    unfold shc5, shz7, shc, shz, EBFR2, SWFR, RSIFR, AVEC, AFALLBACK, AMEMCPY, AANNOT, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148338688 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148338688 <= Z.shiftr (SP + -160) 3 + 2147450880 /\ Z.shiftr (SP + -136) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -152) 3 = Z.shiftr (SP + -160) 3 + 1 /\ Z.shiftr (SP + -144) 3 = Z.shiftr (SP + -160) 3 + 2 /\ Z.shiftr (SP + -136) 3 = Z.shiftr (SP + -160) 3 + 3)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 224, SP); (6951904, 6951904 + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xb3270. release_frame FR1 ST (SP + -160).
    steps_to 0xb30e4. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xb3190. release_frame FR1 ST (SP + -160).
    steps_to 0xb0188. release_frame FR0 ST (SP + -64).
    steps_to 0xaff7c. zstep. bf.                                (* [comment removed for export] *)
    steps_to 0xaff9c. release_frame FRR ST (bv_unsigned sp).
    zstep. zstep. (* [comment removed for export] *)
    apply evtF_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact VEC|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2| exact T3].
  Qed.
End S.
End CANSEC1.
