(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface F_apoison F_annot.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac AU_first_A.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
    [C8 c0; C8 c1; C8 c2; C8 c3; C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 2148320628); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 0x6a2ba0);
     C8 (Z_to_bv 64 0x6a2ba8); C8 (Z_to_bv 64 0x6a2ba0); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 0xb0ee0)].
  Definition SWFR (j : list byte) : list cell :=
    [CB 8 j; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 0x6a2ba0); C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb10e8)].
  Definition shc5 (m : amem) : Prop := shc V m /\ shc (SP + -160) m /\ shc (SP + -152) m /\ shc (SP + -144) m /\ shc (SP + -136) m.

  Ltac prep7 :=
    change (shad 0x6a2ba0) with 2148320628 in *; change (shad 0x6a2bc0) with 2148320632 in *; change (shad 0x161360) with 2147631724 in *;
    change (shad 0x6a2be8) with 2148320637 in *; change (shad 0x6a2a48) with 2148320585 in *; change (shad 0x6a2a50) with 2148320586 in *;
    change (shad 0x6a2a40) with 2148320584 in *.

  (* [comment removed for export] *)
  Lemma rsi_c1 : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j (jv : list byte),
    stk asegs m lo (SP + -176) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m (SP + -176) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb1088)] ->
    rw_cells asegs m (SP + -160) (EBFR j) ->
    rw_cells asegs m V [CB 8 jv] ->
    rw_cells asegs m AVEC [C8 w0; C8 w0; C8 w0] -> rw_cells asegs m 0x6a2ba0 [C8 (Z_to_bv 64 AFALLBACK)] ->
    shz7 m -> shc5 m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) j2,
        ms' = MS (mkR (Z_to_bv 64 0xb4110) (Z_to_bv 64 (SP + -208)) gp tp y5 y6 y7 (Z_to_bv 64 (SP + -160)) (Z_to_bv 64 AVEC)
                     (Z_to_bv 64 V) (Z_to_bv 64 0) (Z_to_bv 64 0) y13 y14 y15 y16 y17
                     (Z_to_bv 64 V) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148320585) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (Z_to_bv 64 AMEMCPY) fc None m' (seg_rom asegs)
        /\ munch [(SP - 224, SP - 128); (V, V + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -208)
        /\ rw_cells asegs m' (SP + -208) (SWFR j2)
        /\ rw_cells asegs m' (SP + -160) (EBFR2 (Z_to_bv 64 V) (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)))
        /\ rw_cells asegs m' V [C8 (Z_to_bv 64 AFALLBACK)]
        /\ rw_cells asegs m' AVEC [C8 w0; C8 w0; C8 w0] /\ rw_cells asegs m' 0x6a2ba0 [C8 (Z_to_bv 64 AFALLBACK)]
        /\ shz7 m' /\ shc5 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -176)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 0x6a2ba0) (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 2148320585) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb4304) fc None m (seg_rom asegs)).
  Proof.
    intros until jv. intros ST MI GOT SHB FR1 FR0 VB VEC ARR (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3).
    unfold shc5, shz7, shc, shz, EBFR, EBFR2, SWFR, AVEC, AFALLBACK, AMEMCPY, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148339200 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148339200 <= Z.shiftr (SP + -160) 3 + 2147450880 /\ Z.shiftr (SP + -136) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -152) 3 = Z.shiftr (SP + -160) 3 + 1 /\ Z.shiftr (SP + -144) 3 = Z.shiftr (SP + -160) 3 + 2 /\ Z.shiftr (SP + -136) 3 = Z.shiftr (SP + -160) 3 + 3)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 224, SP - 128); (V, V + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply (rw_cells_split_CB asegs _ _ [] 32 j _ [8;8;8;8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    steps_to 0xb4310. release_frame FR1 ST (SP + -160).
    steps_to 0xb408c. zstep. carve_frame 48%nat ST.             (* [comment removed for export] *)
    steps_to 0xb3e9c. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xb3f10. release_frame FR2 ST (SP + -208).
    steps_to 0x80b48. rewrite ?Z.sub_0_r.
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
        ms' = MS (mkR (Z_to_bv 64 0xb437c) (Z_to_bv 64 (SP + -176)) gp tp y5 y6 y7 (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 0x6a2ba0)
                     (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)) y14 y15 y16 y17
                     (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 2148320585) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (Z_to_bv 64 AANNOT) fc None m' (seg_rom asegs)
        /\ munch [(SP - 224, SP - 128); (AVEC, AVEC + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -176)
        /\ rw_cells asegs m' (SP + -176) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb10e8)]
        /\ rw_cells asegs m' (SP + -160) (EBFR2 w0 w0 w0 w0)
        /\ rw_cells asegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
        /\ shz7 m' /\ shc5 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -208)) gp tp t0 t1 t2 (Z_to_bv 64 (SP + -160)) (Z_to_bv 64 AVEC)
               (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 V) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148320585) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb4110) fc None m (seg_rom asegs)).
  Proof.
    intros until j2. intros ST MI GOT SHB FR1 FR0 VEC (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3).
    unfold shc5, shz7, shc, shz, EBFR2, SWFR, RSIFR, AVEC, AFALLBACK, AMEMCPY, AANNOT, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148339200 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148339200 <= Z.shiftr (SP + -160) 3 + 2147450880 /\ Z.shiftr (SP + -136) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -152) 3 = Z.shiftr (SP + -160) 3 + 1 /\ Z.shiftr (SP + -144) 3 = Z.shiftr (SP + -160) 3 + 2 /\ Z.shiftr (SP + -136) 3 = Z.shiftr (SP + -160) 3 + 3)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 224, SP - 128); (6957632, 6957632 + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xb41a8. replace (V + 8 - V) with 8 by lia. change (bv_signed (Z_to_bv 64 8)) with 8. change (Z.shiftr 8 3) with 1.
    steps_to 0xb41c4. release_frame FR1 ST (SP + -160).
    steps_to 0xb4320. zstep. carve_frame 16%nat ST.
    steps_to 0xb4350. zstep. bf. (* [comment removed for export] *)
    steps_to 0x84930.
    apply evtF_done. do 12 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact VEC|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2| exact T3].
  Qed.

  (* [comment removed for export] *)
  Lemma rsi_c3 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j,
    stk asegs m lo (SP + -176) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m (SP + -176) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb10e8)] ->
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
      (MS (mkR x1 (Z_to_bv 64 (SP + -176)) gp tp t0 t1 t2 (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 0x6a2ba0)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 2148320585) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb437c) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros ST MI GOT SHB FR1 FR0 FRR VEC (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3).
    unfold shc5, shz7, shc, shz, EBFR2, SWFR, RSIFR, AVEC, AFALLBACK, AMEMCPY, AANNOT, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148339200 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148339200 <= Z.shiftr (SP + -160) 3 + 2147450880 /\ Z.shiftr (SP + -136) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -152) 3 = Z.shiftr (SP + -160) 3 + 1 /\ Z.shiftr (SP + -144) 3 = Z.shiftr (SP + -160) 3 + 2 /\ Z.shiftr (SP + -136) 3 = Z.shiftr (SP + -160) 3 + 3)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 224, SP); (6957632, 6957632 + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xb4384. release_frame FR1 ST (SP + -160).
    steps_to 0xb41f8. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xb42a4. release_frame FR1 ST (SP + -160).
    steps_to 0xb1128. release_frame FR0 ST (SP + -64).
    steps_to 0xb0f1c. zstep. bf.                                (* [comment removed for export] *)
    steps_to 0xb0f3c. release_frame FRR ST (bv_unsigned sp).
    zstep. zstep. (* [comment removed for export] *)
    apply evtF_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact VEC|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2| exact T3].
  Qed.
End S.
End CANSEC1.
