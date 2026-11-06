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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac AU_first_A AU_first_C.
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
Definition AOPDEL_SZ_PC : Z := 0x1018b8.   (* [comment removed for export] *)

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
  Hypothesis RSS : rng RNG (Z.shiftr (SP + -16) 3 + 2147450880) 1.

  Definition shv3 (m : amem) : Prop := shz 0x6a2a48 m /\ shz 0x6a2a50 m /\ shz 0x6a2a40 m.
  (* [comment removed for export] *)
  Definition THFR : list cell := [C8 (Z_to_bv 64 AVEC); C8 ra].
  Definition DVFR : list cell := [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 0xb11a8)].

  (* [comment removed for export] *)
  Notation DST pc mm x1 spv x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 (SP + -16)) (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr (SP + -16) 3 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma vd_a : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo SP -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    shv3 m -> shc (SP + -16) m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = DST AANNOT m' (Z_to_bv 64 0xb3fb0) (SP + -64) y5 y6 y7 (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) y14 y15 y16 y17 y28 y29 y30 y31
        /\ munch [(SP - 64, SP); (AVEC, AVEC + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -64)
        /\ rw_cells asegs m' (SP + -64) [C8 (Z_to_bv 64 (SP + -16)); C8 (Z_to_bv 64 0xb3df0)]
        /\ rw_cells asegs m' (SP + -48) DVFR /\ rw_cells asegs m' (SP + -16) THFR
        /\ rw_cells asegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8))]
        /\ shv3 m' /\ shc (SP + -16) m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AVEC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 ADTOR_THUNK) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI GOT SHB VEC (S5 & S6 & S7) T0.
    unfold shv3, shz, shc, THFR, DVFR in *. unfold AVEC, ADTOR_THUNK, AANNOT in *.
    change (shad 0x6a2a48) with 2148320585 in *. change (shad 0x6a2a50) with 2148320586 in *. change (shad 0x6a2a40) with 2148320584 in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSS : 2148339200 <= Z.shiftr (SP + -16) 3 + 2147450880 /\ Z.shiftr (SP + -16) 3 + 2147450880 + 1 <= 17594333495296)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 64, SP); (6957632, 6957632 + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. carve_frame 16%nat ST.
    steps_to 0xb3d78. zstep. carve_frame 32%nat ST.
    steps_to 0xb3dc4. zstep. bf. (* [comment removed for export] *)
    steps_to 0xb3de8. replace (V + 8 - V) with 8 by lia. change (bv_signed (Z_to_bv 64 8)) with 8.
    steps_to 0xb3f3c. zstep. carve_frame 16%nat ST.
    steps_to 0xb3f68. zstep. bf.
    steps_to 0x84930.
    apply evtF_done. do 12 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR2|]. split; [exact FR1|]. split; [exact FR0|]. split; [exact VEC|]. split; [split; [exact S5| split; [exact S6| exact S7]]| exact T0].
  Qed.

  (* [comment removed for export] *)
  Lemma vd_b : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
    stk asegs m lo (SP + -64) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m (SP + -64) [C8 (Z_to_bv 64 (SP + -16)); C8 (Z_to_bv 64 0xb3df0)] ->
    rw_cells asegs m (SP + -16) THFR ->
    rw_cells asegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8))] ->
    shv3 m -> shc (SP + -16) m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = DST AANNOT m' (Z_to_bv 64 0xb3f08) (SP + -64) y5 y6 y7 (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) y14 y15 y16 y17 y28 y29 y30 y31
        /\ munch [(SP - 64, SP - 48)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -64)
        /\ rw_cells asegs m' (SP + -64) [C8 (Z_to_bv 64 (SP + -16)); C8 (Z_to_bv 64 0xb3e00)]
        /\ rw_cells asegs m' (SP + -16) THFR
        /\ rw_cells asegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8))]
        /\ shv3 m' /\ shc (SP + -16) m')
      (DST 0xb3fb0 m x1 (SP + -64) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until m. intros ST MI GOT SHB FR2 FR0 VEC (S5 & S6 & S7) T0.
    unfold shv3, shz, shc, THFR, DVFR in *. unfold AVEC, ADTOR_THUNK, AANNOT in *.
    change (shad 0x6a2a48) with 2148320585 in *. change (shad 0x6a2a50) with 2148320586 in *. change (shad 0x6a2a40) with 2148320584 in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSS : 2148339200 <= Z.shiftr (SP + -16) 3 + 2147450880 /\ Z.shiftr (SP + -16) 3 + 2147450880 + 1 <= 17594333495296)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 64, SP - 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xb3fb8. release_frame FR2 ST (SP + -48).
    steps_to 0xb3e9c. zstep. carve_frame 16%nat ST.
    steps_to 0xb3ec8. zstep. bf.
    steps_to 0x84930.
    apply evtF_done. do 12 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact VEC|]. split; [split; [exact S5| split; [exact S6| exact S7]]| exact T0].
  Qed.

  (* [comment removed for export] *)
  Lemma vd_c : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
    stk asegs m lo (SP + -64) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m (SP + -64) [C8 (Z_to_bv 64 (SP + -16)); C8 (Z_to_bv 64 0xb3e00)] ->
    rw_cells asegs m (SP + -48) DVFR -> rw_cells asegs m (SP + -16) THFR ->
    rw_cells asegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8))] ->
    shv3 m -> shc (SP + -16) m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = MS (mkR (Z_to_bv 64 0xb11a8) (Z_to_bv 64 (SP + -16)) gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 8) y12 y13 y14 y15 y16 y17
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (Z_to_bv 64 AOPDEL_SZ_PC) fc None m' (seg_rom asegs)
        /\ munch [(SP - 64, SP - 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -16) /\ rw_cells asegs m' (SP + -16) THFR
        /\ rw_cells asegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8))])
      (DST 0xb3f08 m x1 (SP + -64) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until m. intros ST MI GOT SHB FR2 FR1 FR0 VEC (S5 & S6 & S7) T0.
    unfold shv3, shz, shc, THFR, DVFR in *. unfold AVEC, ADTOR_THUNK, AANNOT in *.
    change (shad 0x6a2a48) with 2148320585 in *. change (shad 0x6a2a50) with 2148320586 in *. change (shad 0x6a2a40) with 2148320584 in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSS : 2148339200 <= Z.shiftr (SP + -16) 3 + 2147450880 /\ Z.shiftr (SP + -16) 3 + 2147450880 + 1 <= 17594333495296)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    unfold AOPDEL_SZ_PC.
    pose proof (munch_refl [(SP - 64, SP - 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xb3f10. release_frame FR2 ST (SP + -48).
    steps_to 0xb3e3c. replace (V + 8 - V) with 8 by lia.
    steps_to 0xb3e4c. release_frame FR1 ST (SP + -16).
    steps_to 0x1018b8.
    apply evtF_done. do 14 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR0| exact VEC].
  Qed.

  (* [comment removed for export] *)
  Lemma vd_d : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo (SP + -16) -> mem_inv asegs m -> rw_cells asegs m (SP + -16) THFR ->
    evtF asegs RNG (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (ret_pc ra) fc None m (seg_rom asegs)
        /\ stk asegs m lo SP)
      (MS (mkR x1 (Z_to_bv 64 (SP + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb11a8) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI FR0. unfold THFR in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    zstep. release_frame FR0 ST (bv_unsigned sp). zstep. zstep.
    apply evtF_done. split; [reflexivity| exact ST].
  Qed.
End S.
End CANSEC1.
