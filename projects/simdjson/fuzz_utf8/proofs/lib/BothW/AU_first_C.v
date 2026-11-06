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
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells ABase AMalloc_iface F_apoison F_annot.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac AU_first_A.
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

(* [comment removed for export] *)
Ltac b2z_lia K :=
  exfalso;
  rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.sub_0_r in K;
  repeat match type of K with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
  cbn [Z.b2z] in K;
  repeat match type of K with context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in K end;
  try (change 7 with (Z.ones 3) in K; rewrite !Z.land_ones in K by lia; change (2^3) with 8 in K);
  rewrite ?unsigned_lit in K by lia;
  first [lia | Z.div_mod_to_equations; lia].
Ltac bshow := let K := fresh "K" in if_cases K; zify_cond K; [let T := type of K in idtac "KTRUE:" T| let T := type of K in idtac "KFALSE:" T].
Ltac bf := let K := fresh "K" in if_cases K; zify_cond K; [solve [b2z_lia K]| clear K].
Ltac bt := let K := fresh "K" in if_cases K; zify_cond K; [clear K| solve [b2z_lia K]].
Ltac bdec := first [bf | bt].
Ltac unorm := progress (rewrite ?Z.add_0_l, ?Z.sub_0_r, ?Z.add_0_r).
Ltac usteps_to p := repeat (tryif at_pc p then fail else first [astep | bdec | unorm]);
  tryif at_pc p then idtac else (match goal with |- ?G => idtac "STUCK:" G end; try bshow; fail 1 "usteps_to: stuck before" p).

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
  Hypothesis RSS : rng RNG (Z.shiftr (SP + -216) 3 + 2147450880) 5.

  Definition shc6 (m : amem) : Prop := shc V m /\ shs5 sp m.

  (* [comment removed for export] *)
  Definition EBFR2 (j : list byte) (c0 c1 c2 c3 : word) : list cell :=
    [CB 8 j; C8 c0; C8 c1; C8 c2; C8 c3; C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 (AVEC + 16)); C8 (Z_to_bv 64 0x6ad8c8); C8 (Z_to_bv 64 0x6ad8c0);
     C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 0xafe20)].
  Definition SWFR : list cell :=
    [C8 (Z_to_bv 64 18446744073709551608); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2148326126); C8 (Z_to_bv 64 0x6ad8c0); C8 (Z_to_bv 64 2147450880);
     C8 (Z_to_bv 64 2148326125); C8 (Z_to_bv 64 0x6ad8c0); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb30d0)].

  Ltac prep7 :=
    change (shad 0x6ad8c0) with 2148326168 in *; change (shad 0x6ad8e0) with 2148326172 in *; change (shad 0x16c340) with 2147637352 in *;
    change (shad 0x6ad908) with 2148326177 in *; change (shad 0x6ad768) with 2148326125 in *; change (shad 0x6ad770) with 2148326126 in *;
    change (shad 0x6ad760) with 2148326124 in *.
  Ltac showst := match goal with |- ?G => idtac G end; repeat match goal with H : rw_cells _ _ _ _ |- _ => let T := type of H in idtac "CELLS:" T; clear H end; repeat match goal with H : _ = true |- _ => let T := type of H in idtac "COND:" T; clear H end; repeat match goal with H : _ = false |- _ => let T := type of H in idtac "COND:" T; clear H end.

  (* [comment removed for export] *)
  Lemma rsi_c1 : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j js (jv : list byte),
    stk bsegs m lo (SP + -288) -> mem_inv bsegs m -> rt_got m -> rt_shbase m ->
    rw_cells bsegs m (SP + -288) (SBFR js) ->
    rw_cells bsegs m (SP + -224) (EBFR j) ->
    rw_cells bsegs m V [CB 8 jv] ->
    rw_cells bsegs m AVEC [C8 w0; C8 w0; C8 w0] -> rw_cells bsegs m 0x6ad8c0 [C8 (Z_to_bv 64 AFALLBACK)] ->
    shz7 m -> shc6 m ->
    evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) j2,
        ms' = MS (mkR (Z_to_bv 64 0xb3544) (Z_to_bv 64 (SP + -304)) gp tp y5 y6 y7 (Z_to_bv 64 (SP + -216)) (Z_to_bv 64 AVEC)
                     (Z_to_bv 64 V) (Z_to_bv 64 0) (Z_to_bv 64 0) y13 y14 y15 y16 y17
                     (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 (SP + -208)) (Z_to_bv 64 V) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148326125)
                     (Z_to_bv 64 (Z.shiftr (SP + -208) 3 + 2147450880)) (Z_to_bv 64 2148326124) (Z_to_bv 64 0) (Z_to_bv 64 2148326168) (Z_to_bv 64 2148326125)
                     y28 y29 y30 y31)
                 FR (Z_to_bv 64 AMEMCPY) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 336, SP - 176); (V, V + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo (SP + -304)
        /\ rw_cells bsegs m' (SP + -304) SWFR
        /\ rw_cells bsegs m' (SP + -224) (EBFR2 j2 (Z_to_bv 64 V) (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)))
        /\ rw_cells bsegs m' V [C8 (Z_to_bv 64 AFALLBACK)]
        /\ rw_cells bsegs m' AVEC [C8 w0; C8 w0; C8 w0] /\ rw_cells bsegs m' 0x6ad8c0 [C8 (Z_to_bv 64 AFALLBACK)]
        /\ shz7 m' /\ shc6 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -288)) gp tp t0 t1 t2 (Z_to_bv 64 (SP + -192)) (Z_to_bv 64 1) (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (SP + -216)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (SP + -192) 3 + 2147450880)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 2148326126) (Z_to_bv 64 0) (Z_to_bv 64 (-8)) (Z_to_bv 64 0) (Z_to_bv 64 2148326168) (Z_to_bv 64 2148326125) t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb3368) fc None m (seg_rom bsegs)).
  Proof.
    intros until jv. intros ST MI GOT SHB FR1 FR0 VB VEC ARR (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3 & T4).
    unfold shc6, shs5, shz7, shc, shz, EBFR, EBFR2, SWFR, SBFR, AVEC, AFALLBACK, AMEMCPY, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148344832 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148344832 <= Z.shiftr (SP + -216) 3 + 2147450880 /\ Z.shiftr (SP + -184) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -208) 3 = Z.shiftr (SP + -216) 3 + 1 /\ Z.shiftr (SP + -200) 3 = Z.shiftr (SP + -216) 3 + 2
                  /\ Z.shiftr (SP + -192) 3 = Z.shiftr (SP + -216) 3 + 3 /\ Z.shiftr (SP + -184) 3 = Z.shiftr (SP + -216) 3 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 336, SP - 176); (V, V + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    apply (rw_cells_split_CB bsegs _ _ [] 32 j _ [8;8;8;8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    usteps_to 0xb3428. release_frame FR1 ST (SP + -224).        (* [comment removed for export] *)
    usteps_to 0xb3460. zstep. carve_frame 80%nat ST.            (* [comment removed for export] *)
    usteps_to 0xb2cec. zstep. carve_frame 16%nat ST.            (* [comment removed for export] *)
    usteps_to 0xb2e60. zstep. carve_frame 16%nat ST.            (* [comment removed for export] *)
    usteps_to 0xb2ed0. release_frame FR3 ST (SP + -320).
    usteps_to 0xb2d78. release_frame FR2 ST (SP + -304).
    usteps_to 0x7f9f4. rewrite ?Z.sub_0_r, ?Z.add_0_l, ?Z.add_0_r.
    rewrite ?Z.add_0_l in FR0. replace (8 + V) with (V + 8) in FR0 by lia.
    apply evtF_done. do 14 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact VB|]. split; [exact VEC|]. split; [exact ARR|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2|]. split; [exact T3| exact T4].
  Qed.

  (* [comment removed for export] *)
  Lemma rsi_c2 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j2,
    stk bsegs m lo (SP + -304) -> mem_inv bsegs m -> rt_got m -> rt_shbase m ->
    rw_cells bsegs m (SP + -304) SWFR ->
    rw_cells bsegs m (SP + -224) (EBFR2 j2 (Z_to_bv 64 V) (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8))) ->
    rw_cells bsegs m AVEC [C8 w0; C8 w0; C8 w0] ->
    shz7 m -> shc6 m ->
    evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = MS (mkR (Z_to_bv 64 0xb3860) (Z_to_bv 64 (SP + -240)) gp tp y5 y6 y7 (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 AVEC)
                     (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (V + 8)) y14 y15 y16 y17
                     (Z_to_bv 64 0x6ad8c0) (Z_to_bv 64 2148326125) (Z_to_bv 64 2147450880) (Z_to_bv 64 0x6ad8c0) (Z_to_bv 64 2148326126) (Z_to_bv 64 0)
                     (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 0) (Z_to_bv 64 2148326168) (Z_to_bv 64 2148326125) y28 y29 y30 y31)
                 FR (Z_to_bv 64 AANNOT) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 256, SP - 176); (AVEC, AVEC + 24)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo (SP + -240)
        /\ rw_cells bsegs m' (SP + -240) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb30d0)]
        /\ rw_cells bsegs m' (SP + -224) (EBFR2 j2 w0 w0 w0 w0)
        /\ rw_cells bsegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
        /\ shz7 m' /\ shc6 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -304)) gp tp t0 t1 t2 (Z_to_bv 64 (SP + -216)) (Z_to_bv 64 AVEC)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 (SP + -208)) (Z_to_bv 64 V) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148326125)
               (Z_to_bv 64 (Z.shiftr (SP + -208) 3 + 2147450880)) (Z_to_bv 64 2148326124) (Z_to_bv 64 0) (Z_to_bv 64 2148326168) (Z_to_bv 64 2148326125)
               t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb3544) fc None m (seg_rom bsegs)).
  Proof.
    intros until j2. intros ST MI GOT SHB FR1 FR0 VEC (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3 & T4).
    unfold shc6, shs5, shz7, shc, shz, EBFR2, SWFR, RSIFR, AVEC, AFALLBACK, AMEMCPY, AANNOT, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148344832 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148344832 <= Z.shiftr (SP + -216) 3 + 2147450880 /\ Z.shiftr (SP + -184) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -208) 3 = Z.shiftr (SP + -216) 3 + 1 /\ Z.shiftr (SP + -200) 3 = Z.shiftr (SP + -216) 3 + 2
                  /\ Z.shiftr (SP + -192) 3 = Z.shiftr (SP + -216) 3 + 3 /\ Z.shiftr (SP + -184) 3 = Z.shiftr (SP + -216) 3 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 256, SP - 176); (7001952, 7001952 + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    usteps_to 0xb35f4. replace (V + 8 - V) with 8 by lia. change (bv_signed (Z_to_bv 64 8)) with 8. change (Z.shiftr 8 3) with 1.
    usteps_to 0xb3624. release_frame FR1 ST (SP + -224).        (* [comment removed for export] *)
    usteps_to 0xb37d8. zstep. carve_frame 16%nat ST.
    usteps_to 0xb2e60. zstep. carve_frame 16%nat ST.            (* [comment removed for export] *)
    usteps_to 0xb2ec4. release_frame FR2 ST (SP + -240).
    usteps_to 0x837dc. replace (8 + V) with (V + 8) by lia.
    apply evtF_done. do 12 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact VEC|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2|]. split; [exact T3| exact T4].
  Qed.

  (* [comment removed for export] *)
  Lemma rsi_c3 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m j j1 j2,
    stk bsegs m lo (SP + -240) -> mem_inv bsegs m -> rt_got m -> rt_shbase m ->
    rw_cells bsegs m (SP + -240) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb30d0)] ->
    rw_cells bsegs m (SP + -224) (EBFR2 j w0 w0 w0 w0) ->
    rw_cells bsegs m (SP + -128) (RSIFR ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j1 j2) ->
    rw_cells bsegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    shz7 m -> shc6 m ->
    evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 256, SP); (AVEC, AVEC + 24)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP
        /\ rw_cells bsegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
        /\ shz7 m' /\ shc6 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp t0 t1 t2 (Z_to_bv 64 (AVEC + 8)) (Z_to_bv 64 AVEC)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x6ad8c0) (Z_to_bv 64 2148326125) (Z_to_bv 64 2147450880) (Z_to_bv 64 0x6ad8c0) (Z_to_bv 64 2148326126) (Z_to_bv 64 0)
               (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 0) (Z_to_bv 64 2148326168) (Z_to_bv 64 2148326125) t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb3860) fc None m (seg_rom bsegs)).
  Proof.
    intros until j2. intros ST MI GOT SHB FR1 FR0 FRR VEC (S1 & S2 & S3 & S4 & S5 & S6 & S7) (SV & T0 & T1 & T2 & T3 & T4).
    unfold shc6, shs5, shz7, shc, shz, EBFR2, SWFR, RSIFR, AVEC, AFALLBACK, AMEMCPY, AANNOT, w0 in *. prep7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BSV : 2148344832 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSS : 2148344832 <= Z.shiftr (SP + -216) 3 + 2147450880 /\ Z.shiftr (SP + -184) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -208) 3 = Z.shiftr (SP + -216) 3 + 1 /\ Z.shiftr (SP + -200) 3 = Z.shiftr (SP + -216) 3 + 2
                  /\ Z.shiftr (SP + -192) 3 = Z.shiftr (SP + -216) 3 + 3 /\ Z.shiftr (SP + -184) 3 = Z.shiftr (SP + -216) 3 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SP - 256, SP); (7001952, 7001952 + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    usteps_to 0xb3868. release_frame FR1 ST (SP + -224).        (* [comment removed for export] *)
    usteps_to 0xb3678. zstep. carve_frame 16%nat ST.            (* [comment removed for export] *)
    usteps_to 0xb3754. release_frame FR1 ST (SP + -224).
    usteps_to 0xb3100. release_frame FR0 ST (SP + -128).        (* [comment removed for export] *)
    usteps_to 0xafeb8. release_frame FRR ST (bv_unsigned sp).
    zstep. zstep. (* [comment removed for export] *)
    apply evtF_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact VEC|].
    split. { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7]. }
    split; [exact SV|]. split; [exact T0|]. split; [exact T1|]. split; [exact T2|]. split; [exact T3| exact T4].
  Qed.

End S.
End CANSEC1.
