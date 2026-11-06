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
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AU_kit AU_iface AU_consts AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.

(* [comment removed for export] *)
Lemma land_ldiff_distrU x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x k), (Z.testbit a k), (Z.testbit b k); reflexivity. Qed.
Lemma land_alignU : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> Z.land x (Z.ldiff (Z.ones 64) (Z.ones k)) = x - x mod 2^k.
Proof.
  intros x k Hx Hk. rewrite land_ldiff_distrU. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed.
Lemma land_m32U : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof. intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)). rewrite land_alignU by lia. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition FZRB (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D SZ : Z) (lo : Z) (SPA : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - AHARNESS_STACK.
  Hypothesis LOC : ATOP <= lo.
  Hypothesis SPT : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis ESPA : SPA = SP - 224 - (SP - 224) mod 32.
  Hypothesis HD : 0 <= D /\ D + SZ <= ATOP.
  Hypothesis HSZ : 0 <= SZ < 2^26.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Lemma spa_props : SP - 240 <= SPA <= SP - 224 /\ SPA mod 32 = 0 /\ (SP + -224) - (SP + -224) mod 32 = SPA.
  Proof. rewrite ESPA. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma f_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo SP -> mem_inv asegs m ->
    rt_got m -> rt_shbase m -> rw_cells asegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)] -> rt_suar m ->
    evtF asegs RNG (fun ms' => exists m' y_a1 y_a2,
        ms' = MS (mkR (Z_to_bv 64 0xb1580) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA)
                     (Z_to_bv 64 128) y_a1 y_a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 SZ) (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASHOFF) s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASTKMALLOC1) fc None m' (seg_rom asegs)
        /\ munch [(SP - 240, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SP + -104) (FZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ stk asegs m' lo (SP + -104))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold rt_suar in SUA. unfold AFUZZ_ENTRY, ASTKMALLOC1, AHARNESS_STACK, AGOT_SUAR, ASUAR in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 240, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 120%nat ST.
    zstep. (* [comment removed for export] *)
    do 13 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite land_m32U by lia. rewrite ESPA'.
    release_frame FR1 ST (SP + -104).
    zstep. zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite sx32_lit by lia. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    apply evtF_done. change (Z_to_bv 64 2147450880) with (Z_to_bv 64 ASHOFF).
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0| exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition B00 : byte := Z_to_bv 8 0.
  Definition BF1 : byte := Z_to_bv 8 18446744073709551601.   (* [comment removed for export] *)
  Definition BF2 : byte := Z_to_bv 8 18446744073709551602.   (* [comment removed for export] *)
  Definition BF3 : byte := Z_to_bv 8 18446744073709551603.   (* [comment removed for export] *)
  Definition BF5 : byte := Z_to_bv 8 18446744073709551605.   (* [comment removed for export] *)
  Definition BF8 : byte := Z_to_bv 8 18446744073709551608.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition shcells1 : list cell :=
    [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF2; C1 BF2; C1 BF2; C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3].

  (* [comment removed for export] *)
  Lemma f_hdr : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) m (F : Z) (j0 j1 j2 : word) (g gi : byte),
    stk asegs m lo (SP + -104) -> mem_inv asegs m ->
    rw_cells asegs m F [C8 j0; C8 j1; C8 j2] -> rw_cells asegs m (shad F) (repeat (C1 B00) 16) ->
    rw_cells asegs m AVEC_GUARD [C1 g; C1 gi] -> (g = Z_to_bv 8 0 \/ g = Z_to_bv 8 1) ->
    ablk F (F + 128) -> F + 128 <= ATOP -> F mod 128 = 0 ->
    rng RNG F 128 -> rng RNG (shad F) 16 ->
    evtF asegs RNG (fun ms' => exists m' (l72 l80 l88 l96 : list byte) y10 y11 y12 y13,
        ms' = MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 x14 x15 x16 x17
                     (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 (shad F)) x21 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) x27 x28 x29 x30 x31)
                 FR (Z_to_bv 64 (if bv_eqb g (Z_to_bv 8 0) then 0xb1824 else 0xb1640)) fc None m' (seg_rom asegs)
        /\ munch [(SPA + 72, SPA + 112); (F, F + 24); (shad F, shad F + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SPA + 72) /\ stk asegs m' (SPA + 112) (SP + -104)
        /\ rw_cells asegs m' (SPA + 72) [CB 8 l72; CB 8 l80; CB 8 l88; CB 8 l96; C8 (Z_to_bv 64 F)]
        /\ rw_cells asegs m' F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d36e); C8 (Z_to_bv 64 0xb150c)]
        /\ rw_cells asegs m' (shad F) shcells1)
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 SZ) (Z_to_bv 64 D) x20 x21 x22 x23 x24 x25 (Z_to_bv 64 ASHOFF) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb1580) fc None m (seg_rom asegs)).
  Proof.
    intros until gi. intros ST MI HDR SH0 GRD GV FH FC F128 RF RSF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH. unfold AHARNESS_STACK, AVEC_GUARD in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (shad F) with (Z.shiftr F 3 + ASHOFF) in * by (unfold shad; lia).
    assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 16 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SPA + 72, SPA + 112); (F, F + 24); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ lo (SPA + 112) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 112) 40 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 40) with 40 in STL, FRA. replace (SPA + 112 - 40) with (SPA + 72) in STL, FRA by lia.
    apply (rw_cells_split_CB asegs _ _ [] 40 jA [] [8;8;8;8;8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    cbn [repeat] in SH0.
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    do 8 zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity). (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells asegs mx (Z.shiftr F 3 + ASHOFF) _ |- _ =>
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity). (* [comment removed for export] *)
    do 8 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    destruct GV as [-> | ->].
    - zstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. bcase K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
      apply evtF_done. eexists _, _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STL|]. split; [exact STG|]. split; [exact FRA|]. split; [exact HDR| exact SH0].
    - zstep. change (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1 : word). (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. bcase K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
      apply evtF_done. eexists _, _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STL|]. split; [exact STG|]. split; [exact FRA|]. split; [exact HDR| exact SH0].
  Qed.
End S.
End CANSEC1.
