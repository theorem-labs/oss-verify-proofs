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
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AU_consts AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import ShadowTac.
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
  Hypothesis ESPA : SPA = SP - 192 - (SP - 192) mod 32.
  Hypothesis HD : 0 <= D /\ D + SZ <= ATOP.
  Hypothesis HSZ : 0 <= SZ < 2^26.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Lemma spa_props : SP - 208 <= SPA <= SP - 192 /\ SPA mod 32 = 0 /\ (SP + -192) - (SP + -192) mod 32 = SPA.
  Proof. rewrite ESPA. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma f_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)] -> rt_suar m ->
    evtF bsegs RNG (fun ms' => exists m' y_a1 y_a2 (l32 l40 l48 l64 l72 : list byte),
        ms' = MS (mkR (Z_to_bv 64 0xb1390) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA)
                     (Z_to_bv 64 96) y_a1 y_a2 a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 D) s4 s5 s6 s7 s8 (Z_to_bv 64 ASHOFF) s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASTKMALLOC1) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 208, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) (FZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ stk bsegs m' lo (SPA + 32) /\ stk bsegs m' (SPA + 80) (SP + -104)
        /\ rw_cells bsegs m' (SPA + 32) [CB 8 l32; CB 8 l40; CB 8 l48; C8 (Z_to_bv 64 SZ); CB 8 l64; CB 8 l72])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold rt_suar in SUA. unfold AFUZZ_ENTRY, ASTKMALLOC1, AHARNESS_STACK, AGOT_SUAR, ASUAR in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 208, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep. (* [comment removed for export] *)
    do 13 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite land_m32U by lia. rewrite ESPA'.
    release_frame FR1 ST (SP + -104).
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ lo (SPA + 80) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 80) 48 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 48) with 48 in STL, FRA. replace (SPA + 80 - 48) with (SPA + 32) in STL, FRA by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 48 jA [] [8;8;8;8;8;8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite sx32_lit by lia. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    apply evtF_done. change (Z_to_bv 64 2147450880) with (Z_to_bv 64 ASHOFF).
    eexists _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact STL|]. split; [exact STG| exact FRA].
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
    [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00].

  (* [comment removed for export] *)
  Lemma f_hdr : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word) m (F : Z) (j0 j1 j2 : word) (g gi : byte)
      (l32 l40 l48 l64 l72 : list byte),
    mem_inv bsegs m ->
    rw_cells bsegs m (SPA + 32) [CB 8 l32; CB 8 l40; CB 8 l48; C8 (Z_to_bv 64 SZ); CB 8 l64; CB 8 l72] ->
    rw_cells bsegs m F [C8 j0; C8 j1; C8 j2] -> rw_cells bsegs m (shad F) (repeat (C1 B00) 16) ->
    rw_cells bsegs m AVEC_GUARD [C1 g; C1 gi] -> (g = Z_to_bv 8 0 \/ g = Z_to_bv 8 1) ->
    ablk F (F + 128) -> F + 128 <= ATOP -> F mod 128 = 0 ->
    rng RNG F 128 -> rng RNG (shad F) 16 ->
    evtF bsegs RNG (fun ms' => exists m' y10 y11 y12 y13 y14,
        ms' = MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 x15 x16 x17
                     x18 (Z_to_bv 64 D) (Z_to_bv 64 F) x21 x22 x23 x24 (Z_to_bv 64 ASHOFF) (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) x28 x29 x30 x31)
                 FR (Z_to_bv 64 (if bv_eqb g (Z_to_bv 8 0) then 0xb1648 else 0xb143c)) fc None m' (seg_rom bsegs)
        /\ munch [(SPA + 72, SPA + 80); (F, F + 24); (shad F, shad F + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPA + 32) [CB 8 l32; CB 8 l40; CB 8 l48; C8 (Z_to_bv 64 SZ); CB 8 l64; C8 (Z_to_bv 64 F)]
        /\ rw_cells bsegs m' F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1f51a); C8 (Z_to_bv 64 0xb131c)]
        /\ rw_cells bsegs m' (shad F) shcells1)
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 D) x20 x21 x22 x23 x24 (Z_to_bv 64 ASHOFF) x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb1390) fc None m (seg_rom bsegs)).
  Proof.
    intros until l72. intros MI FRA HDR SH0 GRD GV FH FC F128 RF RSF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH. unfold AHARNESS_STACK, AVEC_GUARD in *.
    replace (shad F) with (Z.shiftr F 3 + ASHOFF) in * by (unfold shad; lia).
    assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 16 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SPA + 72, SPA + 80); (F, F + 24); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 12)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (RLOC : rng RNG (SPA + 32) 48) by (eapply rng_sub'; [exact RSTK| lia]).
    cbn [repeat] in SH0.
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    do 8 zstep. (* [comment removed for export] *)
    zstep.
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr F 3 + ASHOFF) _ |- _ =>
      pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep. (* [comment removed for export] *)
    do 4 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    destruct GV as [-> | ->].
    - zstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. bcase K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
      apply evtF_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact FRA|]. split; [exact HDR| exact SH0].
    - zstep. change (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1 : word). (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. bcase K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
      apply evtF_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact FRA|]. split; [exact HDR| exact SH0].
  Qed.
End S.
End CANSEC1.
