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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
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

(* [comment removed for export] *)
Lemma land_ldiff_distrH x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x k), (Z.testbit a k), (Z.testbit b k); reflexivity. Qed.
Lemma land_alignH : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> Z.land x (Z.ldiff (Z.ones 64) (Z.ones k)) = x - x mod 2^k.
Proof.
  intros x k Hx Hk. rewrite land_ldiff_distrH. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed.
Lemma land_m32H : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof. intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)). rewrite land_alignH by lia. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition ALAM : Z := 0xb1c54.          (* [comment removed for export] *)
Definition ALAM_RET : Z := 0xb1528.      (* [comment removed for export] *)
Definition AVDTORF_H : Z := 0xb2e28.     (* [comment removed for export] *)
Definition AVDTORF_RET : Z := 0xb1618.   (* [comment removed for export] *)
Definition ASETF5 : Z := 0x84a50.        (* [comment removed for export] *)
Definition ASETF5_RET : Z := 0xb1644.
Definition HJOIN : Z := 0xb14c4.         (* [comment removed for export] *)
Definition HFIRST : Z := 0xb1744.        (* [comment removed for export] *)
Definition AGUARD_ACQ_H : Z := 0xf1c6c.  (* [comment removed for export] *)
Definition AGUARD_REL_H : Z := 0xf1cbc.  (* [comment removed for export] *)
Definition ARSI_H : Z := 0xb10e8.        (* [comment removed for export] *)
Definition ACXA_STUB : Z := 0x6c590.     (* [comment removed for export] *)
Definition ACXA_ICEPT_H : Z := 0x76b5c.  (* [comment removed for export] *)
Definition ADSO_H : Z := 0x175b20.       (* [comment removed for export] *)
Definition HMAGIC : Z := 0x41b58ab3.     (* [comment removed for export] *)
Definition HMAGIC_RET : Z := 0x45e0360e. (* [comment removed for export] *)
Definition HDESC : Z := 0x209c9.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HZRB (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition B00 : byte := Z_to_bv 8 0.
Definition BF1 : byte := Z_to_bv 8 18446744073709551601.   (* [comment removed for export] *)
Definition BF2 : byte := Z_to_bv 8 18446744073709551602.   (* [comment removed for export] *)
Definition BF3 : byte := Z_to_bv 8 18446744073709551603.   (* [comment removed for export] *)
Definition BF8 : byte := Z_to_bv 8 18446744073709551608.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition shrowB : list cell := [C1 BF8; C1 BF8; C1 BF8; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2].
(* [comment removed for export] *)
Definition shcells3g (g : byte) : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 g; C1 g; C1 g; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2]
  ++ shrowB ++ shrowB ++ shrowB
  ++ [C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3]
  ++ [C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Definition shcells3 : list cell := shcells3g BF8.
Lemma shcells3g_f8 : shcells3g BF8 = shcells3. Proof. reflexivity. Qed.

Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D SZ : Z) (lo : Z) (SPA : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - AHARNESS_STACK.
  Hypothesis LOC : ATOP <= lo.
  Hypothesis SPT : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis ESPA : SPA = SP - 256 - (SP - 256) mod 32.
  Hypothesis HD : 0 <= D /\ D + SZ <= ATOP.
  Hypothesis HSZ : 0 <= SZ < 2^26.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.

  Lemma spa_props : SP - 272 <= SPA <= SP - 256 /\ SPA mod 32 = 0 /\ (SP + -256) - (SP + -256) mod 32 = SPA.
  Proof. rewrite ESPA. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma h_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)] -> rt_suar m ->
    evtF bsegs RNG (fun ms' => exists m' y_a1 y_a2,
        ms' = MS (mkR (Z_to_bv 64 0xb1394) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA)
                     (Z_to_bv 64 352) y_a1 y_a2 a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 SZ) (Z_to_bv 64 D) s6 (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASTKMALLOC3) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 256, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) (HZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ stk bsegs m' lo (SP + -104))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold rt_suar in SUA. unfold AFUZZ_ENTRY, ASTKMALLOC3, AHARNESS_STACK, AGOT_SUAR, ASUAR in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 256, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 152%nat ST.
    zstep. (* [comment removed for export] *)
    do 13 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite land_m32H by lia. rewrite ESPA'.
    lazymatch goal with H : rw_cells bsegs _ (SP + -256) _ |- _ => release_frame H ST (SP + -104) end.
    zstep. zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite sx32_lit by lia. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    apply evtF_done. change (Z_to_bv 64 2147450880) with (Z_to_bv 64 ASHOFF).
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [| exact ST]. lazymatch goal with H : rw_cells bsegs _ (SP + -104) _ |- _ => exact H end.
  Qed.
  (* [comment removed for export] *)
  Lemma sh64_of_words : forall m A,
    rw_cells bsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m A (repeat (C1 B00) 44 ++ [C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

  (* [comment removed for export] *)
  Definition hlocals (F : Z) (c64 c72 c80 c88 : cell) (l96 l104 l112 : list byte) (c128 c136 c144 : cell) : list cell :=
    [c64; c72; c80; c88; CB 8 l96; CB 8 l104; CB 8 l112; C8 (Z_to_bv 64 F); c128; c136; c144].
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma h_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x28 x29 x30 x31 : word) m (F : Z) (j0 j1 j2 : word) (g gi : byte),
    stk bsegs m lo (SP + -104) -> mem_inv bsegs m ->
    rw_cells bsegs m F [C8 j0; C8 j1; C8 j2] ->
    rw_cells bsegs m (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m AVEC_GUARD [C1 g; C1 gi] -> (g = Z_to_bv 8 0 \/ g = Z_to_bv 8 1) ->
    ablk F (F + 512) -> F + 512 <= ATOP -> F mod 512 = 0 ->
    rng RNG F 512 -> rng RNG (shad F) 64 ->
    evtF bsegs RNG (fun ms' => exists m' (l64 l72 l80 l88 l96 l104 l112 l128 l136 l144 : list byte) y10 y11 y12 y13 y14,
        ms' = MS (mkR (Z_to_bv 64 0xb1394) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 (if bv_eqb g (Z_to_bv 8 0) then HFIRST else HJOIN)) fc None m' (seg_rom bsegs)
        /\ munch [(SPA + 64, SPA + 152); (F, F + 24); (shad F, shad F + 44)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo (SPA + 64) /\ stk bsegs m' (SPA + 152) (SP + -104)
        /\ rw_cells bsegs m' (SPA + 64) (hlocals F (CB 8 l64) (CB 8 l72) (CB 8 l80) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144))
        /\ rw_cells bsegs m' F [C8 (Z_to_bv 64 HMAGIC); C8 (Z_to_bv 64 HDESC); C8 (Z_to_bv 64 AFUZZ_ENTRY)]
        /\ rw_cells bsegs m' (shad F) shcells3)
      (MS (mkR (Z_to_bv 64 0xb1394) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F) x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 SZ) (Z_to_bv 64 D) x22 (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb1394) fc None m (seg_rom bsegs)).
  Proof.
    intros until gi. intros ST MI HDR SH0 GRD GV FH FC F512 RF RSF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH. unfold AHARNESS_STACK, AVEC_GUARD, HFIRST, HJOIN, HMAGIC, HDESC, AFUZZ_ENTRY, hlocals in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    apply sh64_of_words in SH0.
    replace (shad F) with (Z.shiftr F 3 + ASHOFF) in * by (unfold shad; lia).
    assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 64 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SPA + 64, SPA + 152); (F, F + 24); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 44)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ lo (SPA + 152) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 152) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88 in STL, FRA. replace (SPA + 152 - 88) with (SPA + 64) in STL, FRA by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 88 jA [] [8;8;8;8;8;8;8;8;8;8;8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    cbn [repeat app] in SH0.
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    do 9 zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr F 3 + ASHOFF) _ |- _ =>
      pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity). (* [comment removed for export] *)
    do 40 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    destruct GV as [-> | ->].
    - zstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. bcase K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
      apply evtF_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STL|]. split; [exact STG|]. split; [exact FRA|]. split; [exact HDR| exact SH0].
    - zstep. change (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1 : word). (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. bcase K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
      apply evtF_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STL|]. split; [exact STG|]. split; [exact FRA|]. split; [exact HDR| exact SH0].
  Qed.
  (* [comment removed for export] *)
  Lemma h_join : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (F V : Z) (l64 l72 l80 l88 l96 l104 l112 l128 l136 l144 : list byte),
    mem_inv bsegs m ->
    rw_cells bsegs m (SPA + 64) (hlocals F (CB 8 l64) (CB 8 l72) (CB 8 l80) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144)) ->
    rw_cells bsegs m (shad F) shcells3 ->
    rw_cells bsegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    rw_cells bsegs m V [C8 (Z_to_bv 64 AFALLBACK)] ->
    rw_cells bsegs m (Z.shiftr V 3 + ASHOFF) [C1 (Z_to_bv 8 0)] ->
    V mod 8 = 0 -> ablk V (V + 8) -> ablk F (F + 512) -> F mod 512 = 0 -> (V + 8 <= F \/ F + 512 <= V) ->
    rng RNG V 8 -> rng RNG (Z.shiftr V 3 + ASHOFF) 1 -> rng RNG (shad F) 64 ->
    evtF bsegs RNG (fun ms' => exists m' y10,
        ms' = MS (mkR (Z_to_bv 64 ALAM_RET) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (SPA + 128)) (Z_to_bv 64 AFALLBACK) x13 x14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 V) s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 ALAM) fc None m' (seg_rom bsegs)
        /\ y10 = Z_to_bv 64 (F + 32)
        /\ munch [(shad F + 4, shad F + 7); (SPA + 64, SPA + 144)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPA + 64) (hlocals F (C8 (Z_to_bv 64 AVEC)) (CB 8 l72) (CB 8 l80) (C8 (Z_to_bv 64 ASHOFF)) l96 l104 l112 (C8 (Z_to_bv 64 D)) (C8 (Z_to_bv 64 SZ)) (CB 8 l144))
        /\ rw_cells bsegs m' (shad F) (shcells3g B00))
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 HJOIN) fc None m (seg_rom bsegs)).
  Proof.
    intros until l144. intros MI LOCS SH VEC VB VSH V8 VH FH F512 VF RV RVS RSF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    unfold AHARNESS_STACK, AVEC, AFALLBACK, HJOIN, ALAM, ALAM_RET, hlocals in *.
    replace (shad F) with (Z.shiftr F 3 + ASHOFF) in * by (unfold shad; lia).
    assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 64 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (BSV : 2147450880 <= Z.shiftr V 3 + ASHOFF /\ Z.shiftr V 3 + ASHOFF + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (DJS : Z.shiftr V 3 + ASHOFF + 1 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 64 <= Z.shiftr V 3 + ASHOFF)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - VF F512 V8 FH1 VH1; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(Z.shiftr F 3 + ASHOFF + 4, Z.shiftr F 3 + ASHOFF + 7); (SPA + 64, SPA + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold shcells3, shcells3g, shrowB in *. cbn [app] in SH |- *.
    zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; clear - K0 V8 VH1; ubalign K0; lia|]. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. zstep. bcase K1; [exfalso; clear - K1 V8 VH1; ubalign K1; lia|]. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. bcase K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; clear - K2 VH1; lia|]. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with H : rw_cells bsegs mx (Z.shiftr V 3 + ASHOFF) _ |- _ => pose proof (c1_rd _ _ _ H) as RD1 end end.
    zstep. clear RD1. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). (* [comment removed for export] *)
    zstep. bcase K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    apply evtF_done. change (Z_to_bv 64 2147450880) with (Z_to_bv 64 ASHOFF).
    eexists _, _. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact LOCS| exact SH].
  Qed.
  (* [comment removed for export] *)
  Lemma h_mid : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (F V : Z) (c72 c80 : list byte) (l96 l104 l112 l144 : list byte),
    mem_inv bsegs m ->
    rw_cells bsegs m (SPA + 64) (hlocals F (C8 (Z_to_bv 64 AVEC)) (CB 8 c72) (CB 8 c80) (C8 (Z_to_bv 64 ASHOFF)) l96 l104 l112 (C8 (Z_to_bv 64 D)) (C8 (Z_to_bv 64 SZ)) (CB 8 l144)) ->
    0 <= V -> V + 16 <= 2^47 ->
    evtF bsegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 AVDTORF_RET) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (SPA + 144)) x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 V) s9 s10 (Z_to_bv 64 (V + 8)) x28 x29 x30 x31)
                 FR (Z_to_bv 64 AVDTORF_H) fc None m' (seg_rom bsegs)
        /\ munch [(SPA + 144, SPA + 152)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPA + 64) (hlocals F (C8 (Z_to_bv 64 AVEC)) (CB 8 c72) (CB 8 c80) (C8 (Z_to_bv 64 ASHOFF)) l96 l104 l112 (C8 (Z_to_bv 64 D)) (C8 (Z_to_bv 64 SZ)) (C8 (Z_to_bv 64 (F + 32)))))
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 V) s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 ALAM_RET) fc None m (seg_rom bsegs)).
  Proof.
    intros until l144. intros MI LOCS V0 VT.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    unfold AHARNESS_STACK, AVEC, ALAM_RET, AVDTORF_H, AVDTORF_RET, hlocals in *.
    pose proof (munch_refl [(SPA + 144, SPA + 152)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity). (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. bcase K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    apply evtF_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact LOCS].
  Qed.

  (* [comment removed for export] *)
  Lemma h_ret1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x27 y28 y29 y30 y31 : word) m (F : Z) (h1 h2 : word),
    mem_inv bsegs m ->
    rw_cells bsegs m (shad F) (shcells3g B00) ->
    rw_cells bsegs m F [C8 (Z_to_bv 64 HMAGIC); C8 h1; C8 h2] ->
    ablk F (F + 512) -> F mod 512 = 0 ->
    rng RNG F 512 -> rng RNG (shad F) 64 ->
    evtF bsegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 ASETF5_RET) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (shad F)) (Z_to_bv 64 64) x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) x20 x21 (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) x24 s9 s10 x27 y28 y29 y30 y31)
                 FR (Z_to_bv 64 ASETF5) fc None m' (seg_rom bsegs)
        /\ munch [(shad F + 4, shad F + 7); (F, F + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (shad F) shcells3
        /\ rw_cells bsegs m' F [C8 (Z_to_bv 64 HMAGIC_RET); C8 h1; C8 h2])
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) x20 x21 (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) x24 s9 s10 x27 y28 y29 y30 y31)
          FR (Z_to_bv 64 AVDTORF_RET) fc None m (seg_rom bsegs)).
  Proof.
    intros until h2. intros MI SH HDR FH F512 RF RSF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    unfold AHARNESS_STACK, AVEC, AVDTORF_RET, ASETF5, ASETF5_RET, HMAGIC, HMAGIC_RET in *.
    replace (shad F) with (Z.shiftr F 3 + ASHOFF) in * by (unfold shad; lia).
    assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 64 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(Z.shiftr F 3 + ASHOFF + 4, Z.shiftr F 3 + ASHOFF + 7); (F, F + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold shcells3, shcells3g, shrowB in *. cbn [app] in SH |- *.
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity). (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    apply evtF_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact SH| exact HDR].
  Qed.

  (* [comment removed for export] *)
  Lemma h_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x27 y28 y29 y30 y31 : word) m (F FLG : Z) csA,
    mem_inv bsegs m ->
    rw_cells bsegs m (F + 504) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m (SP + -104) (HZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> rw_cells bsegs m (SPA + 64) csA -> cells_size csA = 88%nat ->
    stk bsegs m lo (SPA + 64) -> stk bsegs m (SPA + 152) (SP + -104) ->
    ablk F (F + 512) -> F + 512 <= ATOP -> F mod 512 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= F \/ F + 512 <= FLG) ->
    rng RNG F 512 -> rng RNG FLG 1 ->
    evtF bsegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(FLG, FLG + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) x20 x21 (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) x24 s9 s10 x27 y28 y29 y30 y31)
          FR (Z_to_bv 64 ASETF5_RET) fc None m (seg_rom bsegs)).
  Proof.
    intros until csA. intros MI FLP FLC HRB LOCS CSA STL STG FH FC F512 GH GC GF RF RG.
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    pose proof (ablk_lin _ _ GH) as (GH1 & GH2 & GH3 & GH4). unfold AIMG_HI in GH1. band_ind GH bGH.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND, KHIGH, AHARNESS_STACK, ASETF5_RET in *. atop_facts.
    unfold HZRB in HRB.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    pose proof (munch_refl [(FLG, FLG + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    do 13 zstep. zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply stk_release in LOCS; [| exact STL| lia]. rewrite CSA in LOCS. change (Z.of_nat 88) with 88 in LOCS. replace (SPA + 64 + 88) with (SPA + 152) in LOCS by lia.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 152) (SP + -104) LOCS STG ltac:(lia)) as ST2 end.
    release_frame HRB ST2 (bv_unsigned sp).
    apply evtF_done.
    eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST2| exact FLC].
  Qed.

  (* [comment removed for export] *)
  Lemma h_w1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (F : Z) (l64 l72 l80 l88 l96 l104 l112 l128 l136 l144 : list byte),
    mem_inv bsegs m -> rw_cells bsegs m AVEC_GUARD guard0 ->
    rw_cells bsegs m (SPA + 64) (hlocals F (CB 8 l64) (CB 8 l72) (CB 8 l80) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144)) ->
    evtF bsegs RNG (fun ms' => exists m' y11 y12,
        ms' = MS (mkR (Z_to_bv 64 0xb176c) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 AVEC) y11 y12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 ARSI_H) fc None m' (seg_rom bsegs)
        /\ munch [(AVEC_GUARD + 1, AVEC_GUARD + 2); (SPA + 72, SPA + 88)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' AVEC_GUARD [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 2)]
        /\ rw_cells bsegs m' (SPA + 64) (hlocals F (CB 8 l64) (C8 (Z_to_bv 64 F)) (C8 (Z_to_bv 64 F)) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144)))
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 HFIRST) fc None m (seg_rom bsegs)).
  Proof.
    intros until l144. intros MI GRD LOCS. unfold AVEC_GUARD, AVEC, ARSI_H, HFIRST, guard0, hlocals, AHARNESS_STACK in *. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    pose proof (munch_refl [(7011136 + 1, 7011136 + 2); (SPA + 72, SPA + 88)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    steps_to 0xb10e8.
    apply evtF_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact GRD| exact LOCS].
  Qed.

  (* [comment removed for export] *)
  Lemma h_w2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (F : Z),
    mem_inv bsegs m ->
    evtF bsegs RNG (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 0xb1788) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 ADTOR_THUNK) (Z_to_bv 64 AVEC) (Z_to_bv 64 ADSO_H) x13 x14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 ACXA_ICEPT_H) fc None m (seg_rom bsegs))
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb176c) fc None m (seg_rom bsegs)).
  Proof.
    intros until F. intros MI. unfold ACXA_ICEPT_H, ADTOR_THUNK, AVEC, ADSO_H in *.
    steps_to 0x76b5c.
    apply evtF_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma h_w3 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (F : Z) (g0 g1 : byte) (l64 l88 l96 l104 l112 l128 l136 l144 : list byte),
    mem_inv bsegs m -> rw_cells bsegs m AVEC_GUARD [C1 g0; C1 g1] ->
    rw_cells bsegs m (SPA + 64) (hlocals F (CB 8 l64) (C8 (Z_to_bv 64 F)) (C8 (Z_to_bv 64 F)) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144)) ->
    evtF bsegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 0xb1794) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 AVEC_GUARD) (Z_to_bv 64 1) x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 HJOIN) fc None m' (seg_rom bsegs)
        /\ munch [(AVEC_GUARD, AVEC_GUARD + 2)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' AVEC_GUARD guard1
        /\ rw_cells bsegs m' (SPA + 64) (hlocals F (CB 8 l64) (C8 (Z_to_bv 64 F)) (C8 (Z_to_bv 64 F)) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144)))
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb1788) fc None m (seg_rom bsegs)).
  Proof.
    intros until l144. intros MI GRD LOCS. unfold AVEC_GUARD, guard1, HJOIN, hlocals, AHARNESS_STACK in *. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    pose proof (munch_refl [(7011136, 7011136 + 2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    steps_to 0xf1cc4.
    pose proof (rw_cells_store_ok bsegs _ _ _ 0%nat _ 1%nat GRD ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK.
    zstep. clear SOK.
    steps_to 0xb14c4.
    apply evtF_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact GRD| exact LOCS].
  Qed.
End S.
End CANSEC1.
