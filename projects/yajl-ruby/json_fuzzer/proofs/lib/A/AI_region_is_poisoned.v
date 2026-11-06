(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow AI_memtoshadow AI_mem_is_zero.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition region_is_poisoned_entry : Z := 0x55c0c.
End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition range_in_mem (SB A n : Z) : Prop :=
  (0 < A /\ A + n < SB) \/ (SB + 0x100000000000 <= A /\ A + n <= A_HIGHEND_VAL).

Definition region_is_poisoned_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n SB : Z) (ws : list byte) (lo : Z).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 80.
Hypothesis HN : 65 <= n < 2^40.
Hypothesis HAN : A + n < 2^47.
Hypothesis RIM : range_in_mem SB A n.
Hypothesis SHL : Z.of_nat (length ws) = shw_hi SB A n - shw_lo SB A.
Hypothesis RC : range_clean SB A n ws.
Hypothesis SBR : 2^24 <= SB < 2^32.
Hypothesis PSTK : forall a k, bv_unsigned sp - 80 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSH : forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k).

Notation POST := (region_is_poisoned_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
Notation g1 := (Z.shiftr A 3).
Notation g2 := (Z.shiftr (A + n + -1) 3).
Notation SBG := (SB + Z.shiftr (al8 (A + 7)) 3).     (* [comment removed for export] *)
Notation SEN := (SB + Z.shiftr (al8 (A + n)) 3).     (* [comment removed for export] *)

Lemma GEO :
  0 <= g1 /\ g1 <= g2 /\ 8 * g1 <= A < 8 * g1 + 8 /\ 8 * g2 <= A + n + -1 < 8 * g2 + 8 /\
  shw_lo SB A <= SB + g1 /\ SB + g1 < shw_lo SB A + 8 /\ shw_lo SB A mod 8 = 0 /\
  shw_hi SB A n - 8 <= SB + g2 /\ SB + g2 < shw_hi SB A n /\ shw_hi SB A n mod 8 = 0 /\
  shw_lo SB A + 8 <= shw_hi SB A n.
Proof. unfold range_in_mem in RIM. exact (shw_geom SB A n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma GEO2 :
  A <= al8 (A + 7) < A + 8 /\ A + n - 8 < al8 (A + n) <= A + n /\
  A <= 8 * Z.shiftr (al8 (A + 7)) 3 /\ 8 * Z.shiftr (al8 (A + 7)) 3 = al8 (A + 7) /\
  8 * Z.shiftr (al8 (A + n)) 3 = al8 (A + n) /\
  g1 <= Z.shiftr (al8 (A + 7)) 3 /\ Z.shiftr (al8 (A + 7)) 3 + 7 <= Z.shiftr (al8 (A + n)) 3 /\
  Z.shiftr (al8 (A + n)) 3 <= g2 + 1.
Proof.
  unfold range_in_mem in RIM. pose proof GEO as GE.
  pose proof (al8_le (A + 7)). pose proof (al8_gt (A + 7)). pose proof (al8_mod (A + 7)).
  pose proof (al8_le (A + n)). pose proof (al8_gt (A + n)). pose proof (al8_mod (A + n)).
  pose proof (shr3_bounds (al8 (A + 7)) ltac:(lia)). pose proof (shr3_bounds (al8 (A + n)) ltac:(lia)).
  repeat split; try lia; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
Lemma rip_from_b88 : forall m0 (j8 : list byte) x1 x5 x11 x12 x13 x14 x15 x16 x17,
  mem_inv asegs m0 -> munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m0 -> wmono asegs m m0 ->
  stk asegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m0 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P POST
    (MS (mkR x1 SP' gp tp x5 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 SEN) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (A + n + -1)) (Z_to_bv 64 SBG) (Z_to_bv 64 (al8 (A + n))) (Z_to_bv 64 A_SBVAR) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55d70) fc None m0 (seg_rom asegs)).
Proof.
  intros m0 j8 x1 x5 x11 x12 x13 x14 x15 x16 x17 MI MU WM SK FR SHB.
  pose proof GEO as GE. pose proof GEO2 as GE2. unfold range_in_mem in RIM. unfold A_SBVAR.
  zstepA. (* [comment removed for export] *) if_cases K0; zify_cond K0. { exfalso. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  callA (mem_is_zero_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SBG (SEN - SBG) (shw_lo SB A) ws lo P).
  1:{ rewrite USP. exact SK. }
  1:{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
  1:{ rewrite USP. lia. }
  1:{ exact MI. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ lia. }
  1:{ exact SHB. }
  1:{ lia. }
  1:{ lia. }
  1:{ lia. }
  1:{ intros i Hi. replace (i - shw_lo SB A) with (SB + (i - SB) - shw_lo SB A) by lia.
      apply (range_clean_full SB A n ws (i - SB)); first [exact RC | lia]. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  1:{ intros a k H1 H2. apply PSH; lia. }
  ret_pc_lit.
  lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into SK2; rewrite USP in SK2 end.
  stepA. (* [comment removed for export] *) if_false.
  zstepA. zstepA. (* [comment removed for export] *)
  do 7 stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  release_frame FR SK2 (bv_unsigned sp).
  finishA.
Qed.

(* [comment removed for export] *)
Lemma rip_from_b18 : forall m0 (j8 : list byte) x1 x5 x11 x12 x13 x14 x15 x16 x17,
  mem_inv asegs m0 -> munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m0 -> wmono asegs m m0 ->
  stk asegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m0 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  icp_globals asegs m0 SB -> bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P POST
    (MS (mkR x1 SP' gp tp x5 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 SEN) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (A + n)) (Z_to_bv 64 SBG) (Z_to_bv 64 (al8 (A + n))) (Z_to_bv 64 A_SBVAR) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55d00) fc None m0 (seg_rom asegs)).
Proof.
  intros m0 j8 x1 x5 x11 x12 x13 x14 x15 x16 x17 MI MU WM SK FR G SHB.
  pose proof GEO as GE. pose proof GEO2 as GE2. unfold range_in_mem in RIM.
  pose proof G as G'. icp_globals_open G. unfold A_SBVAR.
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (range_clean_inner SB A n ws g1 RC ltac:(lia)) as Hk1.
  pose proof (u8ro_read asegs m0 (shw_lo SB A) ws (SB + g1 - shw_lo SB A) _ (Z_to_bv 64 (SB + g1)) SHB Hk1 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD1.
  zstepA. clear RD1. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_true.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  destruct (RC g2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read asegs m0 (shw_lo SB A) ws (SB + g2 - shw_lo SB A) _ (Z_to_bv 64 (SB + g2)) SHB Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD2.
  zstepA. clear RD2. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  if_cases KZ.
  { eapply rip_from_b88; eassumption. }
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases KL; zify_cond KL.
  { eapply rip_from_b88; eassumption. }
  exfalso. rewrite sxb_signed, land7_mod, signed_small64 in KL by (pose proof (Z.mod_pos_bound (A + n + -1) 8); lia).
  assert (bv_signed k2 <> 0) by (intros E; apply (proj2 (sxb_zero_iff k2)) in E; rewrite E in KZ; discriminate).
  lia.
Qed.

(* [comment removed for export] *)
Lemma rip_from_ab0 : forall m0 (j8 : list byte) x5 x10 x13 x14 x15 x16 x17 x18 x19 x20,
  mem_inv asegs m0 -> munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m0 -> wmono asegs m m0 ->
  stk asegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m0 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  icp_globals asegs m0 SB -> bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P POST
    (MS (mkR ra SP' gp tp x5 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 n) x10 (Z_to_bv 64 SB) (Z_to_bv 64 (SB + -1)) x13 x14 x15 x16 x17
              x18 x19 x20 (Z_to_bv 64 A_SBVAR) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55c98) fc None m0 (seg_rom asegs)).
Proof.
  intros m0 j8 x5 x10 x13 x14 x15 x16 x17 x18 x19 x20 MI MU WM SK FR G SHB.
  pose proof GEO as GE. pose proof GEO2 as GE2. unfold range_in_mem in RIM. unfold A_HIGHEND_VAL in RIM.
  pose proof G as G'. icp_globals_open G. unfold A_SBVAR.
  zstepA. (* [comment removed for export] *) replace (n + A) with (A + n) by lia.
  (* [comment removed for export] *)
  assert (CONT : forall x5' x12' x13' x14' x15' x16' x17',
    evtA asegs P POST
      (MS (mkR ra SP' gp tp x5' t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 n) x10 (Z_to_bv 64 SB) x12' x13' x14' x15' x16' x17'
                (Z_to_bv 64 (A + n)) x19 x20 (Z_to_bv 64 711544) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x55ce0) fc None m0 (seg_rom asegs))).
  { intros x5' x12' x13' x14' x15' x16' x17'.
    zstepA. (* [comment removed for export] *) if_cases KC; zify_cond KC. { exfalso. lia. }
    zstepA. zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    rewrite ?land_m8, ?land_m8' by lia.
    stepA. (* [comment removed for export] *)
    callA (memtoshadow_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SB (al8 (A + 7)) P).
    1:{ exact MI. } 1:{ exact G'. }
    1:{ unfold a_in_mem, a_high_mem, A_HIGHEND_VAL. lia. }
    1:{ reflexivity. } 1:{ exact PIMG. }
    ret_pc_lit.
    zstepA. zstepA. (* [comment removed for export] *)
    stepA. (* [comment removed for export] *)
    callA (memtoshadow_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SB (al8 (A + n)) P).
    1:{ assumption. } 1:{ exact G'. }
    1:{ unfold a_in_mem, a_high_mem, A_HIGHEND_VAL. lia. }
    1:{ reflexivity. } 1:{ exact PIMG. }
    ret_pc_lit.
    eapply rip_from_b18; try eassumption. }
  zstepA. (* [comment removed for export] *) if_cases KE; zify_cond KE.
  - apply CONT.
  - (* [comment removed for export] *)
    stepA. stepA. stepA. stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    if_cases KM; zify_cond KM. 2:{ exfalso. revert KM. cbn. lia. }
    stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) if_cases KH1; zify_cond KH1. { exfalso. revert KH1. cbn. lia. }
    zstepA. (* [comment removed for export] *) if_cases KH2; zify_cond KH2. { exfalso. revert KH2. cbn. lia. }
    apply CONT.
Qed.

Lemma region_is_poisoned_body : forall x10 x11,
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  icp_globals asegs m SB -> bytes_at asegs m (shw_lo SB A) ws ->
  x10 = Z_to_bv 64 A -> x11 = Z_to_bv 64 n ->
  evtA asegs P POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 region_is_poisoned_entry) fc None m (seg_rom asegs)).
Proof.
  intros x10 x11 SK MI G SHB -> ->. unfold region_is_poisoned_entry.
  pose proof GEO as GE. unfold range_in_mem in RIM. unfold A_HIGHEND_VAL in RIM.
  assert (MU : munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 64%nat SK.
  do 8 stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport asegs) in G; [ | exact MU | exact WM | cbn; lia ] end.
  pose proof G as G'. icp_globals_open G.
  zstepA. (* [comment removed for export] *) if_cases K0; zify_cond K0. { exfalso. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. stepA. stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  replace (SB <? SB + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
  change ((-1) mod 18446744073709551616) with (Z.ones 64).
  rewrite (Z.land_comm (Z.ones 64)), Z.land_ones, Z.mod_small by lia.
  zstepA. (* [comment removed for export] *) if_cases KB; zify_cond KB.
  - eapply rip_from_ab0; try eassumption.
  - stepA. stepA. stepA. stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    if_cases KM; zify_cond KM. 2:{ exfalso. revert KM. cbn. lia. }
    stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) if_cases KH1; zify_cond KH1. { exfalso. revert KH1. cbn. lia. }
    zstepA. (* [comment removed for export] *) if_cases KH2; zify_cond KH2. { exfalso. revert KH2. cbn. lia. }
    eapply rip_from_ab0; try eassumption.
Qed.
End Walk.

Lemma region_is_poisoned_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n SB : Z) (ws : list byte) (lo : Z) (P : acc -> Prop),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv asegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 65 <= n < 2^40 -> A + n < 2^47 -> range_in_mem SB A n ->
  icp_globals asegs m SB ->
  shadow_window asegs m SB A n ws -> range_clean SB A n ws ->
  (forall a k, bv_unsigned sp - 80 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (region_is_poisoned_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 region_is_poisoned_entry) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros SK LOC LO MI HA0 HA1 HN HAN RIM G SHW RC PSTK PIMG PSH.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  assert (SBR : 2^24 <= SB < 2^32) by (unfold icp_globals in G; tauto).
  destruct SHW as [SHB SHL].
  eapply region_is_poisoned_body; eassumption.
Qed.
End RC__2.
