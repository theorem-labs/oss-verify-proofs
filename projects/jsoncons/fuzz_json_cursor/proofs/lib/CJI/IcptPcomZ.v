(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm8RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Cells Exec Frame Step Tac ZBridge Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F8 Require Import F_memcpy F_fmt_fp_lib F_printf_iface.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJM Require Import ShZero QcF IcptCells IcptCellsA RdnCells ShLoads.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJI Require Import IcptPcomS IcptPcomR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac lit_branch := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
  let c' := eval vm_compute in c in change c with c'; cbv iota end.

Ltac zs := zstep; try lit_branch.

Lemma roCB8_of_rdn : forall (m : word -> option byte) a w, rdn rsegs m (Z_to_bv 64 a) 8%nat = Some w -> 0 <= a -> a + 8 <= 2^64 -> ro_cells rsegs m a [CB 8 w].
Proof.
  intros m a w H H0 H1. pose proof (rdn_length _ _ _ _ _ H) as L. split.
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (rdn_bytes_at rsegs 8 m a); [exact H | lia | cbn; lia].
Qed.
Lemma ro1_of_some : forall (m : word -> option byte) a b, m (Z_to_bv 64 a) = Some b -> 0 <= a -> a + 1 <= 2^64 -> ro_cells rsegs m a [C1 b].
Proof. intros m a b H H0 H1. apply ro1_of_rdn; [| exact H0 | exact H1]. cbn [rdn]. rewrite H. reflexivity. Qed.
Lemma sh_word_addr : forall p, 0 <= p < 2^61 ->
  Z.land (Z.land (Pm8RegionPoisoned.SB + p ≫ 3) 18446744073709551615) 18446744073709551608 = (Pm8RegionPoisoned.SB + p / 8) - (Pm8RegionPoisoned.SB + p / 8) mod 8.
Proof.
  intros p Hp. unfold Pm8RegionPoisoned.SB. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= p / 8 < 2 ^ 58) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite land_round8 by lia. pose proof (Z.div_mod (2147450880 + p / 8) 8 ltac:(lia)). lia.
Qed.
Lemma sh_word_addr1 : forall p, 0 <= p < 2^61 ->
  Z.land (Pm8RegionPoisoned.SB + p ≫ 3) 18446744073709551608 = (Pm8RegionPoisoned.SB + p / 8) - (Pm8RegionPoisoned.SB + p / 8) mod 8.
Proof.
  intros p Hp. unfold Pm8RegionPoisoned.SB. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= p / 8 < 2 ^ 58) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite land_m8' by lia. pose proof (Z.div_mod (2147450880 + p / 8) 8 ltac:(lia)). lia.
Qed.
Lemma sh_word_range1 : forall p, 0 <= p < 2^61 ->
  0 <= Z.land (Pm8RegionPoisoned.SB + p ≫ 3) 18446744073709551608
  /\ Z.land (Pm8RegionPoisoned.SB + p ≫ 3) 18446744073709551608 <= Pm8RegionPoisoned.SB + p / 8.
Proof.
  intros p Hp. rewrite sh_word_addr1 by exact Hp. unfold Pm8RegionPoisoned.SB.
  pose proof (Z.mod_pos_bound (2147450880 + p / 8) 8 ltac:(lia)).
  assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia.
Qed.
Lemma sh_word_range : forall p, 0 <= p < 2^61 ->
  0 <= Z.land (Z.land (Pm8RegionPoisoned.SB + p ≫ 3) 18446744073709551615) 18446744073709551608
  /\ Z.land (Z.land (Pm8RegionPoisoned.SB + p ≫ 3) 18446744073709551615) 18446744073709551608 <= Pm8RegionPoisoned.SB + p / 8.
Proof.
  intros p Hp. rewrite sh_word_addr by exact Hp. unfold Pm8RegionPoisoned.SB.
  pose proof (Z.mod_pos_bound (2147450880 + p / 8) 8 ltac:(lia)).
  assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia.
Qed.

Ltac to_pr1 := eapply pr1; try eassumption; lia.

Theorem pcom_ok : pcom_stmt.
Proof.
  unfold pcom_stmt. intros until lo. cbv zeta.
  intros -> -> BY HA0 HA SK ST LO HLO HQ AE MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  unfold PCOM_DEPTH in LO.
  assert (FM : ro_cells rsegs m A [CB 6 (zb FMT_G)]) by (split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BY]).
  cbn [zb FMT_G map] in FM.
  clear BY.
  pose proof (aenv_rt _ AE) as (G1 & G2 & _).
  replace (0x153138%bv : word) with (Z_to_bv 64 0x153138) in G1 by (apply bv_eq; reflexivity).
  replace (0x15c9b8%bv : word) with (Z_to_bv 64 0x15c9b8) in G2 by (apply bv_eq; reflexivity).
  pose proof (ro8_of_rdn rsegs m 0x153138 _ G1 ltac:(lia) ltac:(lia)) as RG1.
  pose proof (ro8_of_rdn rsegs m 0x15c9b8 _ G2 ltac:(lia) ltac:(lia)) as RG2.
  clear G1 G2.
  destruct (shk_k rsegs m A 6 SK) as (k & Hk & Hkr & Hz & Hw).
  specialize (Hk ltac:(lia)). specialize (Hz ltac:(lia)). destruct (Hw ltac:(lia)) as (w0 & w1 & W0 & W1). clear Hw SK.
  replace (A + 6 - 1) with (5 + A) in Hk, Hz, W1, Hkr by lia.
  rewrite <- sh_word_addr1 in W0 by lia. rewrite <- sh_word_addr1 in W1 by lia.
  assert (HSB : Pm8RegionPoisoned.SB = 2147450880) by reflexivity.
  assert (D8a : 0 <= A / 8 <= 0x30000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (D8b : 0 <= (5 + A) / 8 <= 0x30000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (D8c : A ≫ 3 = A / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (D8d : (5 + A) ≫ 3 = (5 + A) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (sh_word_range1 A ltac:(lia)) as [R0a R0b]. destruct (sh_word_range1 (5 + A) ltac:(lia)) as [R1a R1b].
  pose proof (roCB8_of_rdn m _ w0 W0 R0a ltac:(lia)) as RW0.
  pose proof (roCB8_of_rdn m _ w1 W1 R1a ltac:(lia)) as RW1. clear W0 W1.
  replace ((5 + A) / 8) with ((5 + A) ≫ 3) in Hk by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof (ro1_of_some m _ _ Hk ltac:(lia) ltac:(lia)) as RK.
  clear Hk.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 104%nat ST.
  zstep.
  do 13 zstep.
  do 6 zstep.
  do 30 zs.
  zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. rewrite zb_lxor_ones in K1 by lia. lia. }
  zstep. zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
  do 9 zstep.
  zstep. zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3.
  2:{   to_pr1. }

  set (yk := Pm8RegionPoisoned.SB + (5 + A) ≫ 3) in *. set (y0 := Pm8RegionPoisoned.SB + A ≫ 3) in *.
  do 7 zstep.
  assert (Hk8 : bv_unsigned (sxb (Z_to_bv 8 k)) = k).
  { destruct Hkr as [-> | Hkr]; [reflexivity|]. assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) as HK by lia.
    repeat destruct HK as [-> | HK]; try (subst k); reflexivity. }
  rewrite Hk8.
  assert (PL : Z.land (Z.b2z (0 <? k)) (Z.lxor (Z.b2z (Z.lxor (Z.land (5 + A) 7) 9223372036854775808 <? Z.lxor k 9223372036854775808)) 1) = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (5 + A) 8 ltac:(lia)) as M8.
    destruct Hkr as [-> | Hkr]; [reflexivity|].
    replace (Z.lxor ((5 + A) mod 8) 9223372036854775808) with ((5 + A) mod 8 + 9223372036854775808)
      by (change 9223372036854775808 with (2 ^ 63); rewrite zb_lxor_pow2_small by lia; reflexivity).
    replace (Z.lxor k 9223372036854775808) with (k + 9223372036854775808) by (change 9223372036854775808 with (2 ^ 63); rewrite zb_lxor_pow2_small by lia; reflexivity).
    replace (0 <? k) with true by (symmetry; apply Z.ltb_lt; lia).
    replace ((5 + A) mod 8 + 9223372036854775808 <? k + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  rewrite PL.
  if_cases K4; zify_cond K4.
  -
    zs. zs. to_pr1.
  -
    assert (RZ : ro_cells rsegs m0 y0 [C1 (Z_to_bv 8 0)]).
    { apply ro1_of_some; [| unfold y0; lia | unfold y0; lia].
      rewrite (MU (Z_to_bv 64 y0)).
      + apply Hz. rewrite unsigned_lit by (unfold y0; lia). unfold y0. lia.
      + cbn [outside]. rewrite unsigned_lit by (unfold y0; lia). unfold y0. split; [lia | exact I]. }
    zstep. zstep. zstep. zstep. if_cases K5; zify_cond K5.
    + exfalso. assert (Y : yk <= y0 + 1).
      { unfold yk, y0. rewrite D8c, D8d. pose proof (Z.div_mod A 8 ltac:(lia)). pose proof (Z.div_mod (5 + A) 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound A 8 ltac:(lia)). pose proof (Z.mod_pos_bound (5 + A) 8 ltac:(lia)). lia. }
      lia.
    + zs. zs. to_pr1.
Qed.
