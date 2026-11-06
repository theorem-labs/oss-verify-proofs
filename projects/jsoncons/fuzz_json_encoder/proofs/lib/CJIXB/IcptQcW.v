(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm5RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Cells Exec Frame Step Tac ZBridge Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F5 Require Import F_memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMXB Require Import ShZero QcF IcptCells RdnCells ShLoads.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJIXB Require Import IcptPcomZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac lit_branch := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
  let c' := eval vm_compute in c in change c with c'; cbv iota end.

Section QC.
Variable Q : machine_state -> Prop.
Variables ra sp gp tp t0 t1 t2 s0 a0 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D c : Z).
Hypothesis HC : forall a1' a2' a3' a4' a5' : word,
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 c) a0 a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x70a7c) fc None m (seg_rom rsegs)).

Lemma qc_loop : forall (k : nat) (x y : Z) (a2v a4 a5 : word),
  Z.to_nat (y - x) = k -> 0 <= x < y -> y < 2^64 -> a2v = Z_to_bv 64 y ->
  (forall z, x <= z < y -> m (Z_to_bv 64 z) = Some (Z_to_bv 8 0)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 c) a0 (Z_to_bv 64 x) a2v (Z_to_bv 64 0) a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9
                       s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x70b9c) fc None m (seg_rom rsegs)).
Proof.
  induction k as [k IH] using lt_wf_ind.
  intros x y a2v a4 a5 Hk Hxy Hy -> HZ.
  assert (RZ : ro_cells rsegs m x [C1 (Z_to_bv 8 0)]) by (apply ro1_of_some; [apply HZ; lia | lia | lia]).
  zstep. zstep. zstep. zstep.
  if_cases K1; zify_cond K1.
  -
    eapply (IH (Z.to_nat (y - (x + 1))) ltac:(lia) (x + 1) y); [reflexivity | lia | lia | reflexivity | intros z Hz; apply HZ; lia].
  - zstep. zstep. lit_branch. apply HC.
Qed.

Hypothesis SK : shk rsegs m D c.
Hypothesis Hc : 1 <= c <= 64.
Hypothesis HD : 0 <= D /\ D + c <= 2^47.
Hypothesis RL : Pm5RegionPoisoned.rt_layout_globs m.

Lemma qc_write : forall a1 a2 a3 a4 a5 : word,
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x70a34) fc None m (seg_rom rsegs)).
Proof.
  intros a1 a2 a3 a4 a5.
  pose proof RL as (G1 & G2 & _).
  replace (0x164518%bv : word) with (Z_to_bv 64 0x164518) in G1 by (apply bv_eq; reflexivity).
  replace (0x16d7b8%bv : word) with (Z_to_bv 64 0x16d7b8) in G2 by (apply bv_eq; reflexivity).
  pose proof (ro8_of_rdn rsegs m 0x164518 _ G1 ltac:(lia) ltac:(lia)) as RG1.
  pose proof (ro8_of_rdn rsegs m 0x16d7b8 _ G2 ltac:(lia) ltac:(lia)) as RG2.
  clear G1 G2.
  destruct (shk_k rsegs m D c SK) as (k & Hk & Hkr & Hz & Hw).
  specialize (Hk ltac:(lia)). specialize (Hz ltac:(lia)). destruct (Hw ltac:(lia)) as (w0 & w1 & W0 & W1). clear Hw.
  replace (D + c - 1) with (D + c + -1) in Hk, Hz, W1, Hkr by lia.
  assert (R0 : 0 <= D < 2^61) by lia. assert (R1 : 0 <= D + c + -1 < 2^61) by lia.
  pose proof W0 as W0s. pose proof W1 as W1s.
  rewrite <- (sh_word_addr D R0) in W0. rewrite <- (sh_word_addr (D + c + -1) R1) in W1.
  rewrite <- (sh_word_addr1 D R0) in W0s. rewrite <- (sh_word_addr1 (D + c + -1) R1) in W1s.
  destruct (sh_word_range D R0) as [R0a R0b]. destruct (sh_word_range (D + c + -1) R1) as [R1a R1b].
  destruct (sh_word_range1 D R0) as [R0c R0d]. destruct (sh_word_range1 (D + c + -1) R1) as [R1c R1d].
  assert (D8a : 0 <= D / 8 <= 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (D8b : 0 <= (D + c + -1) / 8 <= 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (D8c : D ≫ 3 = D / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (D8d : (D + c + -1) ≫ 3 = (D + c + -1) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (HSB : Pm5RegionPoisoned.SB = 2147450880) by reflexivity.
  pose proof (roCB8_of_rdn m _ w0 W0 R0a ltac:(lia)) as RW0.
  pose proof (roCB8_of_rdn m _ w1 W1 R1a ltac:(lia)) as RW1. clear W0 W1.
  pose proof (roCB8_of_rdn m _ w0 W0s R0c ltac:(lia)) as RW0s.
  pose proof (roCB8_of_rdn m _ w1 W1s R1c ltac:(lia)) as RW1s. clear W0s W1s.
  replace ((D + c + -1) / 8) with ((D + c + -1) ≫ 3) in Hk by exact D8d.
  pose proof (ro1_of_some m _ _ Hk ltac:(lia) ltac:(lia)) as RK. clear Hk.
  change F_memset.rsegs with rsegs in RW0, RW1, RW0s, RW1s, RK.
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  { exfalso. change 18446744073709551615 with (2^64 - 1) in K1. rewrite zb_land_mask in K1 by lia.
    pose proof (Z.mod_pos_bound (c + -65) (2^64) ltac:(lia)). pose proof (Z.div_mod (c + -65) (2^64) ltac:(lia)). lia. }
  do 15 zstep.
  if_cases K2; zify_cond K2.
  2:{   apply HC. }

  set (yk := Pm5RegionPoisoned.SB + (D + c + -1) ≫ 3) in *. set (y0 := Pm5RegionPoisoned.SB + D ≫ 3) in *.
  do 6 zstep.
  assert (Hk8 : bv_unsigned (sxb (Z_to_bv 8 k)) = k).
  { destruct Hkr as [-> | Hkr]; [reflexivity|]. assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) as HK by lia.
    repeat destruct HK as [-> | HK]; try (subst k); reflexivity. }
  rewrite Hk8.
  assert (PL : Z.land (Z.b2z (0 <? k)) (Z.lxor (Z.b2z (Z.lxor (Z.land (D + c + -1) 7) 9223372036854775808 <? Z.lxor k 9223372036854775808)) 1) = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (D + c + -1) 8 ltac:(lia)) as M8.
    destruct Hkr as [-> | Hkr]; [reflexivity|].
    replace (Z.lxor ((D + c + -1) mod 8) 9223372036854775808) with ((D + c + -1) mod 8 + 9223372036854775808)
      by (change 9223372036854775808 with (2 ^ 63); rewrite zb_lxor_pow2_small by lia; reflexivity).
    replace (Z.lxor k 9223372036854775808) with (k + 9223372036854775808) by (change 9223372036854775808 with (2 ^ 63); rewrite zb_lxor_pow2_small by lia; reflexivity).
    replace (0 <? k) with true by (symmetry; apply Z.ltb_lt; lia).
    replace ((D + c + -1) mod 8 + 9223372036854775808 <? k + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  rewrite PL.
  zstep. if_cases K3; zify_cond K3.
  -
    zstep. zstep. lit_branch. apply HC.
  -
    assert (Y0 : 0 <= y0) by (unfold y0; lia). assert (YK : yk < 2^64) by (unfold yk; lia).
    eapply (qc_loop (Z.to_nat (yk - y0)) y0 yk); [reflexivity | lia | lia | reflexivity |].
    intros z Hz'. apply Hz. rewrite unsigned_lit by lia. unfold y0, yk in Hz'. rewrite D8c, D8d in Hz'. lia.
Qed.
End QC.
