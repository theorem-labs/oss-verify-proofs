(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
     AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums L5Defs L5Core L5CoreKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Sums_u PnSrcSMemmove_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModelFacts.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMTK.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b) 256) by lia. rewrite Z.add_0_l. exact IH.
Qed.

Section Generic.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u64_of_defined (M : word -> option byte) a : 0 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8 ->
  exists w, 0 <= w < 2 ^ 64 /\ L5.u64_at segs M a w.
Proof.
  intros Ha Hn D. destruct (PMCP.rdn_of_defined segs M 8%nat a Ha ltac:(cbn; lia) D) as (bs & RD & LEN).
  pose proof (bytes_le_to_Z_bound bs) as HB. rewrite LEN in HB. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HB.
  pose proof (bytes_le_to_Z_nonneg bs) as H0.
  exists (bytes_le_to_Z bs). split; [lia|]. unfold L5.u64_at. rewrite RD. f_equal. unfold word_to_le_bytes.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia. rewrite <- LEN. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma u64_low_byte (M : word -> option byte) a w b :
  L5.u64_at segs M a w -> L5.u8_at segs M a b -> 0 <= w < 2 ^ 64 -> 0 <= b < 256 -> w mod 256 = b.
Proof.
  intros W B Hw Hb. pose proof (PMF.u8_of_u64 segs M a w Hw W) as B2. unfold L5.u8_at in B, B2. rewrite B in B2. injection B2 as E.
  change (bv_unsigned (Z_to_bv 8 b) = bv_unsigned (Z_to_bv 8 (w mod 256))) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
  pose proof (Z.mod_pos_bound w 256 ltac:(lia)) as X. rewrite (Z.mod_small b) in E by lia. rewrite (Z.mod_small (w mod 256)) in E by lia. lia.
Qed.
End Generic.

(* [comment removed for export] *)
Lemma short_size w n0 : 0 <= w < 2 ^ 64 -> w mod 256 = 2 * n0 -> 0 <= n0 <= 22 ->
  ((72057594037927936 * w) mod 2 ^ 64) / 144115188075855872 = n0.
Proof.
  intros Hw Hm Hn.
  assert (E : (72057594037927936 * w) mod 2 ^ 64 = 72057594037927936 * (w mod 256)).
  { change (2 ^ 64) with (72057594037927936 * 256). rewrite Z.mul_mod_distr_l by lia. reflexivity. }
  rewrite E, Hm. replace (72057594037927936 * (2 * n0)) with (n0 * 144115188075855872) by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma fill_run (fx : FPState) R M (dst n r : Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 12) = Z_to_bv 64 n ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  0 <= n -> 0 <= dst -> dst + n < 2 ^ 63 -> L5.writable RSEGS M dst n ->
  exists R3 M3, msteps RSEGS (st fx R 0xaba00 M) (st fx R3 r M3)
    /\ mem_grows M M3
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + n) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ L5.defined M3 dst n
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
  intros H10 H12 H1 RA Hn Hd Hdn W.
  set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr R (reg 11)))) (Z.to_nat n)).
  assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
  destruct (src0_fill_spec_memset fx M (Z_to_bv 64 dst) (getr R (reg 11)) n R (Z_to_bv 64 r) Hn
              ltac:(rewrite L5.unsigned_lit by lia; lia)
              ltac:(replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
              ltac:(pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as X; change (bv_modulus 64) with (2 ^ 64) in X; unfold AX2.two64; lia)
              (L5K.ret_ok_lit r RA) H1 H10 eq_refl H12) as (R3 & MS & KO & A10).
  exists R3, (wbytes M (Z_to_bv 64 dst) bs). fold bs in MS. split; [exact MS|]. split; [apply wbytes_grows|].
  split. { intros a Ha Hout. apply PMCP.wbytes_out; [lia| rewrite LEN; lia| exact Ha| rewrite LEN, Z2Nat.id by lia; exact Hout]. }
  split. { pose proof (PMCP.wbytes_defined M dst bs Hd ltac:(rewrite LEN; lia)) as X. rewrite LEN, Z2Nat.id in X by lia. exact X. }
  split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.

End PMTK.
