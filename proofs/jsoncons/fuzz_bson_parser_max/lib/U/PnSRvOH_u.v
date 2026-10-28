(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac WalkTac L5Defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSRVOH.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Definition TABLE : Z := 80496.

(* [comment removed for export] *)
Definition tabb (b : Z) : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2 with Some bs => bs | None => [] end.
Definition tab_clear (M : mem) : Prop := forall x : word, TABLE <= bv_unsigned x < TABLE + 512 -> M x = None.

Lemma tabb_all : forallb (fun i => let b := Z.of_nat i in
    match rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2 with
    | Some bs => Nat.eqb (length bs) 2 && (0 <=? bytes_le_to_Z bs) && (bytes_le_to_Z bs <? 65536) | None => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tabb_ok b : 0 <= b < 256 -> rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2 = Some (tabb b) /\ 0 <= bytes_le_to_Z (tabb b) < 65536.
Proof.
  intros Hb. pose proof tabb_all as A. rewrite forallb_forall in A.
  specialize (A (Z.to_nat b) ltac:(apply in_seq; lia)). cbv beta zeta in A. rewrite Z2Nat.id in A by lia. unfold tabb.
  destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2) as [bs|]; [| discriminate A].
  apply andb_prop in A as [A B2]. apply andb_prop in A as [A1 A2]. split; [reflexivity|]. apply Z.leb_le in A2. apply Z.ltb_lt in B2. lia.
Qed.
Lemma rdn_clear2 (M : mem) a : tab_clear M -> TABLE <= a -> a + 2 <= TABLE + 512 ->
  rdn RSEGS M (Z_to_bv 64 a) 2 = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 2.
Proof.
  intros TC H1 H2. unfold tab_clear, TABLE in *. cbn [rdn].
  rewrite (TC (Z_to_bv 64 a)) by (rewrite L5.unsigned_lit by lia; lia).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (apply bv_eq; rewrite u_add1 by (rewrite L5.unsigned_lit by lia; lia); rewrite !L5.unsigned_lit by lia; reflexivity).
  rewrite (TC (Z_to_bv 64 (a + 1))) by (rewrite L5.unsigned_lit by lia; lia). reflexivity.
Qed.
Lemma tabb_len b : 0 <= b < 256 -> length (tabb b) = 2%nat.
Proof.
  intros Hb. pose proof tabb_all as A. rewrite forallb_forall in A.
  specialize (A (Z.to_nat b) ltac:(apply in_seq; lia)). cbv beta zeta in A. rewrite Z2Nat.id in A by lia. unfold tabb.
  destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2) as [bs|]; [| discriminate A].
  apply andb_prop in A as [A _]. apply andb_prop in A as [A1 _]. apply Nat.eqb_eq. exact A1.
Qed.
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
Lemma tab_u16 (M : mem) b : tab_clear M -> 0 <= b < 256 ->
  rdn RSEGS M (Z_to_bv 64 (TABLE + 2 * b)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (bytes_le_to_Z (tabb b))))
  /\ 0 <= bytes_le_to_Z (tabb b) < 65536.
Proof.
  intros TC Hb. destruct (tabb_ok b Hb) as (RD & RG). split; [| exact RG].
  rewrite (rdn_clear2 M _ TC) by (unfold TABLE; lia). rewrite RD. f_equal.
  unfold word_to_le_bytes. rewrite L5.unsigned_lit by lia.
  pose proof (Z_to_le_bytes_to_Z (tabb b)) as RT. rewrite (tabb_len b Hb) in RT. symmetry. exact RT.
Qed.
End PNSRVOH.
