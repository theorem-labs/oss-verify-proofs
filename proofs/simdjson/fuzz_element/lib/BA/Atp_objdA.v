(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma obj_land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5) with 32. lia.
Qed.
Lemma obj_land_m32u : forall x, 0 <= x < 2^64 -> x mod 16 = 0 ->
  exists d, (d = 0 \/ d = 16) /\ Z.land x 18446744073709551584 = x - d /\ (x - d) mod 32 = 0.
Proof.
  intros x Hx X16. rewrite obj_land_m32 by lia. exists (x mod 32).
  split; [| split]; Z.div_mod_to_equations; lia.
Qed.
Lemma rw_cells_nil_CB' : forall (m : mem) A, 0 <= A < 2^64 -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A HA. split; [split; [cbn; auto|]|].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition obj_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition obj_W (q out f : Z) : list (Z * Z) := [(q + -304, q); (out, out + 24); (f, f + 120); (shad f, shad f + 16)].

Definition obj_W0 (q : Z) : list (Z * Z) := [(q + -304, q)].

Definition OBJ_SM1_RA : Z := 0xb5ec8.
Definition LIT_SLASH_A : Z := 0x23800.
Definition LIT_TILDE_A : Z := 0x23820.

Lemma find_byte_zlist_SomeA : forall c (l : list Z) n ix, Forall (fun x => 0 <= x < 256) l -> 0 <= c < 256 ->
  find_byte c (firstn n (map (Z_to_bv 8) l)) = Some ix ->
  (ix < length l)%nat /\ (ix < n)%nat /\ nth ix l 0 = c /\ (forall j, (j < ix)%nat -> nth j l 0 <> c).
Proof.
  intros c l n ix HF Hc H. destruct (find_byte_Some _ _ _ H) as (Hl & (b & Hb & Hbc) & Hmin).
  rewrite length_firstn, length_map in Hl.
  assert (L1 : (ix < length l)%nat) by lia. assert (L2 : (ix < n)%nat) by lia.
  split; [exact L1|]. split; [exact L2|]. split.
  - rewrite nth_error_firstn in Hb. replace (ix <? n)%nat with true in Hb by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_map, (nth_error_nth' l 0 L1) in Hb. cbn in Hb. injection Hb as EB. rewrite <- EB in Hbc.
    pose proof (Forall_nth_Z _ l ix HF L1) as R. rewrite a_u8_small in Hbc by exact R. exact Hbc.
  - intros j Hj EQ. apply (Hmin j (Z_to_bv 8 (nth j l 0)) Hj).
    + rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia. reflexivity.
    + rewrite a_u8_small; [exact EQ|]. apply Forall_nth_Z; [exact HF| lia].
Qed.
Lemma find_byte_zlist_NoneA : forall c (l : list Z) n, Forall (fun x => 0 <= x < 256) l -> 0 <= c < 256 ->
  find_byte c (firstn n (map (Z_to_bv 8) l)) = None -> forall j, (j < n)%nat -> (j < length l)%nat -> nth j l 0 <> c.
Proof.
  intros c l n HF Hc H j Hj Hl EQ. apply (find_byte_None _ _ H j (Z_to_bv 8 (nth j l 0))).
  - rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia. reflexivity.
  - rewrite a_u8_small; [exact EQ|]. apply Forall_nth_Z; [exact HF| lia].
Qed.
Lemma find_or_foundA : forall y x, 0 < y -> Z.lor (Z.land (Z.b2z (0 <? y) + -1) 18446744073709551615) x = x.
Proof.
  intros y x Hy. replace (0 <? y) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. change (1 + -1) with 0.
  rewrite Z.land_0_l. apply Z.lor_0_l.
Qed.
Lemma find_or_nposA : forall x, 0 <= x < 2^64 -> Z.lor (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) x = 18446744073709551615.
Proof.
  intros x Hx. cbn [Z.ltb Z.compare Z.b2z]. change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  pose proof (Z.add_lor_land 18446744073709551615 x) as EQ.
  rewrite (Z.land_comm 18446744073709551615 x) in EQ. rewrite land64_mod, Z.mod_small in EQ by lia. lia.
Qed.
