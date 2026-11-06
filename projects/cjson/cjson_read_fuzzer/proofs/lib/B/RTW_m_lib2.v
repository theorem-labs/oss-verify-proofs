(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^56 * 2^8). change (bv_modulus 8) with (2^8).
  rewrite Zaux.Zmod_mod_mult by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac sbfix := rewrite le1_lit; mem_after_store.

(* [comment removed for export] *)
Lemma junk_byte_range : forall (bs : list byte), 0 <= bv_unsigned (zext 64 (bv_extract 0 8 (le_bytes_to_word bs))) < 256.
Proof.
  intros bs. rewrite zext_small, Z_to_bv_unsigned, extract_low_mod by lia. unfold bv_wrap.
  change (2 ^ Z.of_N 8) with 256. change (bv_modulus 64) with (2^64).
  pose proof (Z.mod_pos_bound (bv_unsigned (le_bytes_to_word bs)) 256 ltac:(lia)). rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Definition hdr_b1_mid (hb : Z) : Z := Z.lor (Z.land (Z.lor (Z.land hb 18446744073709551612) 1) 143) 16.
Lemma hdr_b1_mid_chk : forallb (fun hb => (Z.land (hdr_b1_mid hb) 115 =? 17) && (0 <=? hdr_b1_mid hb) && (hdr_b1_mid hb <? 256)) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hdr_b1_mid_ok : forall hb, 0 <= hb < 256 -> Z.land (hdr_b1_mid hb) 115 = 17 /\ 0 <= hdr_b1_mid hb < 256.
Proof.
  intros hb Hhb. pose proof hdr_b1_mid_chk as F. rewrite forallb_forall in F.
  specialize (F hb ltac:(apply in_map_iff; exists (Z.to_nat hb); split; [lia| apply in_seq; lia])).
  apply andb_true_iff in F as [F1 F3]. apply andb_true_iff in F1 as [F1 F2].
  apply Z.eqb_eq in F1. apply Z.leb_le in F2. apply Z.ltb_lt in F3. lia.
Qed.
Definition hdr_b1_fin (b1 : Z) : Z := Z.lor (Z.land b1 243) 0.
Lemma hdr_b1_fin_chk : forallb (fun b => negb (Z.land b 115 =? 17) || ((Z.land (hdr_b1_fin b) 127 =? 17) && (0 <=? hdr_b1_fin b) && (hdr_b1_fin b <? 256))) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hdr_b1_fin_ok : forall b1, 0 <= b1 < 256 -> Z.land b1 115 = 17 -> Z.land (hdr_b1_fin b1) 127 = 17 /\ 0 <= hdr_b1_fin b1 < 256.
Proof.
  intros b1 Hb E. pose proof hdr_b1_fin_chk as F. rewrite forallb_forall in F.
  specialize (F b1 ltac:(apply in_map_iff; exists (Z.to_nat b1); split; [lia| apply in_seq; lia])).
  apply orb_true_iff in F as [F|F]; [apply negb_true_iff in F; apply Z.eqb_neq in F; lia|].
  apply andb_true_iff in F as [F1 F3]. apply andb_true_iff in F1 as [F1 F2].
  apply Z.eqb_eq in F1. apply Z.leb_le in F2. apply Z.ltb_lt in F3. lia.
Qed.

(* [comment removed for export] *)
Lemma c44_c8 : forall m a x, 0 <= x < 2^32 ->
  rw_cells bsegs m a [C4 (wz x); C4 (wz 0)] -> rw_cells bsegs m a [C8 (wz x)].
Proof.
  intros m a x Hx [[Hwf HB] HW]. split; [split; [cbn; tauto|]| exact HW].
  cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *.
  replace (le8 (wz x)) with (le4 (wz x) ++ le4 (wz 0)); [exact HB|].
  unfold le8, le4, wz, word_to_le_bytes. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small x), Z.mod_0_l by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_0_l.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ (8 + 8 + 8 + 8 + 8 + 8 + 8)) with (2^56). change (2 ^ (8 + 8 + 8 + 8 + 8 + 8)) with (2^48).
  change (2 ^ (8 + 8 + 8 + 8 + 8)) with (2^40). change (2 ^ (8 + 8 + 8 + 8)) with (2^32).
  replace (x / 2^32) with 0 by (symmetry; apply Z.div_small; lia).
  replace (x / 2^40) with 0 by (symmetry; apply Z.div_small; lia).
  replace (x / 2^48) with 0 by (symmetry; apply Z.div_small; lia).
  replace (x / 2^56) with 0 by (symmetry; apply Z.div_small; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_m1_7 : forall x, 0 <= x < 2^64 -> Z.land (Z.land x 18446744073709551615) 7 = x mod 8.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma land_48m8 : forall x, 0 <= x < 2^32 -> Z.land x 281474976710648 = x / 8 * 8.
Proof.
  intros x Hx. replace 281474976710648 with (Z.land (Z.ones 48) 18446744073709551608) by reflexivity.
  rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  replace 18446744073709551608 with ((-8) mod 2^64) by reflexivity.
  rewrite land_mod_pow2_r by lia. replace (-8) with (Z.lnot (Z.ones 3)) by reflexivity. rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac sbfix := rewrite le1_lit; mem_after_store.
