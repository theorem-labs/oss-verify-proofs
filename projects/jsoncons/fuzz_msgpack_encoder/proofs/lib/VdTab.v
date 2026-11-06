(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation rsegs := Plain_loaded_segments (only parsing).

Module VDT.

Definition TABF_A : Z := 0x13ba0.
Definition TABE_A : Z := 0x15118.
Definition NTAB : nat := 687.
Definition C_LOG : Z := 0x3FD34413509F79FE.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kcw (x : Z) : word := fcvt_w_d RUP (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 x)) (Z_to_bv 64 C_LOG)).
Definition MK (x : Z) : Z := let r := bv_unsigned (kcw x) in if r <? 2 ^ 63 then r else r - 2 ^ 64.

Lemma kcw_MK x : kcw x = Z_to_bv 64 (MK x).
Proof.
  unfold MK. pose proof (bv_unsigned_in_range _ (kcw x)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  destruct (bv_unsigned (kcw x) <? 2 ^ 63) eqn:E.
  - symmetry. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. symmetry.
    replace (bv_unsigned (kcw x) - 2 ^ 64 + 1 * 2 ^ 64) with (bv_unsigned (kcw x)) by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Definition le_z (bs : list byte) : Z := fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 bs.
Fixpoint chunk (n k : nat) (bs : list byte) : list Z :=
  match n with O => [] | S n' => le_z (firstn k bs) :: chunk n' k (skipn k bs) end.
Definition TABF : list Z := Eval vm_compute in match image_bytes rsegs TABF_A (8 * NTAB) with Some bs => chunk NTAB 8 bs | None => [] end.
Definition TABE : list Z := Eval vm_compute in match image_bytes rsegs TABE_A (4 * NTAB) with Some bs => chunk NTAB 4 bs | None => [] end.
Definition TABFw : list word := map (Z_to_bv 64) TABF.
Definition TABEw : list word := map (Z_to_bv 64) TABE.      (* [comment removed for export] *)
Definition s32 (z : Z) : Z := if z <? 2 ^ 31 then z else z - 2 ^ 32.

Lemma TABF_ro : ro_bytes_b rsegs TABF_A (u64s TABFw) = true. Proof. vm_compute. reflexivity. Qed.
Lemma TABE_ro : ro_bytes_b rsegs TABE_A (u32s TABEw) = true. Proof. vm_compute. reflexivity. Qed.

Definition chk (x : Z) : bool :=
  let mk := MK x in
  (-307 <=? mk) && (mk <=? 325) &&
  match nth_error TABF (Z.to_nat (343 + mk)), nth_error TABE (Z.to_nat (343 + mk)) with
  | Some c, Some ce => (2 ^ 63 <=? c) && (c <? 2 ^ 64) && (ce <? 2 ^ 32) && (0 <=? ce) && (-59 <=? 4 - x + s32 ce) && (4 - x + s32 ce <=? -56)
  | _, _ => false
  end.
Definition XLO : Z := -1021.
Definition XN : nat := 2099.
Lemma chk_all : forallb chk (map (fun i => XLO + Z.of_nat i) (seq 0 XN)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_x x : -1021 <= x <= 1077 -> chk x = true.
Proof.
  intros H. pose proof chk_all as A. rewrite forallb_forall in A. apply A.
  apply in_map_iff. exists (Z.to_nat (x - XLO)). unfold XLO, XN. split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma kc_facts x : -1021 <= x <= 1077 ->
  exists mk c ce, kcw x = Z_to_bv 64 mk /\ -307 <= mk <= 325
    /\ nth_error TABFw (Z.to_nat (343 + mk)) = Some (Z_to_bv 64 c) /\ nth_error TABEw (Z.to_nat (343 + mk)) = Some (Z_to_bv 64 ce)
    /\ 2 ^ 63 <= c < 2 ^ 64 /\ 0 <= ce < 2 ^ 32 /\ -59 <= 4 - x + s32 ce <= -56.
Proof.
  intros H. pose proof (chk_x x H) as C. unfold chk in C. cbv zeta in C.
  exists (MK x). rewrite kcw_MK.
  apply andb_prop in C. destruct C as [C1 C2]. apply andb_prop in C1. destruct C1 as [C0 C1].
  destruct (nth_error TABF (Z.to_nat (343 + MK x))) as [c|] eqn:EF; [|discriminate].
  destruct (nth_error TABE (Z.to_nat (343 + MK x))) as [ce|] eqn:EE; [|discriminate].
  exists c, ce. split; [reflexivity|].
  repeat (apply andb_prop in C2; destruct C2 as [C2 ?]).
  split; [lia|]. split; [unfold TABFw; rewrite nth_error_map, EF; reflexivity|].
  split; [unfold TABEw; rewrite nth_error_map, EE; reflexivity|]. lia.
Qed.

(* [comment removed for export] *)
Section Reads.
Context {bmK : BMode.BMode}.
Variable m : word -> option byte.
Hypothesis MI : mem_inv rsegs m.

Lemma tabf_read (i : Z) (w : word) (a : word) :
  nth_error TABFw (Z.to_nat i) = Some w -> 0 <= i -> a = wa (TABF_A + 8 * i) -> ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros Hn Hi ->.
  assert (Hb : bytes_at rsegs m TABF_A (u64s TABFw)).
  { apply ro_bytes_at; [exact MI | unfold TABF_A; lia | rewrite u64s_length; unfold TABFw; rewrite length_map; vm_compute; discriminate |].
    apply ro_bytes_b_sound. exact TABF_ro. }
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m TABF_A (u64s TABFw) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma tabe_read (i : Z) (w : word) (a : word) :
  nth_error TABEw (Z.to_nat i) = Some w -> 0 <= i -> a = wa (TABE_A + 4 * i) -> ov_read_bytes rsegs m a 4 = Some (le4 w).
Proof.
  intros Hn Hi ->.
  assert (Hb : bytes_at rsegs m TABE_A (u32s TABEw)).
  { apply ro_bytes_at; [exact MI | unfold TABE_A; lia | rewrite u32s_length; unfold TABEw; rewrite length_map; vm_compute; discriminate |].
    apply ro_bytes_b_sound. exact TABE_ro. }
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m TABE_A (u32s TABEw) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
End Reads.

End VDT.
