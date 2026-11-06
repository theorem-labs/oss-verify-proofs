(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells Step Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cu (w : word) : Z := bv_unsigned w mod 2^32.

(* [comment removed for export] *)
Lemma cu_of_Z : forall c, 0 <= c < 2^32 -> cu (Z_to_bv 64 c) = c.
Proof. intros c Hc. unfold cu. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Lemma Forall_cu_of_Z : forall cs, Forall (fun c => 0 < c < 2^32) cs -> Forall (fun w => cu w <> 0) (map (Z_to_bv 64) cs).
Proof.
  intros cs H. induction H as [|c cs Hc H IH]; cbn; constructor; [|exact IH].
  rewrite cu_of_Z by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_eqb0 : forall w, bv_eqb (sx32 w) (Z_to_bv 64 0) = (cu w =? 0).
Proof.
  intros w. unfold sx32, cu, bv_eqb. rewrite !Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  cbn -[Z.modulo Z.add Z.sub Z.mul Z.pow bv_unsigned Z.eqb Z.le Z.lt] in *.
  change (2^32 `div` 2) with (2^31).
  destruct (Z.eqb_spec (bv_unsigned w mod 2^32) 0) as [E|NE].
  - apply Z.eqb_eq. Z.div_mod_to_equations. nia.
  - apply Z.eqb_neq. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma u32ro_read : forall segs m A ws (i : Z) w a,
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
  intros segs m A ws i w a STR Hn Hi ->.
  (nd_pre (u32s_split _ _ _ Hn) 6%nat; intros pre post E Hlen Eu Hlu; nd_post).
  replace (4 * i) with (Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 STR).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32s_of_bytes : forall k (bs : list byte), length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32s ws = bs.
Proof.
  induction k as [|k IH]; intros bs HL.
  - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
  - (nd_pre (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) 3%nat; intros ws Hlen Hu; nd_post).
    exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
    cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
  u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32s ws = bs /\ u32arr segs m A ws.
Proof.
  intros segs m A bs k [Hb Hw] HL.
  (nd_pre (u32s_of_bytes k bs HL) 3%nat; intros ws Hlen Hu; nd_post). exists ws. split; [exact Hlen|]. split; [exact Hu|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (4 * Z.of_nat k) with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof.
  intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length.
  replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma cu_le_bytes_to_word : forall bs : list byte, length bs = 4%nat ->
  cu (le_bytes_to_word bs) = le_val (map bv_unsigned bs).
Proof.
  intros bs HL. unfold cu, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite bytes_le_to_Z_le_val.
  rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cu (w : word) : Z := bv_unsigned w mod 2^32.

(* [comment removed for export] *)
Lemma cu_of_Z : forall c, 0 <= c < 2^32 -> cu (Z_to_bv 64 c) = c.
Proof. intros c Hc. unfold cu. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Lemma Forall_cu_of_Z : forall cs, Forall (fun c => 0 < c < 2^32) cs -> Forall (fun w => cu w <> 0) (map (Z_to_bv 64) cs).
Proof.
  intros cs H. induction H as [|c cs Hc H IH]; cbn; constructor; [|exact IH].
  rewrite cu_of_Z by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_eqb0 : forall w, bv_eqb (sx32 w) (Z_to_bv 64 0) = (cu w =? 0).
Proof.
  intros w. unfold sx32, cu, bv_eqb. rewrite !Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  cbn -[Z.modulo Z.add Z.sub Z.mul Z.pow bv_unsigned Z.eqb Z.le Z.lt] in *.
  change (2^32 `div` 2) with (2^31).
  destruct (Z.eqb_spec (bv_unsigned w mod 2^32) 0) as [E|NE].
  - apply Z.eqb_eq. Z.div_mod_to_equations. nia.
  - apply Z.eqb_neq. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma u32ro_read : forall segs m A ws (i : Z) w a,
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
  intros segs m A ws i w a STR Hn Hi ->.
  (nd_pre (u32s_split _ _ _ Hn) 6%nat; intros pre post E Hlen Eu Hlu; nd_post).
  replace (4 * i) with (Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 STR).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32s_of_bytes : forall k (bs : list byte), length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32s ws = bs.
Proof.
  induction k as [|k IH]; intros bs HL.
  - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
  - (nd_pre (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) 3%nat; intros ws Hlen Hu; nd_post).
    exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
    cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
  u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32s ws = bs /\ u32arr segs m A ws.
Proof.
  intros segs m A bs k [Hb Hw] HL.
  (nd_pre (u32s_of_bytes k bs HL) 3%nat; intros ws Hlen Hu; nd_post). exists ws. split; [exact Hlen|]. split; [exact Hu|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (4 * Z.of_nat k) with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof.
  intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length.
  replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma cu_le_bytes_to_word : forall bs : list byte, length bs = 4%nat ->
  cu (le_bytes_to_word bs) = le_val (map bv_unsigned bs).
Proof.
  intros bs HL. unfold cu, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite bytes_le_to_Z_le_val.
  rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.
End TwB.
