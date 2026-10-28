(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_W3_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bytes_le_to_Z_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 256 ^ Z.of_nat (length bs).
Proof.
  intros bs. rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as H. rewrite length_map in H. exact H.
Qed.

Lemma le_bytes_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_range bs) as [Hr _].
  rewrite lor_shiftl8_add by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.mul_comm, Z_div_plus_full by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.

(* [comment removed for export] *)
Lemma le8_of_junk : forall bs : list byte, length bs = 8%nat -> cbytes (C8 (le_bytes_to_word bs)) = bs.
Proof.
  intros bs L. cbn [cbytes]. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range bs) as Hr. rewrite L in Hr. change (256 ^ Z.of_nat 8) with (2 ^ 64) in Hr.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  rewrite <- L. apply le_bytes_roundtrip.
Qed.

Lemma le4_of_junk : forall bs : list byte, length bs = 4%nat -> cbytes (C4 (le_bytes_to_word bs)) = bs.
Proof.
  intros bs L. cbn [cbytes]. unfold le4, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range bs) as Hr. rewrite L in Hr. change (256 ^ Z.of_nat 4) with (2 ^ 32) in Hr.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  rewrite <- L. apply le_bytes_roundtrip.
Qed.

(* [comment removed for export] *)
Fixpoint wcells (sizes : list nat) (bs : list byte) : list cell :=
  match sizes with
  | [] => []
  | s :: sizes' => (if Nat.eqb s 8 then C8 (le_bytes_to_word (firstn 8 bs)) else C4 (le_bytes_to_word (firstn 4 bs))) :: wcells sizes' (skipn s bs)
  end.

Lemma wcells_ok : forall sizes bs, Forall (fun s => s = 8%nat \/ s = 4%nat) sizes -> length bs = sum_nat sizes ->
  cells_wf (wcells sizes bs) /\ cells_bytes (wcells sizes bs) = bs /\ cells_size (wcells sizes bs) = sum_nat sizes.
Proof.
  induction sizes as [|s sizes IH]; intros bs HF L.
  - cbn. destruct bs; [repeat split; reflexivity| cbn in L; lia].
  - inversion HF as [|s' l' Hs HF']; subst. cbn [sum_nat] in L.
    destruct (IH (skipn s bs) HF' ltac:(rewrite length_skipn; lia)) as (W & B & S).
    destruct Hs as [-> | ->]; cbn [wcells Nat.eqb cells_wf cell_wf cells_bytes cells_size csize sum_nat].
    + split; [split; [exact I| exact W]|]. split; [| rewrite S; reflexivity].
      rewrite le8_of_junk by (rewrite length_firstn; lia). rewrite B. apply firstn_skipn.
    + split; [split; [exact I| exact W]|]. split; [| rewrite S; reflexivity].
      rewrite le4_of_junk by (rewrite length_firstn; lia). rewrite B. apply firstn_skipn.
Qed.

Lemma rw_cells_recast3 : forall m A cs cs',
  rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells usegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

Lemma rw_cells_junk_wcells : forall m A (n : nat) (junk : list byte) sizes,
  rw_cells usegs m A [CB n junk] -> Forall (fun s => s = 8%nat \/ s = 4%nat) sizes -> sum_nat sizes = n ->
  rw_cells usegs m A (wcells sizes junk).
Proof.
  intros m A n junk sizes RW HF SN. pose proof RW as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [L _].
  destruct (wcells_ok sizes junk HF ltac:(lia)) as (W & B & S).
  eapply rw_cells_recast3; [exact RW| exact W| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B| cbn [cells_size csize]; lia].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_junk_pem_loc : forall m A (junk : list byte),
  rw_cells usegs m A [CB 104 junk] ->
  exists l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 ta tb, rw_cells usegs m A (pem_loc l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 ta tb).
Proof.
  intros m A junk RW.
  assert (HF : Forall (fun s => s = 8%nat \/ s = 4%nat) [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 4; 4]%nat)
    by (repeat (apply Forall_cons; [first [left; reflexivity| right; reflexivity]|]); apply Forall_nil).
  pose proof (rw_cells_junk_wcells m A 104 junk [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 4; 4]%nat RW HF eq_refl) as H.
  cbn [wcells Nat.eqb] in H. unfold pem_loc. do 14 eexists. exact H.
Qed.
