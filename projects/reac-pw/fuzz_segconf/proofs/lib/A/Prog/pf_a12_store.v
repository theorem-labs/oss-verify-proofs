(* reac-pw/fuzz_segconf, image A: segment A12 of reac_segconf_parse_file's walk (the ignore key,
   reac_segconf.c:271-280; statements in lib/A/Prog/pf_pieces.v), the step from the two `sw` of the ignore branch
   (0x888d0 `cur->ignore = b` at seg[gi] + 0x18, 0x888f0 `cur->ignore_set = 1` at seg[gi] + 0x1c, R:278-279) to
   the block's new SegModel state. No machine state, no image: only readers (lib/Reusable/YG0f.v), SegABase's
   sa_rconf / sa_bytes and the image-free lemmas of pf_a12_pure.v.
     [a12_w4]           the 4 bytes an `sw` of the 32-bit value z writes, as the reader shows them
                        (the body of SegABase.sa_val rd a 4 z).
     [a12_rconf_store]  the two stores, with every other byte of the block kept, give the block the state
                        pf_prov_mid (PIgn b) cf gi.
   Segment A12's proof, by the G3 walk owner, 2026-10-30. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase pf_a12_pure.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(** The 4 bytes an `sw` of the 32-bit value z writes, as the reader shows them. *)
Definition a12_w4 (rd : reader) (a z : Z) : Prop :=
  forall k, (k < 4)%nat -> rd (a + Z.of_nat k) = Some (YG0f.le_byte z 4 k).

(** * Bytes of le4 *)
Lemma a12s_nth_le : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k]; cbn [nth].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

(** Byte k of `le4 (Z_to_bv 64 z)` is the reader's byte k of the 32-bit value z (for every z: both sides keep
    only bits [8k, 8k + 8) of z, k < 4). *)
Lemma a12s_le4_byte : forall z k, (k < 4)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 z)) ZB0) = YG0f.le_byte z 4 k.
Proof.
  intros z k Hk. unfold le4. rewrite unsigned_lit_wrap. rewrite a12s_nth_le by exact Hk.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  unfold YG0f.le_byte. change (8 * Z.of_nat 4) with 32. change 256 with (2 ^ 8).
  rewrite (shiftr_mod_mod8 z (8 * Z.of_nat k) 64) by lia.
  rewrite (shiftr_mod_mod8 z (8 * Z.of_nat k) 32) by lia.
  reflexivity.
Qed.

Lemma a12s_nth_eq : forall (l1 l2 : list byte) i j, (i < length l1)%nat -> (j < length l2)%nat ->
  nth_error l1 i = nth_error l2 j -> nth i l1 ZB0 = nth j l2 ZB0.
Proof.
  intros l1 l2 i j H1 H2 H.
  rewrite (nth_error_nth' l1 ZB0) in H by exact H1.
  rewrite (nth_error_nth' l2 ZB0) in H by exact H2.
  injection H as E. exact E.
Qed.

(** * The two stores of the ignore branch *)
(** The two stores of the ignore branch (reac_segconf.c:278-279), with every other byte of the block kept,
    give the block the SegModel state pf_prov_mid (PIgn b). *)
Lemma a12_rconf_store : forall (rd rd' : reader) (c : Z) (cf : rconf) (gi : nat) (b : bool),
  sa_rconf rd c cf -> (gi < length (rc_seg cf))%nat -> 0 <= c ->
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE ->
     ~ (c + 356 * Z.of_nat gi + 24 <= a < c + 356 * Z.of_nat gi + 32) -> rd' a = rd a) ->
  a12_w4 rd' (c + 356 * Z.of_nat gi + 24) (b2z b) ->
  a12_w4 rd' (c + 356 * Z.of_nat gi + 28) 1 ->
  sa_rconf rd' c (pf_prov_mid (PIgn b) cf gi).
Proof.
  intros rd rd' c cf gi b (bs & Hbs & He) Hgi Hc Hkeep Hw0 Hw1.
  unfold a12_w4 in Hw0, Hw1.
  assert (He' := He). destruct He' as (HL & H32 & _).
  unfold seg_spec.SEG_C_SIZE in HL.
  assert (HB : (356 * gi + 24 + length (a12_ign_bytes b) <= length bs)%nat)
    by (rewrite a12_ign_bytes_len; lia).
  assert (HLu : length (upd_bytes bs (356 * gi + 24) (a12_ign_bytes b)) = length bs)
    by (apply upd_bytes_length; exact HB).
  unfold sa_rconf. exists (upd_bytes bs (356 * gi + 24) (a12_ign_bytes b)).
  split; [| exact (a12_rconf_ign cf bs gi b He Hgi)].
  unfold sa_bytes. intros i Hi. rewrite HLu in Hi.
  destruct (Nat.lt_ge_cases i (356 * gi + 24)) as [Hlo|Hlo];
    [| destruct (Nat.lt_ge_cases i (356 * gi + 32)) as [Hhi|Hhi]].
  - (* below seg[gi] + 0x18: the old byte, kept *)
    assert (E : nth i (upd_bytes bs (356 * gi + 24) (a12_ign_bytes b)) ZB0 = nth i bs ZB0).
    { apply a12s_nth_eq; [rewrite HLu; exact Hi | exact Hi |].
      apply a12_upd_nth_out; [exact HB | left; lia]. }
    rewrite E, (Hkeep (c + Z.of_nat i)); [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE; lia | lia].
  - (* the 8 stored bytes: ignore = b at + 0x18, ignore_set = 1 at + 0x1c *)
    assert (E : nth i (upd_bytes bs (356 * gi + 24) (a12_ign_bytes b)) ZB0 =
                nth (i - (356 * gi + 24)) (a12_ign_bytes b) ZB0).
    { apply a12s_nth_eq; [rewrite HLu; exact Hi | rewrite a12_ign_bytes_len; lia |].
      apply a12_upd_nth_in; [exact HB | lia | rewrite a12_ign_bytes_len; lia]. }
    rewrite E. unfold a12_ign_bytes.
    destruct (Nat.lt_ge_cases (i - (356 * gi + 24)) 4) as [Hj|Hj].
    + rewrite app_nth1 by (rewrite length_le4; lia).
      rewrite a12s_le4_byte by lia.
      replace (c + Z.of_nat i) with (c + 356 * Z.of_nat gi + 24 + Z.of_nat (i - (356 * gi + 24))) by lia.
      apply Hw0. lia.
    + rewrite app_nth2 by (rewrite length_le4; lia). rewrite length_le4.
      rewrite a12s_le4_byte by lia.
      replace (c + Z.of_nat i) with (c + 356 * Z.of_nat gi + 28 + Z.of_nat (i - (356 * gi + 24) - 4)) by lia.
      apply Hw1. lia.
  - (* from seg[gi] + 0x20 on: the old byte, kept *)
    assert (E : nth i (upd_bytes bs (356 * gi + 24) (a12_ign_bytes b)) ZB0 = nth i bs ZB0).
    { apply a12s_nth_eq; [rewrite HLu; exact Hi | exact Hi |].
      apply a12_upd_nth_out; [exact HB | right; rewrite a12_ign_bytes_len; lia]. }
    rewrite E, (Hkeep (c + Z.of_nat i)); [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE; lia | lia].
Qed.
