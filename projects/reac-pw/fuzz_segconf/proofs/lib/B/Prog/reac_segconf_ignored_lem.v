(* reac_segconf_ignored on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the facts of its walk that speak of a
   reader only, so they hold at any image: the 4 bytes of c->seg[i].ignore (offset 0x18) as the reader sees them,
   from SegABase.sa_rconf and seg_spec.rconf_enc (flag_enc: 0 or 1), and the bound on the index find returns.
   Adapted from image A's lib/A/Prog/reac_segconf_role_lem.v (commit 3e8a17ad1bc0), the
   same reading of the neighbouring role_set field. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
Import ListNotations.
Local Open Scope Z_scope.

(* byte k of the little-endian 4 bytes of a u32 v *)
Lemma ign_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold le4, le_byte.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth];
    rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
    rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.

Lemma ign_nth_firstn : forall (l : list byte) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  induction l as [|x l IH]; intros n k d Hk; destruct n as [|n]; [lia | destruct k; reflexivity | lia |].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma ign_nth_skipn : forall (l : list byte) n k d, nth k (skipn n l) d = nth (n + k) l d.
Proof.
  induction l as [|x l IH]; intros n k d; [destruct n, k; reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

(* the 4 bytes at entry i's offset off, through the reader that holds the struct *)
Lemma ign_seg4 : forall (rd : reader) c bs rc i off,
  sa_bytes rd c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat -> 0 <= off -> off + 4 <= 356 ->
  forall k, (k < 4)%nat ->
  rd (c + 356 * Z.of_nat i + off + Z.of_nat k) = Some (bv_unsigned (nth k (fldz off 4 (fld (356 * i) 356 bs)) ZB0)).
Proof.
  intros rd c bs rc i off HB HE Hi H0 H1 k Hk.
  destruct HE as (L & LS & _). unfold SEG_C_SIZE in L.
  assert (Hlt : (356 * i + Z.to_nat off + k < length bs)%nat) by lia.
  replace (c + 356 * Z.of_nat i + off + Z.of_nat k) with (c + Z.of_nat (356 * i + Z.to_nat off + k)) by lia.
  rewrite (HB _ Hlt). f_equal. f_equal.
  unfold fldz, fld. change (Z.to_nat 4) with 4%nat.
  rewrite ign_nth_firstn by lia. rewrite ign_nth_skipn. rewrite ign_nth_firstn by lia. rewrite ign_nth_skipn.
  f_equal. lia.
Qed.

(* c->seg[i].ignore: 0 or 1, its 4 bytes at + 0x18 *)
Lemma ign_rd_ignore : forall (rd : reader) c rc i, sa_rconf rd c rc -> (i < length (rc_seg rc))%nat ->
  sa_val rd (c + 356 * Z.of_nat i + RS_IGNORE) 4 (seg_spec.b2z (rs_ignore (r_seg rc i))).
Proof.
  intros rd c rc i (bs & HB & HE) Hi. unfold r_seg.
  pose proof (proj1 (proj2 (proj2 HE)) i Hi) as HS.
  destruct HS as (_ & _ & _ & _ & HF & _).
  intros k Hk.
  rewrite (ign_seg4 rd c bs rc i RS_IGNORE HB HE Hi ltac:(unfold RS_IGNORE; lia) ltac:(unfold RS_IGNORE; lia) k Hk).
  rewrite HF. f_equal. unfold seg_spec.b2z.
  apply ign_le4_byte; [destruct (rs_ignore (nth i (rc_seg rc) rseg_d)); lia | exact Hk].
Qed.

(* find's index is an entry of the table, which holds at most 32 *)
Lemma ign_find_bound : forall (rd : reader) c rc nm i, sa_rconf rd c rc -> r_find rc nm = Some i ->
  (i < length (rc_seg rc))%nat /\ (i < 32)%nat.
Proof.
  intros rd c rc nm i (bs & _ & (_ & LS & _)) Hf. unfold r_find in Hf.
  assert (H : forall l k j, r_find_go l nm k = Some j -> (k <= j < k + length l)%nat).
  { induction l as [|s l IH]; intros k j Hg; cbn [r_find_go] in Hg; [discriminate|].
    destruct (strcmp (rs_name s) nm =? 0); [injection Hg as <-; cbn [length]; lia|].
    apply IH in Hg. cbn [length]. lia. }
  apply H in Hf. lia.
Qed.
