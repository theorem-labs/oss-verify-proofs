(** * Bridge.DEmit.BrDetect — pair D33 of PAIRS.md: [detect_data_type], S5 vs RT.

    Both read only the literal/length tree's frequencies of the bytes
    0..255.  S5 loops 32 + 224 times returning [option Z]; RT loops 33 +
    257 times returning [bool]; each loop is related to the other by
    induction on S5's fuel with RT's fuel at least as large. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section Detect.
Variable s : DS.deflate_state.
Variable lt : RT.Tree.
Hypothesis Hf : forall n, 0 <= n < 256 -> DS.Freq s DS.TL n = RT.t_freq lt n.

Lemma land1_eq : forall m, negb (Z.land m 1 =? 0) = (Z.land m 1 =? 1).
Proof.
  intros m. assert (E : Z.land m 1 = m mod 2) by (apply (Z.land_ones m 1); lia).
  assert (H : 0 <= Z.land m 1 <= 1) by (rewrite E; pose proof (Z.mod_pos_bound m 2); lia).
  destruct (Z.eqb_spec (Z.land m 1) 0), (Z.eqb_spec (Z.land m 1) 1); cbn; lia.
Qed.

Lemma loop1_eq : forall f g n mask, (f <= g)%nat -> 0 <= n -> 32 <= n + Z.of_nat f ->
  DT.detect_loop1 f s n mask = if RT.ddt_block (S g) lt n mask then Some Z_BINARY else None.
Proof.
  induction f as [|f IH]; intros g n mask Hfg Hn Hnf.
  - cbn [DT.detect_loop1 RT.ddt_block]. replace (31 <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct g as [|g]; [lia|]. cbn [DT.detect_loop1 RT.ddt_block].
    destruct (Z.leb_spec n 31) as [L|L].
    + replace (31 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite land1_eq. rewrite (Hf n) by lia. unfold RT.t_freq.
      destruct ((Z.land mask 1 =? 1) && negb (RT.tr_fc lt n =? 0)); [reflexivity|].
      apply IH; lia.
    + replace (31 <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma loop2_eq : forall f g n, (f <= g)%nat -> 0 <= n -> 256 <= n + Z.of_nat f ->
  DT.detect_loop2 f s n = if RT.ddt_allow (S g) lt n then Some Z_TEXT else None.
Proof.
  induction f as [|f IH]; intros g n Hfg Hn Hnf.
  - cbn [DT.detect_loop2 RT.ddt_allow]. replace (RT.LITERALS <=? n) with true by (symmetry; apply Z.leb_le; unfold RT.LITERALS; lia).
    reflexivity.
  - destruct g as [|g]; [lia|]. cbn [DT.detect_loop2 RT.ddt_allow].
    unfold DS.LITERALS, RT.LITERALS.
    destruct (Z.ltb_spec n 256) as [L|L].
    + replace (256 <=? n) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite (Hf n) by lia. unfold RT.t_freq.
      destruct (negb (RT.tr_fc lt n =? 0)); [reflexivity|]. apply IH; lia.
    + replace (256 <=? n) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma detect_eq : DT.detect_data_type s = RT.detect_data_type lt.
Proof.
  unfold DT.detect_data_type, RT.detect_data_type.
  rewrite (loop1_eq 32 32 0 4093624447) by (cbn; lia).
  destruct (RT.ddt_block 33 lt 0 4093624447); [reflexivity|].
  rewrite (Hf 9), (Hf 10), (Hf 13) by lia. unfold RT.t_freq.
  destruct (negb (RT.tr_fc lt 9 =? 0)); [reflexivity|].
  destruct (negb (RT.tr_fc lt 10 =? 0)); [reflexivity|].
  destruct (negb (RT.tr_fc lt 13 =? 0)); [reflexivity|]. cbn [orb].
  rewrite (loop2_eq 224 256 32) by (cbn; lia).
  change (Z.to_nat RT.LITERALS + 1)%nat with (S 256).
  destruct (RT.ddt_allow (S 256) lt 32); reflexivity.
Qed.

End Detect.

Theorem br_detect_data_type : forall s ts,
  trel s ts -> DT.detect_data_type s = RT.detect_data_type (RT.ts_trees ts RT.TK_L).
Proof.
  intros s ts (T1 & _). apply detect_eq. intros n Hn. unfold DS.Freq, RT.t_freq. cbn [DS.tree_fc].
  apply T1. unfold DS.HEAP_SIZE. lia.
Qed.

Print Assumptions br_detect_data_type.
