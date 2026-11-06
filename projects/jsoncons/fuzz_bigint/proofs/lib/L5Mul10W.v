(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5Defs L5Words.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5MULW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma limbs_val_val ws : L5.limbs_val ws = val ws.
Proof. induction ws as [|w ws IH]. reflexivity. cbn [L5.limbs_val]. rewrite val_cons, IH, M_val. reflexivity. Qed.

Lemma words_ok_of_Forall ws : Forall (fun w => 0 <= w < 2 ^ 64) ws -> words_ok ws.
Proof. intros F. apply (proj1 (L5W.words_ok_BF ws)). exact F. Qed.

Lemma val_all_zero ws : (forall i, (i < length ws)%nat -> nth i ws 0 = 0) -> val ws = 0.
Proof.
  induction ws as [|w ws IH]; intros Hz. reflexivity.
  rewrite val_cons. pose proof (Hz 0%nat ltac:(cbn; lia)) as H0. cbn in H0. rewrite H0. rewrite IH. lia. intros i Hi. apply (Hz (S i)). cbn. lia.
Qed.

Lemma val_firstn_zeros ws k : (k <= length ws)%nat -> (forall i, (k <= i < length ws)%nat -> nth i ws 0 = 0) -> val (firstn k ws) = val ws.
Proof.
  intros Hk Hz. rewrite (val_firstn_skipn k ws). rewrite (val_all_zero (skipn k ws)). lia.
  intros i Hi. rewrite length_skipn in Hi. rewrite nth_skipn. apply Hz. lia.
Qed.

Lemma wlist_nth' v n i : (i < n)%nat -> nth i (wlist v n) 0 = wordi v i.
Proof. intros Hi. exact (wlist_nth v n i Hi). Qed.

Lemma Forall_wlist v n : Forall (fun w => 0 <= w < 2 ^ 64) (wlist v n).
Proof. apply (proj2 (L5W.words_ok_BF _)). apply wlist_words_ok. Qed.

(* [comment removed for export] *)
Lemma land253_id fb : 0 <= fb < 256 -> Z.testbit fb 1 = false -> Z.land fb 253 = fb.
Proof.
  intros Hfb Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 1) as [->|Hi1]. { rewrite Hb. reflexivity. }
  destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
  - assert (T: Z.testbit 253 i = true).
    { assert (H: In i [0; 2; 3; 4; 5; 6; 7]) by (cbn; lia). cbn in H. repeat (destruct H as [<-|H]; [reflexivity|]). destruct H. }
    rewrite T. apply Bool.andb_true_r.
  - rewrite (Z.bits_above_log2 fb i). reflexivity. lia. apply (Z.le_lt_trans _ (Z.log2 255)). apply Z.log2_le_mono. lia. cbn. lia.
Qed.

Lemma lor1_bit1 fb : Z.testbit (Z.lor fb 1) 1 = Z.testbit fb 1.
Proof. rewrite Z.lor_spec. replace (Z.testbit 1 1) with false by reflexivity. apply Bool.orb_false_r. Qed.

End L5MULW.
