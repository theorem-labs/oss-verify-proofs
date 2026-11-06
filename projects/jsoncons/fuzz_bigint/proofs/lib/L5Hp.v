(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core BigLinkGlue.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5HP.

Section WithSegs.
Variable segs : list (Z * list byte).

(* [comment removed for export] *)
Lemma hpres_trans L LB LB1 sp scr W M M1 M2 sp1 scr1 W1 :
  L5C.hpres L LB sp scr W M M1 ->
  L5C.hpres L LB1 sp1 scr1 W1 M1 M2 ->
  (forall a, L5C.kept L LB sp scr W a -> L5C.kept L LB1 sp1 scr1 W1 a) ->
  (forall b, In b LB -> In b LB1) ->
  hl_ceil L <= sp - scr -> sp <= 2 ^ 47 -> 0 <= scr -> hl_errno L + 4 <= 0x7fff7f800000 -> 0x7fff80000000 <= hl_sptop L ->
  L5C.hpres L LB sp scr W M M2.
Proof.
  intros H1 H2 MONO SUB Hlo Hhi Hscr He Hsp.
  pose proof H1 as (P1 & D1 & C1). pose proof H2 as (P2 & D2 & C2).
  apply L5C.hpres_intro.
  - intros a KA. rewrite (P2 a (MONO a KA)). apply P1. exact KA.
  - intros i Hi. destruct (Z_lt_le_dec (sp - scr + i) (sp1 - scr1)) as [X|X];
      [| destruct (Z_lt_le_dec (sp - scr + i) sp1) as [X'|X']].
    + apply C2. lia. right; left. lia. unfold in_errno; lia. apply D1. lia.
    + replace (sp - scr + i) with (sp1 - scr1 + (sp - scr + i - (sp1 - scr1))) by lia. apply D2. lia.
    + apply C2. lia. right; left. lia. unfold in_errno; lia. apply D1. lia.
  - intros a Ha CA NE Hd.
    destruct (Z_lt_le_dec a (sp1 - scr1)) as [X|X]; [| destruct (Z_lt_le_dec a sp1) as [X'|X']].
    + apply C2. exact Ha. 2: exact NE. 2: apply C1; assumption.
      destruct CA as [IB|[[S1 S2]|IM]]. left. destruct IB as (b & Hb & Hr). exists b. split. apply SUB. exact Hb. exact Hr.
      right; left. split. exact S1. lia. right; right. exact IM.
    + replace a with (sp1 - scr1 + (a - (sp1 - scr1))) by lia. apply D2. lia.
    + apply C2. exact Ha. 2: exact NE. 2: apply C1; assumption.
      destruct CA as [IB|[[S1 S2]|IM]]. left. destruct IB as (b & Hb & Hr). exists b. split. apply SUB. exact Hb. exact Hr.
      right; left. split. exact S1. lia. right; right. exact IM.
Qed.

(* [comment removed for export] *)
Lemma kept_mono L LB LB1 sp scr W sp1 scr1 W1 a :
  L5C.kept L LB sp scr W a ->
  (forall b, In b LB -> In b LB1) ->
  sp - scr <= sp1 - scr1 -> sp1 <= sp ->
  (L5.outside W a -> L5.outside W1 a) ->
  L5C.kept L LB1 sp1 scr1 W1 a.
Proof.
  intros (Ha & CA & NE & OW) SUB H1 H2 HW. split. exact Ha. split.
  - destruct CA as [IB|[[S1 S2]|IM]]. left. destruct IB as (b & Hb & Hr). exists b. split. apply SUB. exact Hb. exact Hr.
    right; left; split; [exact S1|lia]. right; right; exact IM.
  - split. exact NE. apply HW. exact OW.
Qed.

(* [comment removed for export] *)
Lemma hpres_piece L LB sp scr W M M' (chg : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ chg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, L5C.kept L LB sp scr W a -> ~ chg a) ->
  L5.defined M' (sp - scr) scr -> mem_grows M M' ->
  L5C.hpres L LB sp scr W M M'.
Proof.
  intros FR NK DEF GR. apply L5C.hpres_intro.
  - intros a KA. apply FR. exact (proj1 KA). apply NK. exact KA.
  - exact DEF.
  - intros a Ha _ _ Hd. apply GR. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma kept_not_in_scratch L LB sp scr W a :
  L5C.kept L LB sp scr W a -> (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  hl_ceil L <= sp - scr -> hl_img_hi L <= hl_ceil L -> ~ (sp - scr <= a < sp).
Proof.
  intros (Ha & CA & NE & OW) LBhi Hlo Himg.
  destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]]. pose proof (LBhi b Hb). lia. exact S2. lia.
Qed.
Lemma kept_outside_W L LB sp scr W a : L5C.kept L LB sp scr W a -> L5.outside W a.
Proof. intros (_ & _ & _ & OW). exact OW. Qed.
Lemma outside_in W a lo n : L5.outside W a -> In (lo, n) W -> ~ (lo <= a < lo + n).
Proof. intros OW Hin. specialize (OW (lo, n) Hin). unfold L5.in_rng in OW. cbn in OW. exact OW. Qed.

(* [comment removed for export] *)
Lemma agree_on_of_unchanged (M M' : word -> option byte) (chg : Z -> Prop) a n :
  (forall x, 0 <= x < 2 ^ 64 -> ~ chg x -> M' (Z_to_bv 64 x) = M (Z_to_bv 64 x)) ->
  (forall x, a <= x < a + n -> ~ chg x) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M' a n.
Proof. intros FR NC Ha Hn i Hi. apply FR. lia. apply NC. exact Hi. Qed.

End WithSegs.
End L5HP.
