(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt AImg AWpacket.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma addr_ok_of_zeros : forall M a n, 0 <= a -> 0 <= n ->
  zeros M (sha a) (sha (a + n - 1) - sha a + 1) -> addr_ok M a n.
Proof.
  intros M a n Ha Hn Hz x Hx. exists (Z_to_bv 8 0).
  pose proof (sha_mono a x ltac:(lia)) as H1. pose proof (sha_mono x (a + n - 1) ltac:(lia)) as H2.
  split; [|left; reflexivity].
  replace (sha x) with (sha a + (sha x - sha a)) by lia. apply Hz. lia.
Qed.

(* [comment removed for export] *)
Lemma addr_ok_of_chunk : forall M a n (s : byte), 0 <= a -> 0 <= n -> a mod 8 = 0 ->
  zeros M (sha a) (n / 8) ->
  (n mod 8 <> 0 -> M (W (sha a + n / 8)) = Some s /\ bv_unsigned s = n mod 8) ->
  addr_ok M a n.
Proof.
  intros M a n s Ha Hn Hal Hz Hp x Hx.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Hal in Da.
  pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Bn.
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (x - a) 8 ltac:(lia)) as Bx.
  assert (Esh : sha x = sha a + (x - a) / 8).
  { unfold sha. replace x with ((x - a) + a / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (Em : x mod 8 = (x - a) mod 8).
  { replace x with ((x - a) + a / 8 * 8) at 1 by lia. rewrite Z.mod_add by lia. reflexivity. }
  assert (Hq : 0 <= (x - a) / 8 <= n / 8).
  { split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
  destruct (Z_lt_le_dec ((x - a) / 8) (n / 8)) as [Hlt|Hge].
  - exists (Z_to_bv 8 0). split; [rewrite Esh; apply Hz; lia | left; reflexivity].
  - assert (Eq : (x - a) / 8 = n / 8) by lia.
    assert (Hnz : n mod 8 <> 0) by lia.
    destruct (Hp Hnz) as [Hs Hv]. exists s. split; [rewrite Esh, Eq; exact Hs|].
    right. rewrite Hv, Em. lia.
Qed.

(* [comment removed for export] *)
Lemma sh0_of_zeros : forall M a n, 0 <= a -> a mod 8 = 0 -> 0 <= n -> n mod 8 = 0 ->
  zeros M (sha a) (n / 8) -> sh0 M a n.
Proof.
  intros M a n Ha Hal Hn Hn8 Hz x Hx.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Hal in Da.
  pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Hn8 in Dn.
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (x - a) 8 ltac:(lia)) as Bx.
  assert (Esh : sha x = sha a + (x - a) / 8).
  { unfold sha. replace x with ((x - a) + a / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  rewrite Esh. apply Hz. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
Lemma addr_ok_partial : forall M a s (sb : byte), 0 <= a -> a mod 8 = 0 -> 1 <= s <= 7 ->
  M (W (sha a)) = Some sb -> bv_unsigned sb = s -> addr_ok M a s.
Proof.
  intros M a s sb Ha Hal Hs Hm Hv x Hx.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Hal in Da.
  assert (Esh : sha x = sha a).
  { unfold sha. f_equal. replace x with ((x - a) + a / 8 * 8) by lia. rewrite Z.div_add by lia.
    rewrite (Z.div_small (x - a)) by lia. lia. }
  assert (Em : x mod 8 = x - a).
  { replace x with ((x - a) + a / 8 * 8) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  exists sb. split; [rewrite Esh; exact Hm | right; rewrite Hv, Em; lia].
Qed.
