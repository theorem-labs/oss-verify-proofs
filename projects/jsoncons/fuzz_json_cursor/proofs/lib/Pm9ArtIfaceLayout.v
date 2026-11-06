(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface HeapIfaceA PmHeapIfaceA Pm9ArtIfaceLaws Pm9ArtIfaceInst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition art_img_client : list (Z * Z) :=
  [(0x10000, 0x156000); (0x158c38, 0x15a640); (0x680350, 0x691d38); (0x691d40, 0x691d88); (0x691da4, 0x691db8); (0x691dc0, 0x6b3248); (0x6b3250, 0x6b4000)].
Definition art_img_w : list (Z * Z) :=
  [(0x158d28, 0x159020); (0x680350, 0x691d38); (0x691d40, 0x691d88); (0x691da4, 0x691db8); (0x691dc0, 0x6b3248); (0x6b3250, 0x6b4000)].

Lemma art_L_client : forall lo hi a, In (lo, hi) art_img_client -> lo <= a < hi -> ~ hl_rt_static art_L a.
Proof.
  intros lo hi a Hin Ha S. cbn [art_L hl_rt_static] in S. unfold art_static in S. unfold art_img_client in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma art_L_w_not_ro : forall lo hi a, In (lo, hi) art_img_w -> lo <= a < hi -> ~ hl_rt_ro art_L a.
Proof.
  intros lo hi a Hin Ha S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. unfold art_img_w in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma art_L_ro_img : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x6b4000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Lemma art_L_static_img : forall a, hl_rt_static art_L a -> 0x156000 <= a < 0x6b4000.
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.
