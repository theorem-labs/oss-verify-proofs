(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface HeapIfaceA PmHeapIfaceA Pm4ArtIfaceLaws Pm4ArtIfaceInst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition art_img_client : list (Z * Z) :=
  [(0x10000, 0x162000); (0x165360, 0x166840); (0x68c550, 0x69df78); (0x69df80, 0x69dfc8); (0x69dfe4, 0x69dff8); (0x69e000, 0x6bf488); (0x6bf490, 0x6c0000)].
Definition art_img_w : list (Z * Z) :=
  [(0x165448, 0x165740); (0x68c550, 0x69df78); (0x69df80, 0x69dfc8); (0x69dfe4, 0x69dff8); (0x69e000, 0x6bf488); (0x6bf490, 0x6c0000)].

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
Lemma art_L_ro_img : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x6c0000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Lemma art_L_static_img : forall a, hl_rt_static art_L a -> 0x162000 <= a < 0x6c0000.
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.
