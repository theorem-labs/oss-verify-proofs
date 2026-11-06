(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import HeapIface HeapIfaceA HeapIfaceAEx L5DefsAB0 EbrIfaceLaws EbrIfaceInst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

Definition art_img_client : list (Z * Z) :=
  [(0x10000, 0x13f000); (0x141fe8, 0x142a10); (0x668750, 0x67a128); (0x67a130, 0x67a178); (0x67a194, 0x67a1a8); (0x67a1b0, 0x69b638); (0x69b640, 0x69c000)].
Definition art_img_w : list (Z * Z) :=
  [(0x1420d0, 0x1423c8); (0x668750, 0x67a128); (0x67a130, 0x67a178); (0x67a194, 0x67a1a8); (0x67a1b0, 0x69b638); (0x69b640, 0x69c000)].

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
Lemma art_L_ro_img : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x69c000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Lemma art_L_static_img : forall a, hl_rt_static art_L a -> 0x13f000 <= a < 0x69c000.
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.

Lemma art_as0_layout : L5A.as0_layout art_L art_C.
Proof.
  constructor; try reflexivity.
  - cbn [art_C art_statics_cells asc_cells]. apply incl_appl. apply incl_refl.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - exact art_L_ro_img.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - cbn. lia.
Qed.

