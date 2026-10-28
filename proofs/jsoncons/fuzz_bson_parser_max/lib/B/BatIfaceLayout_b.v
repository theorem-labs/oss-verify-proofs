(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b BatIfaceLaws_b BatIfaceInst_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition art_img_client : list (Z * Z) :=
  [(0x10000, 0x139000); (0x13bbe0, 0x13c580); (0x662290, 0x673ca8); (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x6951b8); (0x6951c0, 0x696000)].
Definition art_img_w : list (Z * Z) :=
  [(0x13bcc8, 0x13bfc0); (0x662290, 0x673ca8); (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x6951b8); (0x6951c0, 0x696000)].

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
Lemma art_L_ro_img : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x696000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Lemma art_L_static_img : forall a, hl_rt_static art_L a -> 0x139000 <= a < 0x696000.
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.

(* [comment removed for export] *)
Lemma art_as0_layout : L5A.as0_layout art_L art_C.
Proof.
  constructor; try reflexivity.
  - cbn [art_C art_statics_cells asc_cells]. apply incl_appl. apply incl_refl.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - exact art_L_ro_img.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
