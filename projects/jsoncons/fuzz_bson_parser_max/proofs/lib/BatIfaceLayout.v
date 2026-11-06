(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx L5DefsA BatIfaceLaws BatIfaceInst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition art_img_client : list (Z * Z) :=
  [(0x10000, 0x136000); (0x1396f8, 0x13a0e0); (0x65fe10, 0x671828); (0x671830, 0x671878); (0x671894, 0x6718a8); (0x6718b0, 0x692d38); (0x692d40, 0x694000)].
Definition art_img_w : list (Z * Z) :=
  [(0x1397e0, 0x139ae0); (0x65fe10, 0x671828); (0x671830, 0x671878); (0x671894, 0x6718a8); (0x6718b0, 0x692d38); (0x692d40, 0x694000)].

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
Lemma art_L_ro_img : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x694000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Lemma art_L_static_img : forall a, hl_rt_static art_L a -> 0x136000 <= a < 0x694000.
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
