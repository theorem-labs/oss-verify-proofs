(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA L5DefsAB0 BrtIfaceLaws BrtIfaceInst.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.asan Require Import L5UnwindSpecsAB0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition art_img_client : list (Z * Z) :=
  [(0x10000, 0xd8000); (0xdab38, 0xdb070); (0x600d90, 0x6118b0); (0x6118b8, 0x611900); (0x61191c, 0x611930); (0x611938, 0x632cb0); (0x632cb8, 0x634000)].
Definition art_img_w : list (Z * Z) :=
  [(0xdabb0, 0xdaea8); (0x600d90, 0x6118b0); (0x6118b8, 0x611900); (0x61191c, 0x611930); (0x611938, 0x632cb0); (0x632cb8, 0x634000)].

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
Lemma art_L_ro_img : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x634000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Lemma art_L_static_img : forall a, hl_rt_static art_L a -> 0xd8000 <= a < 0x634000.
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
Lemma art_unw_layout : L5USA.as0_unw_layout art_L.
Proof.
  split; [|split; [|reflexivity]].
  - intros r a Hin Ha. unfold L5USA.UNW_STATICS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO in Hin. cbn [In] in Hin.
    cbn [art_L hl_rt_static hl_rt_ro]. unfold art_static, art_ro. repeat (destruct Hin as [Hin|Hin]; [subst r; cbn [fst snd] in Ha; lia|]). destruct Hin.
  - intros r a Hin Ha. unfold L5USA.UNW_CONSTS in Hin. cbn [In] in Hin. cbn [art_L hl_rt_static]. unfold art_static.
    repeat (destruct Hin as [Hin|Hin]; [subst r; cbn [fst snd] in Ha; lia|]). destruct Hin.
Qed.
