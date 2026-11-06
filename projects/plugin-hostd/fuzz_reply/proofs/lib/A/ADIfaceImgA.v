(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/ADIfaceImgA.v (commit d0fcb396eeeb, sha256 a5a02a1a4b7de2d0; preset image p102: unstripped fuzz_preset.asan sha256 bff8519bbe3e, pin 1be0f53d96cb) to plugin-hostd/fuzz_reply's asan image A (unstripped fuzz_reply.asan sha256 d751b179ea49, pin 42c58610e125) by a Theorem Labs lane's alreloc.py (frozen-ced0368250cb6538): module paths changed, every image numeral moved by symbol + offset (hand-check table in the commit); preset lib.Reusable -> reply lib.A for: none. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the by-value cover check of an owned static table: some area of the table covers all of
   [lo, hi), decided over the whole table (an existsb decision, covers_b), never by the area's row, so a table that
   gains rows, in any order, keeps every proof that uses it. Users: A/ADIfaceA.v (the depot zone and the internal
   allocator's flag bytes of image A's DImg instance) and A/AFf0cf.v (D_owned_cf).
   This file held the image premises of Reusable/YGcfDIface.v at the copied cgif_file numerals, among them the
   NEGATION of IAL_AREA_B (ial_area_B_false_A). YGcfDIface.v is now image-free over c-asan's ImgBaseDG.DImg, so those
   premises are restated over image A's DImg instance in A/ADIfaceA.v (dzone_owned_A, izone_owned_A), where
   IAL_AREA_B HOLDS (ial_area_B_A); the negation is deleted.
   The suffix _A names the image. No address of preset's image is typed here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0f YG0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* Some area of the table [l] covers all of [lo, hi): decided over the whole table, at any row. *)
Definition covers_b (lo hi : Z) (l : list (Z * Z)) : bool :=
existsb (fun r => (fst r <=? lo) && (hi <=? fst r + snd r)) l.
Lemma covers_b_Exists : forall lo hi l, covers_b lo hi l = true -> forall a, lo <= a < hi -> Exists (in_zr a) l.
Proof.
intros lo hi l H a Ha. unfold covers_b in H. apply existsb_exists in H as (r & Hr & E).
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
Qed.
