(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied by path from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v (a working branch acae397d926) for libreac/fuzz_scene's program walk, as its first half, with GrantImg.v's own names: the image's segments, the code table of the program code, the value table over SceneAddr.v and the certificate that the listing is this image's code. The second half, the PAImg instance, is SceneImg.v, which requires this file; the split is this clone's, so that the certificate type-checks before the lib/Reusable ASan layer lands (SceneImg.v needs in_img, ALedger and wx_segs_nowrap from it; nothing here does). scene_segs is defined here from the generated image module because this clone has no twin of fuzz_grant's lib/A/AB1v.v, whose tfibsegs is the same definition. The image is fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026); scene_lib_start = 0x82878 is the address its .symtab gives LLVMFuzzerTestOneInput and scene_lib_count = 2013 the slots of SceneList.v. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable.
From OSSVerify.libreac.fuzz_scene.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneSyms SceneList SceneAddr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition scene_segs : list Segment := Asan.M.loaded_segments.
(* The code table: every word of the program code the listing covers, from the entry function up. *)
Definition scene_lib_start : Z := 0x82878.
Definition scene_lib_count : nat := 2013.
Definition scenetbl : ctable :=
Eval vm_compute in (build_table scene_segs scene_lib_start scene_lib_count TEmpty).
Lemma scenetbl_eq : scenetbl = build_table scene_segs scene_lib_start scene_lib_count TEmpty.
Proof. vm_cast_no_check (eq_refl scenetbl). Qed.
Lemma scenetbl_ok : table_ok scene_segs scenetbl.
Proof. rewrite scenetbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition scene_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then scene_text else if (a <? A_HI 0)%nat then scene_obj (a - A_OBJ 0) else scene_hi (a - A_HI 0).
Lemma scene_lib_check : pi_check ssym (clookup scenetbl) scene_val scene_sigma scene_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma scene_val_range : forall a, 0 <= scene_val a < 2 ^ 64.
Proof.
intros a. unfold scene_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold scene_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 18 (destruct m as [|m]; [zlit|]). zlit.
- unfold scene_hi. generalize (a - A_HI 0)%nat as m. intros m. do 26 (destruct m as [|m]; [zlit|]). zlit.
Qed.
