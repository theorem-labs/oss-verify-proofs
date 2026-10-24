(** Symbolic initial memory for the fixed checksum_fuzzer plain image.
    Adapted from the pinned cgif YH00/YH01 setup, with zlib's own ELF bounds.
    Copyright 2026 Anthropic PBC; SPDX-License-Identifier: Apache-2.0 OR MIT.
    Original generic lemmas retain their notices in Reusable/. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YP0m YP09 YP0l YP08 YP02.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Definition zsegs : list Segment := Plain.M.loaded_segments.
Definition ztext_start : Z := 0x13c04.
Definition ztext_count : nat := 9892.
Definition ztbl : ctable := Eval vm_compute in
  (build_table zsegs ztext_start ztext_count TEmpty).
Lemma ztbl_eq : ztbl = build_table zsegs ztext_start ztext_count TEmpty.
Proof. vm_compute. reflexivity. Qed.
Lemma ztbl_ok : table_ok zsegs ztbl.
Proof. rewrite ztbl_eq. apply build_table_ok0. unfold ztext_start. lia. Qed.

Definition zimg : smem :=
  [mkRegion None 0x10000 0x13000 0 0 [mkChunk 0x10000 (CImg 0x3000)];
   mkRegion None 0x13000 0x1e000 0 0 [mkChunk 0x13000 (CImg 0xb000)];
   mkRegion None 0x1e000 0x1f000 0x1e000 0x1f000 [mkChunk 0x1e000 (CImg 0x1000)];
   mkRegion None 0x1f000 0x51000 0x1f000 0x51000 [mkChunk 0x1f000 (CImg 0x32000)]].
Lemma zimg_ok : img_check zsegs zimg = true.
Proof. vm_compute. reflexivity. Qed.
Definition zpc0 : Z := 0x13c04.
Definition zW : Z := 65536.
Definition zss0 (two : bool) : sstate := ss0 zpc0 Plain.M.phdrs zW two zimg.
Lemma z_init_pc_eq : Z.of_N Plain.M.init_pc = zpc0.
Proof. reflexivity. Qed.

Theorem z_init_st_ok : forall
  (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw)
  (xw : nat -> word) (xd : nat -> list byte) (two : bool),
  valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  xd UID_DATOM = uid_bytes uid -> xd HWCAP_DATOM = hwcap_bytes hw ->
  xd RAND_DATOM = rand_bytes rnd ->
  (if two then 2 <= length argv else True)%nat ->
  st_ok zsegs (E0 sp argv envp xw xd) (zss0 two)
    (init_machine_state zsegs Plain.M.init_pc Plain.M.phdrs sp rnd argv envp uid hw).
Proof.
  intros sp argv envp uid hw rnd xw xd two Hsp Hva Hve Hfits Hxd Hxh Hxr Htwo.
  unfold zss0. rewrite <- z_init_pc_eq.
  apply (init_st_ok zsegs Plain.M.phdrs sp argv envp Hsp Hva Hve Hfits uid hw rnd
    zW ltac:(unfold zW; lia) xw xd Hxd Hxh Hxr Plain.M.init_pc two zimg Htwo zimg_ok).
Qed.

Set Printing Fully Qualified.
Print Assumptions z_init_st_ok.
