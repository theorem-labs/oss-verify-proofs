(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0b YQ0i YQ0a YQ03.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition ubs2_img : smem :=
[ mkRegion None 0x10000 0x12000 0 0 [mkChunk 0x10000 (CImg 0x2000)]    ;
mkRegion None 0x12000 0x21000 0 0 [mkChunk 0x12000 (CImg 0xf000)]    ;
mkRegion None 0x21000 0x22000 0x21000 0x22000 [mkChunk 0x21000 (CImg 0x1000)]    ;
mkRegion None 0x22000 0x54000 0x22000 0x54000 [mkChunk 0x22000 (CImg 0x32000)]     ].
Lemma ubs2_img_ok : img_check ubs2segs ubs2_img = true.
Proof. vm_compute. reflexivity. Qed.
Definition ubs2_pc0 : Z := 0x12aa8.
Definition ubs2_W : Z := 65536.
Definition ubs2_ss0 (two : bool) : sstate := ss0 ubs2_pc0 Ubsan_phdrs ubs2_W two ubs2_img.
Lemma ubs2_init_pc_eq : Z.of_N Ubsan_init_pc = ubs2_pc0.
Proof. reflexivity. Qed.
Theorem ubs2_init_st_ok :
forall (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte) (two : bool),
valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
xd UID_DATOM = uid_bytes uid ->
xd HWCAP_DATOM = hwcap_bytes hw ->
xd RAND_DATOM = rand_bytes rnd ->
(if two then 2 <= length argv else True)%nat ->
st_ok ubs2segs (E0 sp argv envp xw xd) (ubs2_ss0 two)
(init_machine_state ubs2segs Ubsan_init_pc Ubsan_phdrs sp rnd argv envp uid hw).
Proof.
intros sp argv envp uid hw rnd xw xd two Hsp Hva Hve Hfits Hxd Hxh Hxr Htwo.
unfold ubs2_ss0. rewrite <- ubs2_init_pc_eq.
apply (init_st_ok ubs2segs Ubsan_phdrs sp argv envp Hsp Hva Hve Hfits uid hw rnd ubs2_W ltac:(unfold ubs2_W; lia)
xw xd Hxd Hxh Hxr Ubsan_init_pc two ubs2_img Htwo ubs2_img_ok).
Qed.


