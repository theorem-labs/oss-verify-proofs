(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP0l YP08 YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition ubs0_img : smem :=
[ mkRegion None 0x10000 0x12000 0 0 [mkChunk 0x10000 (CImg 0x2000)]    ;
mkRegion None 0x12000 0x1f000 0 0 [mkChunk 0x12000 (CImg 0xd000)]    ;
mkRegion None 0x1f000 0x20000 0x1f000 0x20000 [mkChunk 0x1f000 (CImg 0x1000)]    ;
mkRegion None 0x20000 0x52000 0x20000 0x52000 [mkChunk 0x20000 (CImg 0x32000)]     ].
Lemma ubs0_img_ok : img_check ubs0segs ubs0_img = true.
Proof. vm_compute. reflexivity. Qed.
Definition ubs0_pc0 : Z := 0x12864.
Definition ubs0_W : Z := 65536.
Definition ubs0_ss0 (two : bool) : sstate := ss0 ubs0_pc0 Ubsan_phdrs ubs0_W two ubs0_img.
Lemma ubs0_init_pc_eq : Z.of_N Ubsan_init_pc = ubs0_pc0.
Proof. reflexivity. Qed.
Theorem ubs0_init_st_ok :
forall (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte) (two : bool),
valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
xd UID_DATOM = uid_bytes uid ->
xd HWCAP_DATOM = hwcap_bytes hw ->
xd RAND_DATOM = rand_bytes rnd ->
(if two then 2 <= length argv else True)%nat ->
st_ok ubs0segs (E0 sp argv envp xw xd) (ubs0_ss0 two)
(init_machine_state ubs0segs Ubsan_init_pc Ubsan_phdrs sp rnd argv envp uid hw).
Proof.
intros sp argv envp uid hw rnd xw xd two Hsp Hva Hve Hfits Hxd Hxh Hxr Htwo.
unfold ubs0_ss0. rewrite <- ubs0_init_pc_eq.
apply (init_st_ok ubs0segs Ubsan_phdrs sp argv envp Hsp Hva Hve Hfits uid hw rnd ubs0_W ltac:(unfold ubs0_W; lia)
xw xd Hxd Hxh Hxr Ubsan_init_pc two ubs0_img Htwo ubs0_img_ok).
Qed.
Lemma ubs0_init_config_ms : forall sp brk mbase rnd lim inp,
cfg_ms (init_config ubs0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)
= init_machine_state ubs0segs Ubsan_init_pc Ubsan_phdrs sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp).
Proof. reflexivity. Qed.
Lemma ubs0_init_config_model : forall sp brk mbase rnd lim inp,
m_halted (cfg_model (init_config ubs0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)) = None
/\ m_vm_lazy (cfg_model (init_config ubs0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)) = [].
Proof. intros. split; reflexivity. Qed.
