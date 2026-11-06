(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP0l YP08 YP02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition src0_img : smem :=
[ mkRegion None 0x10000 0x12000 0 0 [mkChunk 0x10000 (CImg 0x2000)]    ;
mkRegion None 0x12000 0x1e000 0 0 [mkChunk 0x12000 (CImg 0xc000)]    ;
mkRegion None 0x1e000 0x1f000 0x1e000 0x1f000 [mkChunk 0x1e000 (CImg 0x1000)]    ;
mkRegion None 0x1f000 0x51000 0x1f000 0x51000 [mkChunk 0x1f000 (CImg 0x32000)]     ].
Lemma src0_img_ok : img_check src0segs src0_img = true.
Proof. vm_compute. reflexivity. Qed.
Definition src0_pc0 : Z := 0x127e4.
Definition src0_W : Z := 65536.
Definition src0_ss0 (two : bool) : sstate := ss0 src0_pc0 Plain_phdrs src0_W two src0_img.
Lemma src0_init_pc_eq : Z.of_N Plain_init_pc = src0_pc0.
Proof. reflexivity. Qed.
Theorem src0_init_st_ok :
forall (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte) (two : bool),
valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
xd UID_DATOM = uid_bytes uid ->
xd HWCAP_DATOM = hwcap_bytes hw ->
xd RAND_DATOM = rand_bytes rnd ->
(if two then 2 <= length argv else True)%nat ->
st_ok src0segs (E0 sp argv envp xw xd) (src0_ss0 two)
(init_machine_state src0segs Plain_init_pc Plain_phdrs sp rnd argv envp uid hw).
Proof.
intros sp argv envp uid hw rnd xw xd two Hsp Hva Hve Hfits Hxd Hxh Hxr Htwo.
unfold src0_ss0. rewrite <- src0_init_pc_eq.
apply (init_st_ok src0segs Plain_phdrs sp argv envp Hsp Hva Hve Hfits uid hw rnd src0_W ltac:(unfold src0_W; lia)
xw xd Hxd Hxh Hxr Plain_init_pc two src0_img Htwo src0_img_ok).
Qed.
Lemma src0_init_config_ms : forall sp brk mbase rnd lim inp,
cfg_ms (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)
= init_machine_state src0segs Plain_init_pc Plain_phdrs sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp).
Proof. reflexivity. Qed.
Lemma src0_init_config_model : forall sp brk mbase rnd lim inp,
m_halted (cfg_model (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)) = None
/\ m_vm_lazy (cfg_model (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)) = [].
Proof. intros. split; reflexivity. Qed.
