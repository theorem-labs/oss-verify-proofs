(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN; the launch's group id): changed ubs0_ss0, ubs0_init_st_ok, ubs0_init_config_ms; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP0l YP08 YP02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Ubsan.
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
Definition ubs0_ss0 (rs : bool) (two : bool) : sstate := ss0 rs ubs0_pc0 Ubsan_phdrs ubs0_W two ubs0_img.
Lemma ubs0_init_pc_eq : Z.of_N Ubsan_init_pc = ubs0_pc0.
Proof. reflexivity. Qed.
Theorem ubs0_init_st_ok :
forall (inp : ProcInput) (mbase sp brk : word) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte) (two : bool),
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
xd UID_DATOM = uid_bytes (in_uid inp) ->
xd HWCAP_DATOM = hwcap_bytes (in_hwcap inp) ->
xd RAND_DATOM = rand_bytes rnd ->
xd GID_DATOM = gid_bytes (in_gid inp) ->
xd EHDR_DATOM = ehdr_bytes inp sp mbase ->
xd MINSIG_DATOM = minsig_bytes inp sp mbase ->
xd EXECFN_DATOM = execfn_ptr_bytes (ed_top rnd) (in_execfn inp) ->
(if two then 2 <= length (in_argv inp) else True)%nat ->
st_ok ubs0segs (E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) xw xd)
(ubs0_ss0 (kb_rseq (in_kernel inp)) two)
(init_machine_state ubs0segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp).
Proof.
intros inp mbase sp brk rnd xw xd two Hsp Hva Hve Hvl Hlau Hvi Hxd Hxh Hxr Hxg Hxe Hxm Hxf Htwo.
unfold ubs0_ss0. rewrite <- ubs0_init_pc_eq.
eapply (init_st_ok ubs0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd) with (W := ubs0_W) (xw := xw) (xd := xd);
first [ eassumption | exact ubs0_img_ok | (unfold ubs0_W; lia) ].
Qed.
Lemma ubs0_init_config_ms : forall sp brk mbase rnd lim inp,
cfg_ms (init_config ubs0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)
= init_machine_state ubs0segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp.
Proof. reflexivity. Qed.
Lemma ubs0_init_config_model : forall sp brk mbase rnd lim inp,
m_halted (cfg_model (init_config ubs0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)) = None
/\ m_vm_lazy (cfg_model (init_config ubs0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)) = [].
Proof. intros. split; reflexivity. Qed.
