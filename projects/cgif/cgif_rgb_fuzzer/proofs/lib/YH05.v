(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up state takes the CONFIG_RSEQ flag, 27 or 29 auxv pairs, and src2_init_st_ok is stated over the run's ProcInput and mmap base with the launch premises and the gid, sysinfo, execfn, minsigstksz and cache data words; trailing blank lines removed; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0b YQ0i YQ0a YQ03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition src2_img : smem :=
[ mkRegion None 0x10000 0x12000 0 0 [mkChunk 0x10000 (CImg 0x2000)]    ;
mkRegion None 0x12000 0x20000 0 0 [mkChunk 0x12000 (CImg 0xe000)]    ;
mkRegion None 0x20000 0x21000 0x20000 0x21000 [mkChunk 0x20000 (CImg 0x1000)]    ;
mkRegion None 0x21000 0x53000 0x21000 0x53000 [mkChunk 0x21000 (CImg 0x32000)]     ].
Lemma src2_img_ok : img_check src2segs src2_img = true.
Proof. vm_compute. reflexivity. Qed.
Definition src2_pc0 : Z := 0x12988.
Definition src2_W : Z := 65536.
(* 08b1429: the start-up layout depends on kb_rseq (27 or 29 auxv pairs) *)
Definition src2_ss0 (two rs : bool) : sstate := ss0 src2_pc0 Plain_phdrs src2_W two rs src2_img.
Lemma src2_init_pc_eq : Z.of_N Plain_init_pc = src2_pc0.
Proof. reflexivity. Qed.
Theorem src2_init_st_ok :
forall (inp : ProcInput) (mbase sp brk : word) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte) (two : bool),
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
xd UID_DATOM = uid_bytes (in_uid inp) ->
xd HWCAP_DATOM = hwcap_bytes (in_hwcap inp) ->
xd RAND_DATOM = rand_bytes rnd ->
xd GID_DATOM = word_le8 (in_gid inp) ->
xd SYSI_DATOM = word_le8 (la_sysinfo_ehdr (launch_auxv inp sp mbase)) ->
xd XFN_DATOM = word_le8 (at_execfn_ptr (ed_top rnd) (in_execfn inp)) ->
xd MSS_DATOM = word_le8 (la_minsigstksz (launch_auxv inp sp mbase)) ->
(forall i, (i < 8)%nat ->
xd (CW_DATOM i) = word_le8 (nth i (cache_list (la_cache (launch_auxv inp sp mbase))) (Z_to_bv 64 0))) ->
(if two then 2 <= length (in_argv inp) else True)%nat ->
st_ok src2segs (E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) xw xd)
(src2_ss0 two (kb_rseq (in_kernel inp)))
(init_machine_state src2segs Plain_init_pc Plain_phdrs sp mbase rnd inp).
Proof.
intros inp mbase sp brk rnd xw xd two Hsp Hva Hve Hvl Hlau Hxd Hxh Hxr Hxg Hxs Hxx Hxm Hxc Htwo.
unfold src2_ss0. rewrite <- src2_init_pc_eq.
eapply init_st_ok; first [ exact Hlau | eassumption | exact src2_img_ok
| (pose proof YK1b.stack_window_depth_val; unfold src2_W; lia) ].
Qed.
