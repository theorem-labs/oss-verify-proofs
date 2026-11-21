(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: image regions and their lengths for libtasn1/asn1_get_length_der_fuzzer's UBSan binary, and module names. *)
(* Modified by Theorem Labs, 2026-11: ported toward LPS 727298f3 by the change of the same file of cgif/cgif_rgb_fuzzer, its addresses relocated to this unit's binaries; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YQ0j YQ0b YQ0i YQ0a YQ03.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import UH04.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition ubs2_img : smem :=
[ mkRegion None 0x10000 0x12000 0 0 [mkChunk 0x10000 (CImg 0x2000)]    ;
mkRegion None 0x12000 0x1b000 0 0 [mkChunk 0x12000 (CImg 0x9000)]    ;
mkRegion None 0x1b000 0x1c000 0x1b000 0x1c000 [mkChunk 0x1b000 (CImg 0x1000)]    ;
mkRegion None 0x1c000 0x4e000 0x1c000 0x4e000 [mkChunk 0x1c000 (CImg 0x32000)]     ].
Lemma ubs2_img_ok : img_check ubs2segs ubs2_img = true.
Proof. vm_compute. reflexivity. Qed.
Definition ubs2_pc0 : Z := 0x12468.
Definition ubs2_W : Z := 65536.
(* 08b1429: the start-up layout depends on kb_rseq (27 or 29 auxv pairs) *)
Definition ubs2_ss0 (two rs : bool) : sstate := ss0 ubs2_pc0 Ubsan_phdrs ubs2_W two rs ubs2_img.
Lemma ubs2_init_pc_eq : Z.of_N Ubsan_init_pc = ubs2_pc0.
Proof. reflexivity. Qed.
Theorem ubs2_init_st_ok :
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
st_ok ubs2segs (E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) xw xd)
(ubs2_ss0 two (kb_rseq (in_kernel inp)))
(init_machine_state ubs2segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp).
Proof.
intros inp mbase sp brk rnd xw xd two Hsp Hva Hve Hvl Hlau Hxd Hxh Hxr Hxg Hxs Hxx Hxm Hxc Htwo.
unfold ubs2_ss0. rewrite <- ubs2_init_pc_eq.
eapply init_st_ok; first [ exact Hlau | eassumption | exact ubs2_img_ok
| (pose proof YK1b.stack_window_depth_val; unfold ubs2_W; lia) ].
Qed.
