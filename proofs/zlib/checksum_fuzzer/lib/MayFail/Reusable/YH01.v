(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YH01.v, with its module paths changed; 9 of its 19 lines of code are new or changed and 37 lines of the source are left out. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZImage.
Definition src0_img := zimg.
Definition src0_img_ok := zimg_ok.
Definition src0_pc0 := zpc0.
Definition src0_W := zW.
Definition src0_ss0 := zss0.
Definition src0_init_pc_eq := z_init_pc_eq.
Definition src0_init_st_ok := z_init_st_ok.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
Lemma src0_init_config_ms : forall sp brk mbase rnd lim inp,
cfg_ms (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)
= init_machine_state src0segs Plain_init_pc Plain_phdrs sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp).
Proof. reflexivity. Qed.
Lemma src0_init_config_model : forall sp brk mbase rnd lim inp,
m_halted (cfg_model (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)) = None
/\ m_vm_lazy (cfg_model (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)) = [].
Proof. intros. split; reflexivity. Qed.
