(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section is over the run's ProcInput, VA size, mmap base, entry and break, with valid_launch and entry_launch_ok_va, in place of argv/envp/uid/hwcap; bsb_nw and wrap_mem are over the launch's entry_stack_image). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK14 YK1a.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section b.
Variable segs : list Segment.
Variable v : VaSize.
Variable inp : ProcInput.
Variable mbase : word.
Variable ph : PhdrInfo.
Variable entry : word.
Variable sp brk : word.
Variable rnd : EntryDraw.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase rnd) inp.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.
Definition argcN : word := len_word (in_argv inp).
Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
Proof.
pose proof (valid_argv_len (in_argv inp) Hva).
unfold argcN, len_word. apply u_Z2bv; lia.
Qed.
Lemma bsb_nw :
(bv_unsigned sp
 + Z.of_nat (length (entry_stack_image inp mbase ph entry sp rnd)) < 2^64)%Z.
Proof.
pose proof (bsb_bound v inp mbase ph entry sp brk rnd Hvl Hlau). pose proof sp_hi_num. lia.
Qed.
Definition envp_ptr : word :=
Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length (in_argv inp)) + 8).

Definition wmem : word -> option byte := wrap_mem inp mbase ph entry sp rnd.
End b.
