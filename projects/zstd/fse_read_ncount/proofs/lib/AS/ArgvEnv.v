(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec CatExec SeqExec StepTac.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Section Scaffold.
Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rnd : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.
#[using="Hsp_hi"] Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.
Definition argcN : word := len_word av.
#[using="Hva"] Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
pose proof (valid_argv_len av Hva).
unfold argcN, len_word. apply u_Z2bv; lia.
Qed.
#[using="Hva Hve Hsp_hi"] Lemma bsb_nw :
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
Proof.
pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
Qed.
End Scaffold.
