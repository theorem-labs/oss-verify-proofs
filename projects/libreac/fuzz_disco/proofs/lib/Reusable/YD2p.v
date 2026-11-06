(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD2o.v, YD2p.v and YD1q.v
   (ossv/recipes c8557374ad2) for fuzz_disco, in the form of fuzz_pcap's closing file lib/A/PcapClose.v
   (a working branch fe3d720b4c7), the asan-ubsan twin of lib/A/AD2p.v: the closing of lib/A/DiscoAsanTop.v
   ASAN_UBSAN_T (= lib/Reusable/YZ03.v TFIB_T) from named parts; module paths changed, shape DiscoAsanTop.disco_shape,
   fuzz_disco's asan-ubsan image, ONE program part (LLVMFuzzerTestOneInput's contract) in place of cgif_file_fuzzer's
   three (TNEWGIFX / TADDFX / TCLOSEX and their wfn); the closed statements of cgif's lib/YZ05.v are here too. *)
(* The closing side of fuzz_disco's two asan-ubsan statements (rule 24: no function proved; this file is assembly).
   Since S1's split (a Theorem Labs lane, 2026-10-29): every part but the program part is closed over the landed asan-ubsan
   core in lib/Reusable/DiscoAsanUbsanT.v (the twin of lib/A/DiscoAsanT.v), so the Section below has ONE hypothesis,
   H_PROG_LIBX. The text that follows describes the donor's two steps.

   The donor closes TFIB_T in two steps: YD2o.v applies YD1q.v tfib_srealizesX (the twin of AD1q.v). This file
   does the same with every input a named Section variable or hypothesis below, each with the donor statement it
   stands for and the lane that supplies it (proofs/libreac/fuzz_disco/lib/A/OBLIGATIONS.md at a working branch 37e11e67676d).

   Types it uses beyond milestone 3 (a working branch 7287935fdf1): lib/Reusable/YCfn.v (the program contract,
   floating-point state quantified across the call), lib/Reusable/YCeg.v (in_ro_tfa) and lib/Reusable/YF0m.v
   (TfibSyms), from a Theorem Labs lane's S2b (a working branch d0f0dc0a3fa). The read-only range is the
   asan-ubsan image's .data.rel.ro start to .got end, lib/Reusable/YB1w.v tfib_data_rel_ro_lo / tfib_got_hi
   (0xa0280 / 0xa15a8, checked against the image's section headers). *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.libreac.fuzz_disco.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YC5d YCbp YI16 YE00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YCfn YCeg YF0m YB1w YRo YD2l YRoClose.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import DiscoAsanTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require DiscoAsanUbsanT YZ03.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := DiscoAsanTop.disco_shape.

(* donor lib/YD2o.v valid_sp_windowX. *)
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Section asan_ubsan.
(* H_PROG_LIBX: THE PART, donor lib/YD1q.v LIBX (lib/Reusable/YCfn.v tfib_lib_contract_x_all, closed in the donor by
   lib/YCfi.v tfib_lib_x_all over three program parts), at fuzz_disco's one program part: the contract of
   LLVMFuzzerTestOneInput, with the donor's XL0 (YCfi.v:54, fun _ => 0), ameter_triv (Reusable/YCbp.v) and fuzz_disco's
   relro range (lib/Reusable/YB1w.v), given the read-only facts DiscoAsanUbsanT.H_RO_stmt (proved there from
   YRoClose.tfib_ro_hyps). Owner: the asan-ubsan twin of lib/A/Prog/DiscoLibX.v disco_lib_x_all (a Theorem Labs lane). *)
Hypothesis H_PROG_LIBX :
  forall rc : YM05.RunCeil,
  DiscoAsanUbsanT.H_RO_stmt rc ->
  @YCfn.tfib_lib_contract_x_all rc LS YD2l.TfibB ameter_triv (fun _ => 0) (fun _ => 0)
    YB1w.tfib_data_rel_ro_lo YB1w.tfib_got_hi.

(* donor lib/YD2o.v TFIB_T_of_partsXF; ASAN_UBSAN_T is lib/Reusable/YZ03.v TFIB_T. *)
Theorem ASAN_UBSAN_T_of_parts : DiscoAsanTop.ASAN_UBSAN_T.
Proof. exact (DiscoAsanUbsanT.TFIB_TB_of_lib H_PROG_LIBX). Qed.

(* The two asan-ubsan statements, given only the program part (donor lib/YZ05.v). *)
Theorem disco_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (DiscoAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Theorem disco_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (DiscoAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
End asan_ubsan.
