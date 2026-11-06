(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 17 of its 40 lines of code are new or changed and 495 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA: the refusal of a key line, 0x863ac jal m_refuse(c,
   line + 1) when cur = NULL or the stripped line has no '=' (SegModel.m_key's last arm), then 0x863b0 `j 0x86bdc`,
   0x86bdc `ld a7,144(s1)`, 0x86be0 `j 0x86cf8` (TAIL). KA_REF_stmt is the state at the jal (a0 = s5 = c, a1 = s6 =
   line + 1, s8 = FAKE, the model as the refusal and the next lines). The KEYA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_keya_m m_file_s_keya_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Section e.
Variable B : asyms.

(* 0x863ac, jal m_refuse: a0 = c, a1 = line + 1; the line is done as the refusal (cur kept), the next line's address
   in 144(s1) *)
Definition KA_REF_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (m_refuse mcc (line + 1) false, cur) (line + 1) (lines (mf_rest rest))) = mf_final v ->
mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 (mv_c v) -> getr regs1 11 = w64 (line + 1) ->
getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc KA_JREF.
End e.
End f.
End d.
