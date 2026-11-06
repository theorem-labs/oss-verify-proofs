(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs: reply image row img-constapart-B (its IMG_QAPART half) of the cf layer at plugin-hostd/fuzz_reply.
   rule 24: no function proved (kind: closed image fact over the symbol table of reply's image B, fuzz_reply.asan-ubsan,
   pin 10ffb5f9202a).

   IMG_QAPART, proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:65-68 @ 8b12df2b772 (four clauses), with qhdr_inst
   (YGcfInstDrainX.v:62-63 @ 8b12df2b772) unfolded:
   qhdr_inst B a := (as_inst B + o_quar + 152 <= a < as_inst B + o_quar + 156) \/
                    (as_inst B + o_quar + 160 <= a < as_inst B + o_quar + 192).
   The layer states IMG_QAPART over the image class (Context {IM : AImg}).  Reply does not carry YGcfInstDrainX.v, so the
   Lemma states IMG_QAPART's body, qhdr_inst unfolded, at reply's instance IM := AImg_reply (B/AGif2reply.v:24,
   im_syms := YF0m.TfibSyms).  (The error buffer object's apartness is the separate row ERRB_QAPART,
   B/ReplyImg_errbqapart.v.)
   At image B (B/YF0m.v:16-19) the header words are [0xa3348, 0xa334c) and [0xa3350, 0xa3370): below the internal
   allocator (0xa7840), the flag (0x1360c8), the store (0x178508) and the depot (0x188518).  cgif's discharge: YFey.v:579
   / :585 / :638 by its numerals. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
Open Scope Z_scope.

(* IMG_QAPART at image B: YGcfInstDrainX.v:65-68 @ 8b12df2b772, qhdr_inst unfolded, at IM := AImg_reply. *)
Lemma IMG_QAPART_B : forall B, @im_syms AImg_reply B -> forall a,
  ((as_inst B + o_quar + 152 <= a < as_inst B + o_quar + 156) \/ (as_inst B + o_quar + 160 <= a < as_inst B + o_quar + 192)) ->
  ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\
  ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS.
rewrite (ts_inst B TS) in Ha.
rewrite (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
replace (2 ^ 20) with 1048576 by reflexivity.
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, o_quar in *. lia.
Qed.
