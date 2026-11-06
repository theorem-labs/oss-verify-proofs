(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v, with its module paths and module names changed; 21 of its 54 lines of code are new or changed and 610 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30): the message path's queueing,
   kin_qmsg (+0x1e9c) -> kin_latch (+0x2100) (lib/A/Prog/kernel_defs.v; link-a/plan/kernel-lanes.md
   (internal record, sha256 18c8d69749d5)). Listing (internal path)
   (internal record, sha256 7bc02d6772b3), +0x1e9c .. +0x1f2c. The code: n = 0 queues an empty 4-byte message (put32(0),
   w2.n := 4); chunk j of g_nl (j = n_chunks <= ci <= 2) := w2's n bytes (checked_memcpy +0x1ee4); n_chunks := j + 1;
   chunk_len[j] := n (instrumented check +0x1f10); w2's shadow back to 0xf8 (meta_fill_f8 +0x1f24); s6 := ci (slot
   KS_CI); j +0x2100. kn_qmsg composes the five steps (kernel_qmsg_b.v kq_qa, kq_qc; kernel_qmsg_a.v kq_qb, kq_qd,
   kq_qe) over the lane's own cuts kin_qcpy (+0x1ee4), kin_qcnt (+0x1ee8), kin_qfil (+0x1f24), kin_qret (+0x1f28).
   Section hypotheses used: LAWS, LV, TB, KI, AMEMCPY, ASSF8 (the Section of link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_qmsg_a kernel_qmsg_b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)
Hypothesis ASSF8 : aset_shadow_realizes pa_segs B 0x55f94 0xf8. (* meta_fill_f8: SetShadow.v link_set_shadow_f8 *)

Theorem kn_qmsg : forall POST Rc, kfrom SK B POST (kin_latch B Rc) -> kfrom SK B POST (kin_qmsg B Rc).
Proof.
  intros POST Rc H.
  eapply kq_qa; try eassumption.
  eapply kq_qb; try eassumption.
  eapply kq_qc; try eassumption.
  eapply kq_qd; try eassumption.
  eapply kq_qe; eassumption.
Qed.

End b.
End a.

Print Assumptions kn_qmsg.
