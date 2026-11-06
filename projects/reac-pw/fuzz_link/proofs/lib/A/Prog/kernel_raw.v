(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v, with its module paths and module names changed; 28 of its 65 lines of code are new or changed and 606 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30): the raw path,
   kin_raw (+0x1f30) -> kin_latch (+0x2100) (lib/A/Prog/kernel_defs.v; link-a/plan/kernel-lanes.md
   (internal record, sha256 18c8d69749d5)). Listing (internal path)
   (internal record, sha256 7bc02d6772b3), +0x1f30 .. +0x2100. The code: w1's shadow to 0 (meta_fill_00 +0x1f38), w1 := 0
   (checked_memset +0x1f48); the next chunk of the input (2 header bytes, take := min(nl + 1, left - 2), kernel_raw_c.v);
   a chunk of t >= 1 bytes is copied into w1 (checked_memcpy +0x2074), w1.n := t, chunk j of g_nl := w1's t bytes
   (checked_memcpy +0x20b8), n_chunks := j + 1, chunk_len[j] := t; w1's shadow back to 0xf8 (meta_fill_f8 +0x20f8);
   s6 := ci (+0x20fc). kn_raw composes the steps over the lane's cuts (kernel_raw_kit.v kr_c1 .. kr_c8):
     kin_raw -kr_a-> kr_c1 -kr_b-> kr_c2 -kr_c-> kr_c3 -kr_d-> kr_c4 -kr_e-> kr_c5 -kr_f-> kr_c6 -kr_g-> kr_c7
     (kr_c also kr_c2 -> kr_c7, no chunk) -kr_h-> kr_c8 -kr_i-> kin_latch.
   Section hypotheses: LAWS, LV, TB, KI, AMEMCPY, AMEMSET, AS00, ASSF8 (the Section of link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit kernel_next kernel_qmsg_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_qmsg_a kernel_qmsg_b kernel_raw_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_raw_a kernel_raw_b kernel_raw_c kernel_raw_d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.   (* checked_memset: AE2r.v asan_memset_realizes *)
Hypothesis AS00 : aset_shadow_realizes pa_segs B 0x55e74 0x00.  (* meta_fill_00: SetShadow.v link_set_shadow_00 *)
Hypothesis ASSF8 : aset_shadow_realizes pa_segs B 0x55f94 0xf8. (* meta_fill_f8: SetShadow.v link_set_shadow_f8 *)

Theorem kn_raw : forall POST Rc, kfrom SK B POST (kin_latch B Rc) -> kfrom SK B POST (kin_raw B Rc).
Proof.
  intros POST Rc HL.
  assert (H8 : kfrom SK B POST (kr_c8 B Rc)) by (eapply kr_i; eassumption).
  assert (H7 : kfrom SK B POST (kr_c7 B Rc)) by (eapply kr_h; eassumption).
  assert (H6 : kfrom SK B POST (kr_c6 B Rc)) by (eapply kr_g; eassumption).
  assert (H5 : kfrom SK B POST (kr_c5 B Rc)) by (eapply kr_f; eassumption).
  assert (H4 : kfrom SK B POST (kr_c4 B Rc)) by (eapply kr_e; eassumption).
  assert (H3 : kfrom SK B POST (kr_c3 B Rc)) by (eapply kr_d; eassumption).
  assert (H2 : kfrom SK B POST (kr_c2 B Rc)) by (eapply kr_c; eassumption).
  assert (H1 : kfrom SK B POST (kr_c1 B Rc)) by (eapply kr_b; eassumption).
  eapply kr_a; eassumption.
Qed.

End b.
End a.

Print Assumptions kn_raw.
