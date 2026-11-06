(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module names changed; 21 of its 61 lines of code are new or changed and 299 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30): the message path's set-up, two
   phase lemmas of kernel_defs.v's cuts, composed from this lane's four steps:
     kn_msg0 : kin_msg0 (+0x594) -> kin_loop (+0x63c, k = 0) / kin_qmsg (+0x1e9c)
       = kernel_msg0_a.v kn_m5a (+0x594 .. meta_fill_00 of w2's shadow .. +0x5b4)
       ; kernel_msg0_b.v kn_m5b (+0x5b4 .. checked_memset(w2, 0, 4112) .. +0x5c4)
       ; kernel_msg0_c.v kn_m5c (+0x5c4 .. the message count m = b % 6 .. +0x63c / +0x1e9c)
     kn_mz : kin_mz (+0x1e7c) -> kin_qmsg (+0x1e9c)
       = kernel_msg0_a.v kn_mza (+0x1e7c .. meta_fill_00 .. +0x1e8c) ; kernel_msg0_b.v kn_mzb (.. checked_memset .. +0x1e9c)
   The +0x1e7c path unpoisons w2 (meta_fill_00 at +0x1e88), so kin_qmsg's F shadow (kfsh 0xf8 0 0xf3) holds there.
   The lane's own cuts (kin_m5b4, kin_m5c4, kin_z1e8c) are kernel_msg0_kit.v's.
   Section hypotheses: LAWS, TB (AF0m.PcapSyms B: the read set's shadow at the current memory, LinkWalkShadow.v),
   LV (the calls' pcs), AS00 (meta_fill_00), AMEMSET (checked_memset).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit kernel_msg0_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_a kernel_msg0_b kernel_msg0_c.
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
Hypothesis TB : AF0m.PcapSyms B.     (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis LV : LinkVals.
Hypothesis AS00 : aset_shadow_realizes pa_segs B 0x55e74 0x00.        (* meta_fill_00: SetShadow.v link_set_shadow_00 *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.         (* checked_memset: AE2r.v asan_memset_realizes *)

Theorem kn_msg0 : forall POST Rc Rm, (forall cx v, 1 <= v <= 5 -> Rm cx v) ->
  kfrom SK B POST (kin_loop B Rc Rm) -> kfrom SK B POST (kin_qmsg B Rc) -> kfrom SK B POST (kin_msg0 B Rc).
Proof.
  intros POST Rc Rm HRm HL HQ.
  apply (kn_m5a SK B LAWS TB LV AS00 POST Rc).
  apply (kn_m5b SK B LAWS LV AMEMSET POST Rc).
  exact (kn_m5c SK B LAWS TB POST Rc Rm HRm HL HQ).
Qed.

Theorem kn_mz : forall POST Rc, kfrom SK B POST (kin_qmsg B Rc) -> kfrom SK B POST (kin_mz B Rc).
Proof.
  intros POST Rc HQ.
  apply (kn_mza SK B LAWS LV AS00 POST Rc).
  exact (kn_mzb SK B LAWS LV AMEMSET POST Rc HQ).
Qed.

End b.
End a.

Print Assumptions kn_msg0.
Print Assumptions kn_mz.
