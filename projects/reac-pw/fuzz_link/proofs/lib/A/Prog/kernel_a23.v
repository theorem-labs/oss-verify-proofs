(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v; 18 of its 51 lines of code are new or changed and 610 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases a % 6 in {2, 3} (the nest), kin_acase at +0xaa0
   (KP_A23, ka_23) -> kin_alat (+0xb44): the phases of this segment composed over its cut a23_at
   (kernel_a23_defs.v) at J2 = +0xbf4, J5 = +0xd68, J6 = +0xdb8, J7 = +0xdcc:
     kernel_a23_head.v a23_head (+0xaa0 -> J2: the nest's header) and a23_mid (J2 -> J5 / J6: `bne a1, 3`, the nested
     attribute), kernel_a23_pad.v a23_pad (J5 -> J6: NL_ALIGN, checked_memset), kernel_a23_call.v a23_call (J6 -> J7:
     attr_text, kernel_atcall.v kn_atcall), kernel_a23_end.v a23_end_ph (J7 -> +0xb44: the nest's length).
   Section hypotheses: LAWS, LV, KI, TB, AMEMSET (checked_memset: AE2r.v asan_memset_realizes), ATEXT (attr_text).
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs attr_text_c kernel_a23_defs kernel_a23_head kernel_a23_pad kernel_a23_call
kernel_a23_end.
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
Hypothesis KI : KernImg pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.                                    (* AF0m.v; AD2l.PcapB_syms at the frame's B *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.       (* checked_memset: AE2r.v asan_memset_realizes *)
Hypothesis ATEXT : attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

Theorem kn_a23 : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (kin_alat B Rc Rm Ra) -> kfrom SK B POST (kin_acase B Rc Rm Ra KP_A23 ka_23).
Proof.
  intros POST Rc Rm Ra HN.
  pose proof (a23_call SK B LAWS LV KI TB ATEXT POST Rc Rm Ra (a23_end_ph SK B LAWS POST Rc Rm Ra HN)) as H6.
  apply (a23_head SK B LAWS POST Rc Rm Ra).
  apply (a23_mid SK B LAWS POST Rc Rm Ra); [|exact H6].
  exact (a23_pad SK B LAWS LV AMEMSET POST Rc Rm Ra H6).
Qed.

End b.
End a.

Print Assumptions kn_a23.
