(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstRefillSpeccgif.v (commit f01d79f3fb5, cf refill round 3; file sha256 03717aa9575f) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane for a Theorem Labs lane, lane refill-b2): the cf layer's REFILL CONTRACT at cgif's image.
   refill_spec_core_cf_cgif: MnRefillSeamcf.refill_spec_core_cf_of_cases applied to the three entry cases at cgif:
   - B3 (inited, few free chunks): CfW's MnRefillB3Topcf.refill_B3_entry_cf_of_parts;
   - B2 (inited, enough free chunks): MnRefillB2Rcf.refill_B2_entry_cgif;
   - uninit: MnRefillUninitcf.refill_uninit_entry_cgif, its B3 case from CfW's
     MnRefillB3cf.refill_B3_inner_cf_of_classfull.
   refill_spec_cf_cgif: YGcfInstRefill.refill_spec_cf_of_core (the model clauses from the model).
   ag_refill_ret_ok_cgif: Allocate's return address into the refill is a valid return target (by computation).
   refill_walk_cf_cgif: YGcfInstRefill.refill_walk_cf_of_spec, the Allocate-site walk.
   OPEN, a named Section hypothesis: HCF : MnRefillSeamcf.refill_B3_classfull_cf (a Theorem Labs lane's class-full report
   walk).  The unit rows: TS (TfibSyms B) and IOK_ok; field round 2 carries the cells' image rows in ARmcf.
   Field round 3: the contracts take the overlay normal form, arodata_ok_cf and the hull admission at the call state
   (YGcfInstRefill.refill_spec_core_cf); the seam passes them to the three entries.  The file is at cgif's image
   constants CfImg_cgif (YGcfImgcgif.v), the uninit entry's (its post-init arodata_ok_cf reads cgif's RELRO row), as
   the WalkSig closing that consumes refill_walk_cf_cgif is.
   EVENT-FREE.  rule 24: no function proved (kind: assembly of proved refill arms). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFhy AFis AFhz YFkpcf YFkrcf YFhmcf YFkscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0qcf YG0scf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstRefill MnRefillSeamcf YGcfRefillCells.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFhn YFhncf YFkocf YFkxcf YFkycf YFkzcf MnRefillB2Rcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YFk5cf YFk8cf YFkkcf YFklcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT MemnormLoc MnRefillLocreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MnRefillUninitcf MnRefillB3cf MnRefillB3Topcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfImgA.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
#[local] Existing Instance CfImgA.CfImg_A.

Section b.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : TfibSyms B.
Hypothesis IOK_ok : forall i, IOK i -> i = A_ALLOCATOR.
Hypothesis HCF : refill_B3_classfull_cf.

Theorem refill_spec_core_cf_reply : @refill_spec_core_cf fx rc CfImgA.CfImg_A cp AImg_reply AGImg_reply B IOK.
Proof.
apply (@refill_spec_core_cf_of_cases fx rc CfImgA.CfImg_A cp AImg_reply AGImg_reply B IOK).
- exact (MnRefillB3Topcf.refill_B3_entry_cf_of_parts B IOK TS IOK_ok HCF).
- exact (MnRefillB2Rcf.refill_B2_entry_reply B IOK TS IOK_ok).
- exact (MnRefillUninitcf.refill_uninit_entry_reply B IOK TS IOK_ok
    (MnRefillB3cf.refill_B3_inner_cf_of_classfull HCF)).
Qed.

Theorem refill_spec_cf_reply : @refill_spec_cf fx rc CfImgA.CfImg_A cp AImg_reply AGImg_reply B IOK.
Proof. exact (@refill_spec_cf_of_core fx rc CfImgA.CfImg_A cp AImg_reply AGImg_reply B IOK refill_spec_core_cf_reply). Qed.
End b.

(* Allocate's refill return address is a valid return target at cgif (by computation on the image constant). *)
Lemma ag_refill_ret_ok_reply : ag_refill_ret_ok (IM := AImg_reply) (AG := AGImg_reply).
Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

Section c.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : TfibSyms B.
Hypothesis IOK_ok : forall i, IOK i -> i = A_ALLOCATOR.
Hypothesis HCF : refill_B3_classfull_cf.

(* The Allocate-site refill walk at cgif (CfInstMiss's non-vacuity row, CfF1's iface_miss_cf_cgif premise). *)
Theorem refill_walk_cf_reply : @refill_walk_cf fx rc CfImgA.CfImg_A cp AImg_reply AGImg_reply B IOK.
Proof.
exact (@refill_walk_cf_of_spec fx rc CfImgA.CfImg_A cp AImg_reply AGImg_reply B IOK ag_refill_ret_ok_reply
  (refill_spec_cf_reply B IOK TS IOK_ok HCF)).
Qed.
End c.
End a.

Print Assumptions refill_spec_cf_reply.
Print Assumptions refill_walk_cf_reply.
About refill_spec_cf_reply.
About refill_walk_cf_reply.
