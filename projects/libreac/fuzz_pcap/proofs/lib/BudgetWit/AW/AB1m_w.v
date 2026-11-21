(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for libreac/fuzz_pcap's asan image by mkfiles.py (sha256 8e6d8a8535c7; internal record) (the image module, the fuel constants and the certificate statement); module paths changed, ...Proofs.cgif.cgif_file_fuzzer.lib.A -> ...Proofs.libreac.fuzz_pcap.lib.A and ...Proofs.cgif.cgif_file_fuzzer.lib -> ...Proofs.libreac.fuzz_pcap.lib.Reusable *)
(* Modified by Theorem Labs, 2026-10-29: `startup_shape` is NOT the donor's; it is this unit's own, taken from the asan certificate run AB1m.v (sha256 4d6fc40da809; internal record) (pass 2 on a build machine, log cert.log (sha256 bc8eb9989917; internal record): Cert.vo rc 0, `check ... = COk` with exactly this shape, 592.1 s of vm_compute, over the AB01 of the same run -- all 50 hand-off states walked, none filled).  The ten holes the case split uses are 0, 1, 8, 9, 16, 17, 24, 25, 32, 36. *)
(* Modified by Theorem Labs, 2026-11: made from A/AB1m.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed startup_shape, startup_cert). *)
(* gated: a Theorem Labs lane PASS A+B.  Before (2026-10-29) brought AB1p and AB1l into this tree, this file compiled ONLY in a union that also included a working branch: it Requires AB1p and AB1l, both of them files of that branch. *)
(* Modified by Theorem Labs, 2026-10-29: this file ENDS after `startup_cert`.  The donor's proof half (AB1m.v:37-62: `#[local] Instance tfibcert_fx`, `Section a` and `Theorem tfib_startup_closed`) is cut out, per the split ruling: it belongs to a Theorem Labs lane's lib/A/AB1mClosed.v, on a working branch, and keeping it here would prove one theorem in two files.  The Require / Import list above is left exactly as the generator wrote it -- an import that only the cut half needed is harmless, and AB1mClosed may need the same modules. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK00 YK04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YA01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0e_w YA0d_w YA0f_w YA02_w YA00_w YA0h_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AB1h_w AB1k_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YB1j_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AB1p_w AB1l_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AB05_w AB01r_w.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
Definition IT0 : itab := mk_itab_ranges TSEGS startup_plan_tfib_ranges.
Lemma IT0_ok : itab_sound TSEGS IT0.
Proof. apply mk_itab_ranges_sound. Qed.
Definition hole_le_tfib (h1 h2 : nat) : bool := true.
Definition startup_shape : shape :=
(SCase (EVar 6) 10 (SAlt2 (SAlt2 (SHole 8) (SHole 9)) (SAlt2 (SHole 0) (SHole 1))) (SCase (EVar 6) 1802 (SAlt2 (SAlt2 (SHole 24) (SHole 25)) (SAlt2 (SHole 16) (SHole 17))) (SAlt2 (SHole 36) (SHole 32)))).
(* THE CERTIFICATE OVER A FREE CONFIG_RSEQ FLAG.  The flag is [kb_rseq] of the run's own
   kernel record, which [Run.valid_input] leaves free, so the plan term
   [init_acs_of_g (rseq_z rs) TFIB] is open; [destruct] on the free boolean gives two closed
   checks, one per flag.  The hand-off states, the band join state and the plan's variable
   renumbering are [AB01r_w]'s, computed from the run in the build (the recorded [AB01_w.HS_tfib]
   and [AB03_w.JS_tfib_band] were written against the released launch).  As
   cgif/cgif_file_fuzzer's A/AB1m.v in this working copy. *)
Lemma startup_cert : forall rs : bool,
check TSEGS IT0 TFIB NX0G YA02_w.LIMIT (rseq_z rs) (XNG TSEGS tfib_XN1) XE0 XB0 (HS_tfib_r (rseq_z rs)) hole_le_tfib KC0 BFUEL FUEL None
(init_acs_of_g (rseq_z rs) TFIB) (startup_plan_tfib_r (rseq_z rs))
= COk startup_shape.
Proof. intros rs. destruct rs; vm_cast_no_check (@eq_refl cres (COk startup_shape)). Qed.
