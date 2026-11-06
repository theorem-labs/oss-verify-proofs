(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for libreac/fuzz_pcap's asan-ubsan image by mkfiles.py (sha256 8e6d8a8535c7; internal record) (the image module, the fuel constants and the certificate statement); module paths changed, ...Proofs.cgif.cgif_file_fuzzer.lib -> ...Proofs.libreac.fuzz_pcap.lib.Reusable *)
(* Modified by Theorem Labs, 2026-10-29: `startup_shape` is NOT the donor's; it is this unit's own, taken from the asan-ubsan certificate run YB1m.v (sha256 db2c4af1a99e; internal record) (pass 2 on a build machine, log cert.log (sha256 bc8ff290a020; internal record): rc 0, `check ... = COk` with exactly this shape, 587.7 s of vm_compute, over the YB01 of the same run -- all 50 hand-off states walked, none filled, every hand-off at main 0x802e8).  The ten holes the case split uses are 0, 1, 8, 9, 16, 17, 24, 25, 32, 36; they are the asan side's, measured again on this image. *)
(* Modified by Theorem Labs, 2026-10-29: this file ENDS after `startup_cert`.  The donor's proof half (`#[local] Instance tfibcert_fx`, `Section a` and `Theorem tfib_startup_closed`) is cut out, as on the asan twin lib/A/AB1m.v, per the split ruling: that half belongs to a Theorem Labs lane's closed-theorem file.  The Require / Import list above is left exactly as the generator wrote it -- an import that only the cut half needed is harmless. *)
(* The unit rename (TfibSyms -> PcapSyms etc., commit d4691bce0fe) does not apply: MEASURED, no identifier of the UNIT_RENAME list of assemble.py (sha256 32e4cec27d2a; internal record) occurs in this file. *)
(* gated: a Theorem Labs lane PASS A+B at c061542723f / 731386609e0.  When this file was written (731386609e0), YB1p and YB1l were NOT on its branch: they were on a working branch 529392df4fe56b8a76e1459851ddb7a2e003e824, so this file then compiled only in a union that included that branch; both are in this unit now (lib/Reusable/YB1p.v, lib/Reusable/YB1l.v). *)
(* lib/Reusable/YF0m.v Requires YF0l and lib/Reusable/YD2i.v Requires YB13. When this file was written both were core files absent from its branch, so the asan-ubsan files built only in a union with that same working branch 529392df4fe56b8a76e1459851ddb7a2e003e824; both are in this unit now (lib/Reusable/YF0l.v, lib/Reusable/YB13.v). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YB12 YB1h YB1k YB1j YB1p YB1l YB05 YB01.
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
Lemma startup_cert :
check TSEGS IT0 TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib hole_le_tfib KC0 BFUEL FUEL None
(init_acs_of_g TFIB) startup_plan_tfib
= COk startup_shape.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shape)). Qed.
