(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN09.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup src0tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word src0segs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply src0tbl_ok. exact H.
Qed.
End a.
Local Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma FN_000 : fetch_word src0segs (Z_to_bv 64 (src0_A_free + 0x0)) = Some (0x1440006f%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_000 : decode_any (0x1440006f%bv : bv 32) = Some (Jal 0 324, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_008 : fetch_word src0segs (Z_to_bv 64 (src0_A_libc_free + 0x0)) = Some (0x1c050463%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_008 : decode_any (0x1c050463%bv : bv 32) = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_1c8 : fetch_word src0segs (Z_to_bv 64 (src0_A_libc_free + 0x1c8)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_1c8 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma src0_free_null_msteps : forall regs mem rom,
getr regs 10 = Z_to_bv 64 0 ->
msteps src0segs (mkst regs (Z_to_bv 64 src0_A_free) mem rom)
(mkst regs (v_jalr (getr regs 1) 0) mem rom).
Proof.
intros regs mem rom H10.
change (Z_to_bv 64 src0_A_free) with (Z_to_bv 64 (src0_A_free + 0x0)). norm_pc.
stepj' FN_000 DN_000.
stepbt FN_008 DN_008.
stepret FN_1c8 DN_1c8.
apply mst_refl.
Qed.
Theorem src0_free_null : free_null_realizes src0_msyms.
Proof.
intros regs mem md Hret H10 Hh Hlz.
eapply SR_msteps; [exact Hh | exact Hlz | apply (src0_free_null_msteps regs mem _ H10) |].
apply SR_ret. unfold YK0s.ret_ok in Hret. rewrite Hret. reflexivity.
Qed.
End b.
