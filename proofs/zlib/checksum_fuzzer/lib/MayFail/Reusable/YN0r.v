(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0r.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Notation B1 := src0_msyms.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition kept_regs : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Record ntmid (Xz : list sptr) (fuel : nat) (L : layout) (A0 s : astate) (g : sptr)
(regs0 regs1 : bvmap 5 word) (mem0 mem1 : word -> option byte) (md : Model) (gv : Z) : Prop := {
nm_syms : syms_ok B1;
nm_layout : layout_ok L s;
nm_ctx : ly_ctx L = CTX;
nm_sec : 0 <= ly_sec L < 2 ^ 64;
nm_rep : memrepX B1 Xz L s mem1;
nm_statics : statics_ok B1 mem1;
nm_ledger : ledger_ok B1 L s md;
nm_md : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [];
nm_a0 : getr regs1 (nat_to_reg 10) = Z_to_bv 64 (ptr_addr L g);
nm_s1 : getr regs1 (nat_to_reg 9) = Z_to_bv 64 GUARD;
nm_s2 : getr regs1 (nat_to_reg 18) = Z_to_bv 64 CTX;
nm_sp : getr regs1 (nat_to_reg 2) = Z_to_bv 64 (spZ regs0 - 96);
nm_keep : forall r, In r kept_regs -> getr regs1 (nat_to_reg r) = getr regs0 (nat_to_reg r);
nm_frame :
bytes_are mem1 (spZ regs0 - 48) 8 gv /\
bytes_are mem1 (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 (nat_to_reg 19))) /\
bytes_are mem1 (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 (nat_to_reg 18))) /\
bytes_are mem1 (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 (nat_to_reg 9))) /\
bytes_are mem1 (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 (nat_to_reg 8))) /\
bytes_are mem1 (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 (nat_to_reg 1)));
nm_guard : word_mem src0segs mem1 GUARD gv;
nm_ret : YK0s.ret_ok (getr regs0 (nat_to_reg 1));
nm_tp : getr regs0 (nat_to_reg 4) = Z_to_bv 64 (ms_tp B1);
nm_spf : spZ regs0 mod 16 = 0 /\ alloc_ceiling + NT_FRAME * Z.of_nat (S fuel) <= spZ regs0 /\ spZ regs0 < 2 ^ 63;
nm_stkw : forall a, spZ regs0 - NT_FRAME * Z.of_nat (S fuel) <= a < spZ regs0 -> writable_at src0segs mem1 a;
nm_unch : forall a, 0 <= a < 2 ^ 64 -> ~ alloc_owned L A0 a -> ~ (spZ regs0 - NT_FRAME * Z.of_nat (S fuel) <= a < spZ regs0) ->
mem1 (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)
}.
End b.
