(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v, with its module paths changed; relocated to fuzz_preset asan-ubsan (pin f8f98a95bc52), map sha256 69a6a2e91fb7, checker port_addr_check.py 39e67a7eb166. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02 YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfibsegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition musl_sel_ranges : list (Z * nat) :=
[ (B_OPEN_PC, 71%nat); (B_DPRINTF_PC, 25%nat); (B_LOCKFILE_PC, 87%nat); (0x952e8, 125%nat); (0x954dc, 258%nat); (B_VFPRINTF_PC, 1146%nat); (B_VPRINTF_PC, 47%nat);
(B_SCCP_PC, 10%nat); (B_CLOSE_PC, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x42e04, 24%nat); (0x42e64, 1%nat); (0x42e68, 11%nat);  (B_INTERCEPTOR_STRNLEN_PC, 165%nat); (B__PC, 549%nat); (B_INTERCEPTOR_MEMCMP_PC, 94%nat); (B_INTERCEPTOR_MEMCHR_PC, 180%nat);
(B_INTERCEPTOR_READ_PC, 156%nat); (B_INTERCEPTOR_FWRITE_PC, 157%nat); (B_INTERCEPTOR_VPRINTF_PC, 729%nat); (B_INTERCEPTOR_VFPRINTF_PC, 45%nat); (B_INTERCEPTOR_FPRINTF_PC, 54%nat);
(B_FORMAT_GET_VALUE_SIZE_PC, 102%nat); (B_WRAP_MEMSET_PC, 1009%nat); (B_MEMTOSHADOW_ASAN_POISONING_PC, 79%nat); (B_ASAN_REGION_IS_POISONED_PC, 209%nat); (B_ASANINITED_PC, 6%nat);
(B_TRYASANINITFROMRTL_PC, 40%nat);  (B_INTERNAL_STRCHR_PC, 13%nat);  (B_INTERNAL_STRLEN_PC, 7%nat);   (B_INTERNAL_STRNLEN_PC, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges, B_ASANINITED_PC, B_ASAN_REGION_IS_POISONED_PC, B_FORMAT_GET_VALUE_SIZE_PC, B_INTERCEPTOR_FPRINTF_PC, B_INTERCEPTOR_FWRITE_PC, B_INTERCEPTOR_MEMCHR_PC, B_INTERCEPTOR_MEMCMP_PC, B_INTERCEPTOR_READ_PC, B_INTERCEPTOR_STRNLEN_PC, B_INTERCEPTOR_VFPRINTF_PC, B_INTERCEPTOR_VPRINTF_PC, B_INTERNAL_STRCHR_PC, B_INTERNAL_STRLEN_PC, B_INTERNAL_STRNLEN_PC, B_MEMTOSHADOW_ASAN_POISONING_PC, B_TRYASANINITFROMRTL_PC, B_WRAP_MEMSET_PC, B__PC, B_CLOSE_PC, B_DPRINTF_PC, B_LOCKFILE_PC, B_OPEN_PC, B_SCCP_PC, B_VFPRINTF_PC, B_VPRINTF_PC. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt B_INTERCEPTOR_MEMCPY_PC = Some 0x81010113 /\ clookup tbl_icpt B_MEMCPY_PC = None /\ clookup tbl_icpt B_MEM_IS_ZERO_PC = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
