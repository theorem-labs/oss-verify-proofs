(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malcore_stmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_refillstmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sys_stmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sys_fixed.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sys_grant.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sys_madvise.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sys_munmap.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_refill.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_contracts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malsec.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_ldefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_istmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_fin.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeFin.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_dsec.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem rta_refill_closed : refill_stmt.
Proof. exact (refill_ok fixed_commit_ok). Qed.

Theorem rta_core_sec_closed : core_stmt_sec.
Proof. exact (mal_core_sec grant_node_ok fixed_commit_pab_ok). Qed.

Theorem rta_free_closed : free_contract RTA.
Proof. exact (rta_free (drain_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem rta_contracts_closed : rt_contracts RTA.
Proof. exact (rta_contracts rta_refill_closed rta_core_sec_closed rta_free_closed). Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed
  RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin
  RT_freeFin RT_dsec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem rta_refill_closed : refill_stmt.
Proof. exact (refill_ok fixed_commit_ok). Qed.

Theorem rta_core_sec_closed : core_stmt_sec.
Proof. exact (mal_core_sec grant_node_ok fixed_commit_pab_ok). Qed.

Theorem rta_free_closed : free_contract RTA.
Proof. exact (rta_free (drain_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem rta_contracts_closed : rt_contracts RTA.
Proof. exact (rta_contracts rta_refill_closed rta_core_sec_closed rta_free_closed). Qed.
