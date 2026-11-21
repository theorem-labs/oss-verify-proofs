(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Definition am_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ CTX <= a < CTX + 928
  \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Lemma am_fp_alloc_fp st lo sp a : am_fp st lo sp a -> alloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold am_fp, alloc_fp. tauto. Qed.
Lemma am_fp_stack st lo sp a : lo <= a < sp -> am_fp st lo sp a.
Proof. intros; left; assumption. Qed.
Lemma am_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> am_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
Lemma am_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> am_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
Lemma am_fp_not_errno st lo sp a : am_fp st lo sp a -> regions_wf st -> ATOP <= lo ->
  ~ (errno_addr (Z_to_bv 64 0x1a6fc) <= a < errno_addr (Z_to_bv 64 0x1a6fc) + 4).
Proof.
  intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; unfold CTX in *; rewrite ?unsigned_lit by lia; try lia.
  destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [_ D2].
  pose proof (lr_lo_ge r). atop_facts. lia.
Qed.
Lemma am_fp_same st st' lo sp a : s_regions st' = s_regions st -> am_fp st' lo sp a <-> am_fp st lo sp a.
Proof. intros ER. unfold am_fp. rewrite ER. tauto. Qed.

Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate :=
  upd_meta q clr_links (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).

End CANSEC1.
