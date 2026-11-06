(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_syscalls A_MallocRep A_F_malloc_free A_F_malloc_fast A_MallocTree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocKit_B A_MallocModel_B A_F_ntf_A A_F_ntf_B A_F_ntf_C.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocKit_B3 A_F_ntf_D A_F_ntf_E.

Set Keyed Unification.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition seq_st (ns sc : Z) (st : mstate) : mstate := record_seq sc (upd_ctx (set_seq ns) st).

Lemma free_fp_ctx_only : forall st st' lo sp a,
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  free_fp st' lo sp a -> free_fp st lo sp a.
Proof. intros st st' lo sp a ER ES EG H. eapply (free_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

Lemma fm_facts_ctx : forall st f g,
  c_free_meta_head (f (s_ctx st)) = c_free_meta_head (s_ctx st) -> fm_facts st g -> fm_facts (upd_ctx f st) g.
Proof. intros st f g E H hd Hh. unfold ctx in *. cbn [upd_ctx s_ctx] in Hh. rewrite E in Hh. exact (H hd Hh). Qed.

Lemma seq_range_test sc : 0 <= sc <= 63 ->
  (31 < Z.land (sc + -7) 18446744073709551615 <-> sc_in_seq_range sc = false).
Proof.
  intros Hsc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold sc_in_seq_range.
  destruct (Z.lt_ge_cases sc 7) as [L|GE].
  - replace ((sc + -7) mod 2 ^ 64) with (sc + -7 + 2^64).
    2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
    destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try discriminate; lia.
Qed.

Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.

End CEIL.
