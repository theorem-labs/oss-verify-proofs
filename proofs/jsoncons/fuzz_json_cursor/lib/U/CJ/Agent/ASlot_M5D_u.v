(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u F_malloc_entry_u F_malloc_enframe_u MallocTree_u MallocFacts_A_u MallocHINV_u MallocKit_A_u F_mm_syscalls_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocKit_AB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import Malloc_fp_u MallocKit_A2_u AllocSlot_iface_u F_malloc_join_u Malloc_iface_u F_malloc_bigw_u F_malloc_big_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocNat_u MallocFacts_AS_u MallocKit_A3_u ASlot_W0_u ASlot_W1_u ASlot_W9_u ASlot_W10_u ASlot_W12_u ASlot_W13_u ASlot_W14_u ASlot_W18_u ASlot_I_u ASlot_M0_u ASlot_M2_u ASlot_M3_u ASlot_M4P_u ASlot_M4_u ASlot_M5P_u.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Lemma slot_ok_N st g b r idx n N :
  slot_ok st g b r idx n -> get_stride (get_meta_rec st g) = N + 4 -> 0 <= N -> slot_ok st g b r idx N.
Proof.
  intros SO STR N0. destruct SO. constructor; try assumption; try lia.
  intros off O0 OF. apply so_q16; lia.
Qed.

Lemma outside_app' W1 W2 a : outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma arith_prog_dec a c s n : 0 < s ->
  (exists j, 0 <= j <= n /\ a = c + s * j) \/ (forall j, 0 <= j <= n -> a <> c + s * j).
Proof.
  intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
  - pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
    destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
    + left. exists ((a - c) / s). split; [lia|]. lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
  - right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.

Lemma errno_lit5 (tp : word) : tp = Z_to_bv 64 0x1a640 -> errno_addr tp = 107932.
Proof. intros ->. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma meta_slot_mono stA stB g :
  (forall a, is_Some ((s_areas stA) !! a) -> is_Some ((s_areas stB) !! a)) -> meta_slot stA g -> meta_slot stB g.
Proof.
  intros HA (ar & arr & kk & Ha & Hk & E). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
  exists ar, arr', kk. auto.
Qed.

Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).

Lemma nest_class sc (SC : 0 <= sc < 48) cnt1 : 1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  nreq sc cnt1 = size_class sc * 16 * cnt1 + 12 /\ 0 <= ncls sc cnt1 <= 26 /\ 16 * size_class sc * cnt1 + 16 <= UNIT * size_class (ncls sc cnt1)
  /\ sc < ncls sc cnt1 /\ 0 <= nreq sc cnt1 < 2^32 /\ nreq sc cnt1 + 4 <= 16 * size_class (ncls sc cnt1).
Proof.
  intros C1 SM. pose proof (size_class_range sc SC) as SZR.
  assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
  assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
  pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
  assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
  destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
  split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
  split.
  { destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
    destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
    pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
  split; [lia|]. nia.
Qed.
End CEIL_WRAP_1.

