(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_malloc_enframe MallocTree MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma actives_length : forall st, length (actives st) = 48%nat.
Proof. intros. unfold actives. rewrite length_map, length_seq. reflexivity. Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 -> nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
  intros st sc Hsc. unfold actives. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grp_hdr_cov (st : mstate) (rid : N) (off : Z) : Prop :=
  exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b <= off < snd b + 12.

(* [comment removed for export] *)
Definition unk_agree (st : mstate) (o m1 : mem) : Prop :=
  forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
    0 <= off < round_up_pg (r_len r) ->
    cell_read (get_shadow st rid) off = Unknown h ->
    ~ grp_hdr_cov st rid off ->
    m1 (wa (r_base r + off)) = o (wa (r_base r + off)).

Lemma unk_agree_refl : forall st m, unk_agree st m m.
Proof. intros st m rid r off h _ _ _ _ _. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition expo_cond (st : mstate) (n : Z) : Prop := MMAP_THRESHOLD <= n \/ s_regions st = ∅.

Record slot_ok (st1 : mstate) (g b : aptr) (r : region) (idx n : Z) : Prop := mkSO {
  so_mem : m_mem (get_meta_rec st1 g) = Some b;
  so_reg : (s_regions st1) !! (fst b) = Some r;
  so_kind : r_kind r = RKGroup;
  so_b0 : 0 <= snd b;
  so_b16 : snd b mod 16 = 0;
  so_idx : 0 <= idx <= m_last_idx (get_meta_rec st1 g);
  so_li : m_last_idx (get_meta_rec st1 g) < 32;
  so_span : snd b + 16 + get_stride (get_meta_rec st1 g) * (m_last_idx (get_meta_rec st1 g) + 1) <= round_up_pg (r_len r);
  so_s16 : 16 <= get_stride (get_meta_rec st1 g);
  so_smod : get_stride (get_meta_rec st1 g) mod 16 = 0;
  so_s31 : get_stride (get_meta_rec st1 g) - 4 - n < 2^31;
  so_n : 0 <= n;
  so_fit : n + 4 <= get_stride (get_meta_rec st1 g);
  (* [comment removed for export] *)
  so_nogrp : forall b' gh, (s_groups st1) !! b' = Some gh -> fst b' = fst b ->
     snd b' + 9 <= snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4
     \/ snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 <= snd b';
  (* [comment removed for export] *)
  so_hdr0 : cell_read (get_shadow st1 (fst b)) (snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4) = Known 0;
  (* [comment removed for export] *)
  so_q16 : forall off, 0 <= off -> 16 * off + n + 4 <= get_stride (get_meta_rec st1 g) ->
     (get_stride (get_meta_rec st1 g) * idx + 16 * off) / 16 < 65536;
  (* [comment removed for export] *)
  so_slot : (s_slots st1) !! (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx) = Some (g, idx);
  so_mslot : meta_slot st1 g;
  so_avail : 0 <= m_avail (get_meta_rec st1 g) < 2^32;
  so_freed : 0 <= m_freed (get_meta_rec st1 g) < 2^32;
  so_freeable : 0 <= m_freeable (get_meta_rec st1 g) < 2;
  so_maplen : 0 <= m_maplen (get_meta_rec st1 g) < 2^40;
  so_sc : 0 <= m_sizeclass (get_meta_rec st1 g) < 48
          \/ (m_sizeclass (get_meta_rec st1 g) = 63 /\ m_last_idx (get_meta_rec st1 g) = 0 /\ 0 < m_maplen (get_meta_rec st1 g))
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition free_slot_addr (st : mstate) (a : Z) : Prop :=
  exists g b r i, m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= i /\
    (Z.testbit (m_avail (get_meta_rec st g)) i = true \/ Z.testbit (m_freed (get_meta_rec st g)) i = true) /\
    r_base r <= a < r_base r + round_up_pg (r_len r) /\
    r_base r + sstart_of (get_meta_rec st g) i - IB <= a
      < r_base r + sstart_of (get_meta_rec st g) i + get_stride (get_meta_rec st g) - IB.

(* [comment removed for export] *)
Definition grp_hdr_addr (st : mstate) (a : Z) : Prop :=
  exists b gh r, (s_groups st) !! b = Some gh /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\
    r_base r <= a < r_base r + round_up_pg (r_len r) /\
    r_base r + snd b <= a < r_base r + snd b + 16.

(* [comment removed for export] *)
Definition new_reg_addr (st st' : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st') !! rid = Some r /\ (s_regions st) !! rid = None /\
    lr_lo r <= a < r_base r + round_up_pg (r_len r).

Record mrel (st st' : mstate) : Prop := mkMREL {
  mrel_regions : forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r';
  mrel_next : (s_next_rid st <= s_next_rid st')%N;
  mrel_reserved : s_reserved st' = s_reserved st
}.

Lemma mrel_trans st1 st2 st3 : mrel st1 st2 -> mrel st2 st3 -> mrel st1 st3.
Proof.
  intros [R1 N1 S1] [R2 N2 S2]. split; [| lia | congruence].
  intros rid r H. destruct (R1 rid r H) as (r' & H' & K' & B' & L'). destruct (R2 rid r' H') as (r'' & H'' & K'' & B'' & L'').
  exists r''. repeat split; auto; try congruence. lia.
Qed.

Lemma round_up_pg_eq x : round_up_pg x = x + (- x) mod 4096.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_mono x y : x <= y -> round_up_pg x <= round_up_pg y.
Proof. intros H. rewrite !round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

End CeilWrap.
