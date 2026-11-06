(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MallocFacts_A.
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocRep MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Record block_ok (st : mstate) (b : block) : Prop := mkBO {
  (* [comment removed for export] *)
  bo_slot : exists g idx, (s_slots st) !! (blk_slot b) = Some (g, idx)
            /\ Z.testbit (m_avail (get_meta_rec st g)) idx = false
            /\ Z.testbit (m_freed (get_meta_rec st g)) idx = false
            /\ 0 <= idx <= m_last_idx (get_meta_rec st g)
            (* [comment removed for export] *)
            /\ (exists off, 0 <= off /\ blk_addr b = conc st (blk_slot b) + UNIT * off
                           /\ UNIT * off + blk_size b <= get_stride (get_meta_rec st g) - IB);
  (* [comment removed for export] *)
  bo_region : exists r, (s_regions st) !! (fst (blk_slot b)) = Some r /\ r_kind r = RKGroup;
  bo_size : 0 <= blk_size b
}.

(* [comment removed for export] *)

Definition sstart_of (mr : meta) (i : Z) : Z := snd (default (0%N, 0) (m_mem mr)) + UNIT + get_stride mr * i.

Definition fact_ctx (cs : mstate) : Prop :=
  0 <= c_mmap_counter (ctx cs) < 2^32 /\ 0 <= c_secret (ctx cs) < 2^64
  /\ (c_init_done (ctx cs) = 0 \/ c_init_done (ctx cs) = 1)
  /\ 0 <= c_seq (ctx cs) < 256
  /\ (forall i, 0 <= bounces cs i < 256) /\ (forall i, 0 <= unmap_seq cs i < 256).

Definition fact_active (cs : mstate) : Prop :=
  forall sc g, active cs sc = Some g ->
    0 <= sc < 48 /\ m_sizeclass (get_meta_rec cs g) = sc /\ m_mem (get_meta_rec cs g) <> None.

Definition fact_gmeta (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b ->
    let mr := get_meta_rec cs g in
    meta_slot cs g
    /\ 0 <= m_avail mr < 2^32 /\ 0 <= m_freed mr < 2^32
    /\ 0 <= m_last_idx mr <= 31 /\ m_freeable mr = 1
    /\ ((0 <= m_sizeclass mr < 48 /\ 0 <= m_maplen mr < 2^19) \/ (m_sizeclass mr = 63 /\ m_last_idx mr = 0 /\ 0 < m_maplen mr))
    /\ 0 <= m_maplen mr
    /\ (exists ai, (s_groups cs) !! b = Some (mkGhdr (Some g) ai) /\ 0 <= ai <= m_last_idx mr
                   /\ forall i, 0 <= i -> Z.testbit (m_avail mr) i = true -> i <= ai)
    /\ (exists r, (s_regions cs) !! (fst b) = Some r /\ r_kind r = RKGroup
                  /\ 0 <= snd b /\ snd b mod 16 = 0
                  /\ sstart_of mr (m_last_idx mr + 1) <= round_up_pg (r_len r))
    /\ UNIT <= get_stride mr /\ get_stride mr mod UNIT = 0
    (* [comment removed for export] *)
    /\ (m_sizeclass mr < 48 -> get_stride mr < 2^31)
    /\ (m_sizeclass mr < 48 -> forall i, 0 <= i -> Z.testbit (m_avail mr) i = true ->
          UNIT * size_class (m_sizeclass mr) <= get_stride mr)
    (* [comment removed for export] *)
    /\ (m_sizeclass mr < 48 -> get_stride mr * (m_last_idx mr + 1) < 2^20).

Definition fact_avail_clear (cs : mstate) (LB : list block) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i -> Z.testbit (m_avail (get_meta_rec cs g)) i = true ->
    let mr := get_meta_rec cs g in
    let lo := sstart_of mr i - IB in
    let hi := sstart_of mr i + get_stride mr - IB in
    (forall b' gh, (s_groups cs) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= lo \/ hi <= snd b')
    /\ (forall blk, In blk LB -> fst (blk_slot blk) = fst b ->
          exists r, (s_regions cs) !! (fst b) = Some r /\
          (blk_addr blk + blk_size blk <= r_base r + lo \/ r_base r + hi <= blk_addr blk)).

(* [comment removed for export] *)
Definition fact_free_clear (cs : mstate) (LB : list block) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i ->
    Z.testbit (m_avail (get_meta_rec cs g)) i = true \/ Z.testbit (m_freed (get_meta_rec cs g)) i = true ->
    let mr := get_meta_rec cs g in
    let lo := sstart_of mr i - IB in
    let hi := sstart_of mr i + get_stride mr - IB in
    (forall b' gh, (s_groups cs) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= lo \/ hi <= snd b')
    /\ (forall blk, In blk LB -> fst (blk_slot blk) = fst b ->
          exists r, (s_regions cs) !! (fst b) = Some r /\
          (blk_addr blk + blk_size blk <= r_base r + lo \/ r_base r + hi <= blk_addr blk)).

(* [comment removed for export] *)
Definition fact_hdr_clear (cs : mstate) (LB : list block) : Prop :=
  forall b gh blk r, (s_groups cs) !! b = Some gh -> In blk LB -> fst (blk_slot blk) = fst b ->
    (s_regions cs) !! (fst b) = Some r ->
    blk_addr blk + blk_size blk <= r_base r + snd b \/ r_base r + snd b + 16 <= blk_addr blk.

(* [comment removed for export] *)
Definition fact_usage (cs : mstate) : Prop := forall i, 0 <= usage cs i < 2^60.

(* [comment removed for export] *)
Definition fact_masks (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b ->
    let mr := get_meta_rec cs g in
    (forall i, 0 <= i -> Z.testbit (m_avail mr) i = true -> i <= m_last_idx mr)
    /\ (forall i, 0 <= i -> Z.testbit (m_freed mr) i = true -> i <= m_last_idx mr)
    /\ Z.land (m_avail mr) (m_freed mr) = 0.

(* [comment removed for export] *)
Definition fact_maplen (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b -> m_maplen (get_meta_rec cs g) < 2^40.

(* [comment removed for export] *)
Definition fact_slots (cs : mstate) : Prop :=
  forall p g idx, (s_slots cs) !! p = Some (g, idx) ->
    exists b, m_mem (get_meta_rec cs g) = Some b /\ fst p = fst b
              /\ snd p = sstart_of (get_meta_rec cs g) idx /\ 0 <= idx <= m_last_idx (get_meta_rec cs g).

(* [comment removed for export] *)
Definition fact_slots_complete (cs : mstate) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i <= m_last_idx (get_meta_rec cs g) ->
    (s_slots cs) !! (fst b, sstart_of (get_meta_rec cs g) i) = Some (g, i).

(* [comment removed for export] *)
Definition fact_ptrs (st : mstate) : Prop :=
  ptrs_in (fun rid => (rid < s_next_rid st)%N) st
  /\ (forall rid, (s_next_rid st <= rid)%N -> (s_regions st) !! rid = None /\ (s_shadow st) !! rid = None).

(* [comment removed for export] *)
Definition fact_blk_unknown (st : mstate) (LB : list block) : Prop :=
  forall blk r, In blk LB -> (s_regions st) !! (fst (blk_slot blk)) = Some r ->
    forall a, blk_addr blk <= a < blk_addr blk + blk_size blk ->
      exists h, cell_read (get_shadow st (fst (blk_slot blk))) (a - r_base r) = Unknown h.

(* [comment removed for export] *)
Definition fact_blocks_disjoint (st : mstate) (LB : list block) : Prop :=
  forall b1 b2, In b1 LB -> In b2 LB -> fst (blk_slot b1) = fst (blk_slot b2) -> blk_slot b1 <> blk_slot b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.

(* [comment removed for export] *)
Definition fact_hdr0 (st : mstate) : Prop :=
  forall g b i, m_mem (get_meta_rec st g) = Some b -> 0 <= i <= m_last_idx (get_meta_rec st g) + 1 ->
    cell_read (get_shadow st (fst b)) (sstart_of (get_meta_rec st g) i - IB) = Known 0.

(* [comment removed for export] *)
Definition fact_cell_ticks (st : mstate) : Prop :=
  forall rid sh o v t, (s_shadow st) !! rid = Some sh -> (r_cells sh) !! o = Some (v, t) -> (t <= s_tick st)%N.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record MFACTS_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkMF {
  mf_blocks : Forall (block_ok st) LB;
  (* [comment removed for export] *)
  mf_nodup : List.NoDup (map blk_slot LB);
  (* [comment removed for export] *)
  mf_ticks : ticks_ok st;
  (* [comment removed for export] *)
  mf_reserved : s_reserved st = resv;
  mf_ctx : fact_ctx (strip st);
  mf_active : fact_active (strip st);
  mf_gmeta : fact_gmeta (strip st);
  mf_avail_clear : fact_avail_clear (strip st) LB;
  mf_hdr0 : fact_hdr0 st;
  (* [comment removed for export] *)
  mf_free_clear : fact_free_clear (strip st) LB;
  mf_hdr_clear : fact_hdr_clear (strip st) LB;
  mf_usage : fact_usage (strip st);
  mf_masks : fact_masks (strip st);
  mf_maplen : fact_maplen (strip st);
  mf_slots : fact_slots (strip st);
  mf_slots_complete : fact_slots_complete (strip st);
  (* [comment removed for export] *)
  mf_ptrs : fact_ptrs st;
  mf_blk_unknown : fact_blk_unknown st LB;
  mf_blocks_disjoint : fact_blocks_disjoint st LB;
  (* [comment removed for export] *)
  mf_cell_ticks : fact_cell_ticks st
}.

(* [comment removed for export] *)

End PORT.

End WithCeil.
End MallocFacts_A.

(* [comment removed for export] *)
Module MallocKit_A.
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma ticks_ok_upd_meta st g f : ticks_ok st -> ticks_ok (upd_meta g f st).
Proof. intros T; exact T. Qed.
#[using="Type"] Lemma ticks_ok_upd_ctx st f : ticks_ok st -> ticks_ok (upd_ctx f st).
Proof. intros T; exact T. Qed.
#[using="Type"] Lemma ticks_ok_wr16 st p v : ticks_ok st -> ticks_ok (wr16 p v st).
Proof. intros T. unfold wr16. apply ticks_ok_wr8, ticks_ok_wr8, T. Qed.
#[using="Type"] Lemma ticks_ok_wr32 st p v : ticks_ok st -> ticks_ok (wr32 p v st).
Proof. intros T. unfold wr32. repeat apply ticks_ok_wr8. exact T. Qed.
#[using="Type"] Lemma ticks_ok_set_size p e n b st : ticks_ok st -> ticks_ok (set_size p e n b st).
Proof.
  intros T. unfold set_size.
  destruct (5 <=? _); destruct (negb _); repeat first [apply ticks_ok_wr8 | apply ticks_ok_wr32]; exact T.
Qed.

#[using="Type"] Lemma get_shadow_set_tick st t rid : get_shadow (set_tick t st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_upd_meta st g f rid : get_shadow (upd_meta g f st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_wr8 st p v : s_regions (wr8 p v st) = s_regions st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_wr8 st p v : s_groups (wr8 p v st) = s_groups st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_wr8 st p v q : conc (wr8 p v st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_wr16 st p v q : conc (wr16 p v st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_set_tick st t q : conc (set_tick t st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_upd_meta st g f q : conc (upd_meta g f st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_havoc st p n q : conc (havoc p n st) q = conc st q.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma conc_set_size p e n b st q : conc (set_size p e n b st) q = conc st q.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma conc_enframe_at st g k n off q : conc (fst (enframe_at st g k n off)) q = conc st q.
Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn [fst]; rewrite conc_set_size; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma le4_bytes : forall v, 0 <= v < 2^32 ->
  le4 (wz v) = [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)].
Proof.
  intros v Hv. unfold le4, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^(8+8)) with 65536. change (2^(8+8+8)) with 16777216.
  assert (E : forall x, Z_to_bv 8 x = Z_to_bv 8 (x mod 256)).
  { intros x. apply Z_to_bv8_mod. change (2^8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite (E v) at 1. rewrite (E (v / 256)) at 1. rewrite (E (v / 65536)) at 1. reflexivity.
Qed.

#[using="Type"] Lemma lowbit_facts : forall v, 0 < v < 2^32 -> exists k, 0 <= k < 32 /\ lowbit v = 2 ^ k.
Proof.
  intros v Hv. destruct (lowbit_pow2 v ltac:(lia)) as (k & Hk & E & Hle). exists k.
  split; [|unfold lowbit; exact E]. split; [exact Hk|].
  destruct (Z.lt_ge_cases k 32) as [?|GE]; [assumption|].
  assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma b8_of_byte : forall x : byte, b8 (bv_unsigned x) = x.
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

End PORT.

End WithCeil.
End MallocKit_A.

(* [comment removed for export] *)
Module ASlot_W1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Section TA.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition ta_avz (st3 : mstate) (m3 : aptr) : Malloc.M R :=
  activate_group m3 st3 (fun st4 mask =>
    guard 40 (negb (mask =? 0)) (
      ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail.

(* [comment removed for export] *)
Definition ta_act (st2 : mstate) (m2 : aptr) (mask : Z) : Malloc.M R :=
  let mr2 := get_meta_rec st2 m2 in
  let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
  let '(st3, m3) :=
    if Z.land mask (mask_upto gai) =? 0 then
      if negb (optr_eqb (m_next mr2) (Some m2)) then
        match m_next mr2 with
        | Some mn => (set_active sc (Some mn) st2, mn)
        | None => (st2, m2)
        end
      else
        let cnt := gai + 2 in
        let size := size_class (m_sizeclass mr2) * UNIT in
        let span := UNIT + size * cnt in
        let cnt := span_loop 300%nat cnt span size in
        let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
        match m_mem mr2 with
        | Some g => (set_group_active_idx g (cnt - 1) st2, m2)
        | None => (st2, m2)
        end
    else (st2, m2) in
  ta_avz st3 m3.

(* [comment removed for export] *)
Definition ta_m (st1 : mstate) (m1 : aptr) : Malloc.M R :=
  let mask := m_freed (get_meta_rec st1 m1) in
  let '(st2, m2, mask) :=
    let mr := get_meta_rec st1 m1 in
    if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
      match m_next mr with
      | Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
      | None => (st1, m1, mask)
      end
    else (st1, m1, mask) in
  ta_act st2 m2 mask.

(* [comment removed for export] *)
#[using="Type"] Lemma try_avail_eq st :
  try_avail sc st k bail =
  match active st sc with
  | None => k st 0
  | Some m =>
    if negb (m_avail (get_meta_rec st m) =? 0) then ta_fin st m (m_avail (get_meta_rec st m)) k else
    let step1 : option (mstate * aptr) :=
      if m_freed (get_meta_rec st m) =? 0 then
        let st1 := dequeue (LActive sc) m st in
        match active st1 sc with None => None | Some m1 => Some (st1, m1) end
      else
        match m_next (get_meta_rec st m) with
        | Some m1 => Some (set_active sc (Some m1) st, m1)
        | None => None
        end in
    match step1 with
    | None => if m_freed (get_meta_rec st m) =? 0 then k (dequeue (LActive sc) m st) 0
              else SVis (EUndef UBadPtr) (fun _ => bail)
    | Some (st1, m1) => ta_m st1 m1
    end
  end.
Proof. reflexivity. Qed.
End TA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AS.
Context {R : Type}.
Variables (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition as_grp (st1 : mstate) : Malloc.M R :=
  alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
    match go with
    | None => k st2 (-1)
    | Some g =>
      let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
      queue (LActive sc) g st3 (fun st4 => k st4 0) bail
    end) bail.

Definition as_k (st1 : mstate) (first : Z) : Malloc.M R :=
  if negb (first =? 0) then k st1 (ctz32 first) else as_grp st1.

#[using="Type"] Lemma alloc_slot_S st : alloc_slot lay (S f) st sc req k bail = try_avail sc st as_k bail.
Proof. reflexivity. Qed.
End AS.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint span_exit (fuel : nat) (span size : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_exit f (span + size) size else true
  end.

(* [comment removed for export] *)
Definition span_fn (sc cnt : Z) : bool :=
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16).
Definition span_chk (sc : Z) : bool := forallb (span_fn sc) (zseq 2 32).

#[using="Type"] Lemma span_chk_true : forallb span_chk (zseq 1 47) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma span_fn_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 -> span_fn sc cnt = true.
Proof.
  intros Hsc Hc.
  pose proof (forallb_zseq span_chk 1 47 sc span_chk_true ltac:(lia) ltac:(lia)) as X. unfold span_chk in X.
  exact (forallb_zseq (span_fn sc) 2 32 cnt X ltac:(lia) ltac:(lia)).
Qed.

#[using="Type"] Lemma span_exit_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 ->
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16) = true.
Proof. intros Hsc Hc. exact (span_fn_ok sc cnt Hsc Hc). Qed.

End PORT.

End WithCeil.
End ASlot_W1.

(* [comment removed for export] *)
Module F_am_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate :=
  upd_meta q clr_links (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).

End PORT.

End WithCeil.
End F_am_A.

(* [comment removed for export] *)
Module F_am_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
  cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
       c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma am_take_eq {R} st (k : mstate -> optr -> M R) bail q :
  c_avail_meta (ctx st) = Some q ->
  am_take st k bail = k (am_took st q (c_avail_meta_count (ctx st) - 1)) (Some q).
Proof. intros H. unfold am_take. rewrite H. reflexivity. Qed.

End PORT.

End WithCeil.
End F_am_D.

(* [comment removed for export] *)
Module F_am_K.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma zeros_length n : length (zeros n) = n. Proof. unfold zeros. apply repeat_length. Qed.

#[using="Type"] Lemma le8_zero : le8 (wz 0) = zeros 8. Proof. reflexivity. Qed.
#[using="Type"] Lemma le4_zero : le4 (wz 0) = zeros 4. Proof. reflexivity. Qed.

#[using="Type"] Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition carve_st (st : mstate) (p : aptr) : mstate :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3.

#[using="Type"] Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
  am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End PORT.

End WithCeil.
End F_am_K.

(* [comment removed for export] *)
Module F_am_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition pgal (z : Z) : Prop := z mod 4096 = 0.

(* [comment removed for export] *)
#[using="Type"] Lemma carve_st_some st p tl ar :
  c_meta_area_tail (ctx st) = Some tl -> (s_areas st) !! tl = Some ar -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
  intros HT Har Hp. assert (NE : tl <> p) by (intros ->; rewrite Hp in Har; discriminate).
  unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Har. rewrite lookup_insert_ne by exact NE. rewrite Hp. reflexivity.
Qed.

#[using="Type"] Lemma carve_st_none st p :
  c_meta_area_tail (ctx st) = None -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := upd_ctx (set_meta_area_head (Some p)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
  intros HT Hp. unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Hp. reflexivity.
Qed.

(* [comment removed for export] *)

End PORT.

End WithCeil.
End F_am_C.

(* [comment removed for export] *)
Module F_am_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

(* [comment removed for export] *)
Definition am_init_st (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

End PORT.

End WithCeil.
End F_am_E.

(* [comment removed for export] *)
Module F_free_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma self_word2 b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (Z.land b3 31 mod 32))) = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

(* [comment removed for export] *)

End PORT.

End WithCeil.
End F_free_A.

(* [comment removed for export] *)
Module F_free_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
End F_free_B.

(* [comment removed for export] *)
Module F_ntf_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
End F_ntf_E.

(* [comment removed for export] *)
Module F_ntf_F.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_E.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition seq_st (ns sc : Z) (st : mstate) : mstate := record_seq sc (upd_ctx (set_seq ns) st).

#[using="Type"] Lemma fm_facts_ctx : forall st f g,
  c_free_meta_head (f (s_ctx st)) = c_free_meta_head (s_ctx st) -> fm_facts st g -> fm_facts (upd_ctx f st) g.
Proof. intros st f g E H hd Hh. unfold ctx in *. cbn [upd_ctx s_ctx] in Hh. rewrite E in Hh. exact (H hd Hh). Qed.

#[using="Type"] Lemma seq_range_test sc : 0 <= sc <= 63 ->
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

(* [comment removed for export] *)
#[using="Type"] Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.

End PORT.

End WithCeil.
End F_ntf_F.

(* [comment removed for export] *)
Module F_ntf_G.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
End F_ntf_G.

(* [comment removed for export] *)
Module F_ntf_H.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition ntf_cond (st : mstate) (g : aptr) (i : Z) : bool :=
  let mr := get_meta_rec st g in
  (Z.lor (m_freed mr) (m_avail mr) + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g.

(* [comment removed for export] *)
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
End POST.

Record entry_hyps (st : mstate) (g : aptr) (i : Z) : Prop := mkEH {
  eh_slot : meta_slot st g;
  eh_mw : mw_ok (get_meta_rec st g);
  eh_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  eh_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  eh_i : 0 <= i <= m_last_idx (get_meta_rec st g);
  (* [comment removed for export] *)
  eh_sc : m_sizeclass (get_meta_rec st g) < 48 \/ m_sizeclass (get_meta_rec st g) = 63;
  (* [comment removed for export] *)
  eh_next : forall nx, m_next (get_meta_rec st g) = Some nx -> meta_slot st nx;
  eh_head : forall h, active st (m_sizeclass (get_meta_rec st g)) = Some h -> meta_slot st h;
  eh_ctx : (forall j, 0 <= bounces st j < 256) /\ (m_sizeclass (get_meta_rec st g) < 48 -> 0 <= usage st (m_sizeclass (get_meta_rec st g)) < 2^64);
  (* [comment removed for export] *)
  eh_g50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48;
  eh_g51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48;
  (* [comment removed for export] *)
  eh_g1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
          m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g
}.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Hypothesis EH : entry_hyps st g i.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 80.

(* [comment removed for export] *)
#[using="i EH"] Lemma maskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
#[using="Type"] Lemma maskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ntf_cond_unfold :
  ntf_cond st g i = ((mask + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g)%bool.
Proof. reflexivity. Qed.

#[using="Type"] Lemma okf_unfold :
  okay_to_free st g =
    if m_freeable mr =? 0 then false
    else if (48 <=? sc) || (get_stride mr <? UNIT * size_class sc) then true
    else if m_maplen mr =? 0 then true
    else if negb (optr_eqb (m_next mr) (Some g)) then true
    else if negb (is_bouncing sc st) then true
    else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false.
Proof. reflexivity. Qed.

Ltac post_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].

(* [comment removed for export] *)
End ENTRY.

End PORT.

End WithCeil.
End F_ntf_H.

(* [comment removed for export] *)
Module MallocNat.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocRep MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma steq_trans {E A R} (t1 t2 t3 : stree E A R) : steq t1 t2 -> steq t2 t3 -> steq t1 t3.
Proof.
  intros H1 H2. apply strel_eq_steq. apply strel_eq_steq in H1. apply strel_eq_steq in H2.
  eapply strel_trans_eq; [exact H1| exact H2].
Qed.

#[using="Type"] Lemma steq_sbind {E A R S} (t1 t2 : stree E A R) (f1 f2 : R -> stree E A S) :
  steq t1 t2 -> (forall r, steq (f1 r) (f2 r)) -> steq (sbind t1 f1) (sbind t2 f2).
Proof.
  intros Ht Hf. apply strel_eq_steq. eapply (strel_sbind (RR := eq)); [apply strel_eq_steq; exact Ht|].
  intros r1 r2 ->. apply strel_eq_steq. apply Hf.
Qed.

#[using="Type"] Lemma eruns_steq {E A O R} (sel : O -> E -> option A) (upd : O -> E -> A -> O) (t1 t2 : stree E A R) :
  steq t1 t2 -> forall o, steq (eruns sel upd o t1) (eruns sel upd o t2).
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros o; cbn [eruns].
  - constructor.
  - destruct (sel o e) as [a|]; [apply IH|]. constructor. intros a. apply IH.
Qed.

Definition kS {X Y : Type} : X -> Y -> Malloc.M (option (X * Y)) := fun x y => SRet (Some (x, y)).
Definition bS {T : Type} : Malloc.M (option T) := SRet None.
Definition KF {X Y R : Type} (k : X -> Y -> Malloc.M R) (bail : Malloc.M R) (r : option (X * Y)) : Malloc.M R :=
  match r with Some (x, y) => k x y | None => bail end.
(* [comment removed for export] *)
Definition kS1 {X : Type} : X -> Malloc.M (option X) := fun x => SRet (Some x).
Definition KF1 {X R : Type} (k : X -> Malloc.M R) (bail : Malloc.M R) (r : option X) : Malloc.M R :=
  match r with Some x => k x | None => bail end.

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac nat_leaf := cbn [sbind KF KF1 kS kS1 bS]; apply steq_refl.
Ltac nat_vis := cbn [sbind]; apply steq_vis; intros ?.
Ltac nat_case :=
  lazymatch goal with
  | |- steq _ (sbind (match ?c with _ => _ end) _) => destruct c
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac nat_call NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [[? ?]|]; cbn [KF sbind].
Ltac nat_call1 NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [?|]; cbn [KF1 sbind].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma guard_nat {X Y R} tag c (K : Malloc.M R) (K' : Malloc.M (option (X * Y))) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

#[using="Type"] Lemma guard_nat1 {X R} tag c (K : Malloc.M R) (K' : Malloc.M (option X)) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

#[using="Type"] Lemma queue_nat {R} h m st (k : mstate -> Malloc.M R) bail :
  steq (queue h m st k bail) (sbind (queue h m st kS1 bS) (KF1 k bail)).
Proof.
  unfold queue. apply guard_nat1; [|nat_leaf]. apply guard_nat1; [|nat_leaf].
  nat_case; cbv zeta; [destruct (m_prev _)|]; nat_leaf.
Qed.

#[using="Type"] Lemma free_meta_nat {R} m st (k : mstate -> Malloc.M R) bail :
  steq (free_meta m st k bail) (sbind (free_meta m st kS1 bS) (KF1 k bail)).
Proof. unfold free_meta. apply queue_nat. Qed.

#[using="Type"] Lemma activate_group_nat {R} m st (k : mstate -> Z -> Malloc.M R) bail :
  steq (activate_group m st k bail) (sbind (activate_group m st kS bS) (KF k bail)).
Proof. unfold activate_group. apply guard_nat; [|nat_leaf]. cbv zeta. nat_leaf. Qed.

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac nat_auto cal :=
  first [ nat_leaf
        | cal
        | nat_vis; nat_auto cal
        | nat_case; nat_auto cal
        | progress (cbv zeta); nat_auto cal ].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma am_take_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_take st k bail) (sbind (am_take st kS bS) (KF k bail)).
Proof. unfold am_take. nat_auto fail. Qed.

#[using="Type"] Lemma am_carve_nat {R} st p (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_carve st p k bail) (sbind (am_carve st p kS bS) (KF k bail)).
Proof. unfold am_carve. cbv zeta. apply am_take_nat. Qed.

#[using="Type"] Lemma am_finish_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_finish st nu k bail) (sbind (am_finish st nu kS bS) (KF k bail)).
Proof. unfold am_finish, bad_answer. nat_auto ltac:(apply am_carve_nat). Qed.

#[using="Type"] Lemma am_after_brk_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_after_brk st nu k bail) (sbind (am_after_brk st nu kS bS) (KF k bail)).
Proof. unfold am_after_brk, bad_answer. nat_auto ltac:(apply am_finish_nat). Qed.

#[using="Type"] Lemma alloc_meta_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_meta st k bail) (sbind (alloc_meta st kS bS) (KF k bail)).
Proof.
  unfold alloc_meta, bad_answer. nat_auto ltac:(first [apply am_take_nat | apply am_after_brk_nat]).
Qed.

#[using="Type"] Lemma ta_fin_nat {R} st m mask (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) :
  steq (ta_fin st m mask k) (sbind (ta_fin st m mask kS) (KF k bail)).
Proof. unfold ta_fin. cbv zeta. nat_leaf. Qed.

#[using="Type"] Lemma try_avail_nat {R} sc st (k : mstate -> Z -> Malloc.M R) bail :
  steq (try_avail sc st k bail) (sbind (try_avail sc st kS bS) (KF k bail)).
Proof.
  unfold try_avail. nat_case; [|nat_leaf]. cbv zeta. nat_case; [apply ta_fin_nat|].
  nat_case.
  - destruct p as [st1 m1]. nat_case. destruct p as [st2 m2]. nat_case.
    eapply steq_trans; [apply activate_group_nat|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply activate_group_nat| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st4 mask]|]; cbn [KF sbind]; [|nat_leaf].
    apply guard_nat; [apply ta_fin_nat| nat_leaf].
  - nat_case; [nat_leaf|]. nat_vis. nat_leaf.
Qed.

#[using="Type"] Lemma ag_tail_nat {R} lay st sc m p cnt ai (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) :
  steq (ag_tail lay st sc m p cnt ai k) (sbind (ag_tail lay st sc m p cnt ai kS) (KF k bail)).
Proof. unfold ag_tail. cbv zeta. nat_leaf. Qed.

Section AG.
Variable lay : layout_hook.
Variable rec : forall R, mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R.
Hypothesis rec_nat : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (rec R st sc req k bail) (sbind (rec _ st sc req kS bS) (KF k bail)).

#[using="rec_nat"] Lemma alloc_group_nat {R} st sc req (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_group R lay (rec R) st sc req k bail)
       (sbind (alloc_group _ lay (rec _) st sc req kS bS) (KF k bail)).
Proof.
  unfold alloc_group, bad_answer. cbv zeta. nat_call (@alloc_meta_nat); [|nat_leaf].
  nat_case; [|nat_leaf]. nat_case.
  - (* [comment removed for export] *)
    match goal with |- steq _ (sbind (let '(_, _) := ?p in _) _) => destruct p as [cnt' needed] end.
    nat_vis. nat_case; [nat_vis; nat_leaf|]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case. cbv zeta. apply ag_tail_nat.
  - (* [comment removed for export] *)
    nat_call rec_nat; [|nat_leaf]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case; [|nat_vis; nat_leaf]. cbv zeta. apply ag_tail_nat.
Qed.
End AG.

#[using="Type"] Lemma alloc_slot_nat lay fuel : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (alloc_slot lay fuel st sc req k bail) (sbind (alloc_slot lay fuel st sc req kS bS) (KF k bail)).
Proof.
  induction fuel as [|f IH]; intros R st sc req k bail.
  - cbn [alloc_slot]. nat_vis. nat_leaf.
  - cbn [alloc_slot]. nat_call (@try_avail_nat); [|nat_leaf]. nat_case; [nat_leaf|].
    eapply steq_trans; [apply (alloc_group_nat lay (fun R => @alloc_slot _ R lay f) IH)|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply (alloc_group_nat lay (fun R => @alloc_slot _ R lay f) IH)| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st2 go]|]; cbn [KF sbind]; [|nat_leaf].
    nat_case; [|nat_leaf]. cbv zeta. nat_call1 (@queue_nat); nat_leaf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End PORT.

End WithCeil.
End MallocNat.

(* [comment removed for export] *)
Module MallocFacts_AS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocNat.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition ta_fail (sc : Z) (st st1 : mstate) : Prop :=
  try_avail sc st kS bS = SRet (Some (st1, 0)).

(* [comment removed for export] *)
Definition req_ok (sc req : Z) : Prop := 0 <= req /\ req + IB <= UNIT * size_class sc.

(* [comment removed for export] *)
Inductive IST (st0 : mstate) : mstate -> Prop :=
| ist_top : forall t, (s_tick st0 < t)%N -> IST st0 (set_tick t st0)
| ist_am : forall o st sc st1 st2 m,
    IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
    leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
    IST st0 st2.

(* [comment removed for export] *)
Definition ISTR (st0 st3 : mstate) : Prop :=
  exists o st f sc req idx,
    IST st0 st /\ 0 <= sc < 48 /\ req_ok sc req /\
    leaf_of o (alloc_slot full_lay f st sc req kS bS) (Some (st3, idx)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lmem (cs : mstate) (g : aptr) : Prop :=
  m_mem (get_meta_rec cs g) <> None /\ m_next (get_meta_rec cs g) <> None /\ m_prev (get_meta_rec cs g) <> None.

Definition fact_lists (cs : mstate) : Prop :=
  (forall sc g, active cs sc = Some g -> lmem cs g)
  /\ (forall g n, m_mem (get_meta_rec cs g) <> None -> m_next (get_meta_rec cs g) = Some n ->
        lmem cs n /\ m_sizeclass (get_meta_rec cs n) = m_sizeclass (get_meta_rec cs g))
  /\ (forall g p, m_mem (get_meta_rec cs g) <> None -> m_prev (get_meta_rec cs g) = Some p ->
        lmem cs p /\ m_sizeclass (get_meta_rec cs p) = m_sizeclass (get_meta_rec cs g)).

Definition fact_freelist (cs : mstate) : Prop :=
  forall h, c_free_meta_head (ctx cs) = Some h ->
    meta_slot cs h /\ m_mem (get_meta_rec cs h) = None /\ m_next (get_meta_rec cs h) <> None
    /\ exists p, m_prev (get_meta_rec cs h) = Some p /\ meta_slot cs p /\ m_mem (get_meta_rec cs p) = None
                 /\ m_next (get_meta_rec cs p) <> None.

Definition mw_ok (mr : meta) : Prop :=
  0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Definition fact_mw (cs : mstate) : Prop :=
  forall g, mw_ok (get_meta_rec cs g) /\ 0 <= m_avail (get_meta_rec cs g) < 2^32 /\ 0 <= m_freed (get_meta_rec cs g) < 2^32.

Definition fact_host_stride (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b -> 0 <= m_sizeclass (get_meta_rec cs g) <= 27 ->
    get_stride (get_meta_rec cs g) = UNIT * size_class (m_sizeclass (get_meta_rec cs g)).

(* [comment removed for export] *)
Definition fact_links (cs : mstate) : Prop :=
  forall g, lmem cs g ->
    (forall n, m_next (get_meta_rec cs g) = Some n -> m_prev (get_meta_rec cs n) = Some g)
    /\ (forall p, m_prev (get_meta_rec cs g) = Some p -> m_next (get_meta_rec cs p) = Some g).

Definition fact_sc0_full (cs : mstate) : Prop :=
  forall g b gh, m_mem (get_meta_rec cs g) = Some b -> (s_groups cs) !! b = Some gh ->
    m_sizeclass (get_meta_rec cs g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec cs g).

Definition fact_ghdr_unk (st : mstate) : Prop :=
  forall b gh o, (s_groups st) !! b = Some gh -> 0 <= o < 9 ->
    exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h.

(* [comment removed for export] *)
Definition fact_bit_stride (cs : mstate) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i ->
    Z.testbit (m_avail (get_meta_rec cs g)) i || Z.testbit (m_freed (get_meta_rec cs g)) i = true ->
    m_sizeclass (get_meta_rec cs g) < 48 ->
    UNIT * size_class (m_sizeclass (get_meta_rec cs g)) <= get_stride (get_meta_rec cs g).

Record LFACTS (cs : mstate) : Prop := mkLF {
  lf_lists : fact_lists cs;
  lf_freelist : fact_freelist cs;
  lf_mw : fact_mw cs;
  lf_host_stride : fact_host_stride cs;
  lf_links : fact_links cs;
  lf_sc0_full : fact_sc0_full cs;
  lf_bit_stride : fact_bit_stride cs
}.

(* [comment removed for export] *)
Record ISTF_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkISTF {
  isf_mf : @MFACTS_g resv st LB;
  isf_lf : LFACTS (strip st);
  isf_ghdr : fact_ghdr_unk st
}.

(* [comment removed for export] *)
Definition nest_ok (m : aptr) (st3 : mstate) : Prop :=
  get_meta_rec st3 m = meta0
  /\ forall h, c_free_meta_head (ctx st3) = Some h -> h <> m /\ m_prev (get_meta_rec st3 h) <> Some m.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMP_AS_g (resv : list (Z * Z)) (am_pre : mstate -> Prop) : Prop :=
  forall st0 LB st sc st1, AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 -> am_pre st1.

End PORT.

End WithCeil.
End MallocFacts_AS.

(* [comment removed for export] *)
Module MallocTreeB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocRep MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
#[using="Type"] Lemma leaf_of_bind_inv {R S} (o : mem) (t : Malloc.M R) (k : R -> Malloc.M S) (r : S) :
  leaf_of o (sbind t k) r -> exists x, leaf_of o t x /\ leaf_of o (k x) r.
Proof.
  intros (l & ans & l' & H). unfold lrun, prun in H.
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim.steq_follow ans (eruns_sbind (psel pans_l) pupd_l l t k)) in H.
  rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim.follow_sbind in H.
  destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim.followk (eruns (psel pans_l) pupd_l l t) ans) as [[[l1 x] rest]|] eqn:FK; [| discriminate].
  exists x. split.
  - exists l, ans, l1. unfold lrun, prun. exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim.followk_follow _ _ FK).
  - exists l1, rest, l'. unfold lrun, prun. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tree.
Variable segs : list Segment.
Context {St : Type} {AS : AllocSt St}.

#[using="Type"] Lemma raw_calloc_bridge : forall s m n (o : mem) Q1 Q ms,
  implT segs o (calloc (ps_m s) m n) s Q1 ms ->
  (forall st' (p : optr) s' ms', Q1 (st', p) s' ms' -> Q p (set_m st' s') ms') ->
  implM segs (raw_callocF peekG m n) s Q ms.
Proof.
  intros s m n o Q1 Q ms H HQ. unfold raw_callocF.
  eapply (implM_bind segs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind segs _ _ _ Q1); [exact H|].
  intros [st' p] s' ms' H1. cbv beta iota.
  eapply (implM_bind segs _ _ _ (fun _ s2 ms2 => s2 = set_m st' s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done. eapply HQ. exact H1.
Qed.

#[using="Type"] Lemma raw_realloc_bridge : forall s (p : optr) n (o : mem) Q1 Q ms,
  implT segs o (realloc (ps_m s) p n) s Q1 ms ->
  (forall st' (q : optr) s' ms', Q1 (st', q) s' ms' -> Q q (set_m st' s') ms') ->
  implM segs (raw_reallocF peekG p n) s Q ms.
Proof.
  intros s p n o Q1 Q ms H HQ. unfold raw_reallocF.
  eapply (implM_bind segs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind segs _ _ _ Q1); [exact H|].
  intros [st' q] s' ms' H1. cbv beta iota.
  eapply (implM_bind segs _ _ _ (fun _ s2 ms2 => s2 = set_m st' s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done. eapply HQ. exact H1.
Qed.

End Tree.

End WithCeil.
End MallocTreeB.

(* [comment removed for export] *)
Module Malloc_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocRep MallocHINV MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition MALLOC_STACK : Z := 8192.    (* [comment removed for export] *)
Definition FREE_STACK : Z := 8192.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition medtab_cells : list cell := [C1 (Z_to_bv 8 28); C1 (Z_to_bv 8 24); C1 (Z_to_bv 8 20); C1 (Z_to_bv 8 32)].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_block (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

(* [comment removed for export] *)
Definition bptr_eqb (p q : bptr) : bool :=
  aptr_eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).
(* [comment removed for export] *)
Definition lb_remove (p : bptr) (LB : list block) : list block :=
  filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.

(* [comment removed for export] *)

End PORT.

End WithCeil.
End Malloc_iface.
