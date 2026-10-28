(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From Stdlib Require Lia. 
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module ASlot_W1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
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
Lemma try_avail_eq st :
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

Lemma alloc_slot_S st : alloc_slot lay (S f) st sc req k bail = try_avail sc st as_k bail.
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

Lemma span_chk_true : forallb span_chk (zseq 1 47) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma span_fn_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 -> span_fn sc cnt = true.
Proof.
  intros Hsc Hc.
  pose proof (forallb_zseq span_chk 1 47 sc span_chk_true ltac:(lia) ltac:(lia)) as X. unfold span_chk in X.
  exact (forallb_zseq (span_fn sc) 2 32 cnt X ltac:(lia) ltac:(lia)).
Qed.

Lemma span_exit_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 ->
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16) = true.
Proof. intros Hsc Hc. exact (span_fn_ok sc cnt Hsc Hc). Qed.

End ACeilS1.
End ASlot_W1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : mrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : mrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

(* [comment removed for export] *)
End SLOT.

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

(* [comment removed for export] *)
Definition malloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
  alloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
  \/ fresh_addr st a.

Record mrel (st st' : mstate) : Prop := mkMREL {
  mrel_regions : forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r';
  mrel_next : (s_next_rid st <= s_next_rid st')%N;
  mrel_reserved : s_reserved st' = s_reserved st
}.

(* [comment removed for export] *)

Lemma mrel_trans st1 st2 st3 : mrel st1 st2 -> mrel st2 st3 -> mrel st1 st3.
Proof.
  intros [R1 N1 S1] [R2 N2 S2]. split; [| lia | congruence].
  intros rid r H. cps_destruct (R1 rid r H) as (r' & H' & K' & B' & L'). cps_destruct (R2 rid r' H') as (r'' & H'' & K'' & B'' & L'').
  exists r''. repeat split; auto; try congruence. lia.
Qed.

Lemma round_up_pg_eq x : round_up_pg x = x + (- x) mod 4096.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_mono x y : x <= y -> round_up_pg x <= round_up_pg y.
Proof. intros H. rewrite !round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : MFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

(* [comment removed for export] *)

(* [comment removed for export] *)
End FASTFACTS.

End ACeilS1.
