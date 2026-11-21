(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MallocKit_A2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma pw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma get_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma meta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !pw_extP by assumption. reflexivity.
Qed.
End PEXT.


Definition agree_on (m m' : mem) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

Lemma agree_on_sub m m' A n A' n' : agree_on m m' A n -> A <= A' -> A' + n' <= A + n -> agree_on m m' A' n'.
Proof. intros AG H1 H2 a Ha. apply AG. lia. Qed.


Lemma mmap_len_round_up l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply KStep.round_up_pg_eq. Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia. Qed.

Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read, shadow0. cbn. rewrite !lookup_empty. reflexivity. Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= ATOP.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma nr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
Lemma nr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite nr_regions. apply lookup_insert_eq. Qed.
Lemma nr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma nr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite nr_lookup_new in H. inversion H. auto.
  - right. rewrite nr_lookup_old in H by exact NE. auto.
Qed.
Lemma nr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.
Lemma nr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite nr_lookup_new. reflexivity. Qed.
Lemma nr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
Lemma nr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

Lemma nr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma ticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (MLOCK <= a < MLOCK + 4 \/ LIBC <= a < LIBC + 0x408 \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).

Lemma dr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
Lemma dr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
  intros H. rewrite dr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma dr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite dr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma dr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite dr_lookup_old by assumption. reflexivity. Qed.
Lemma dr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma ticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
  intros [T1 T2]. split.
  - intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
  - intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

Lemma ptrs_in_set_tick P st t : ptrs_in P st -> ptrs_in P (set_tick t st).
Proof. intros H; exact H. Qed.
Lemma ptrs_in_upd_ctx_scalar P st f :
  (forall c, c_free_meta_head (f c) = c_free_meta_head c) -> (forall c, c_avail_meta (f c) = c_avail_meta c) ->
  (forall c, c_meta_area_head (f c) = c_meta_area_head c) -> (forall c, c_meta_area_tail (f c) = c_meta_area_tail c) ->
  (forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) -> (forall c, c_active (f c) = c_active c) ->
  (forall c, c_brk (f c) = c_brk c) ->
  ptrs_in P st -> ptrs_in P (upd_ctx f st).
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
  rewrite E1, E2, E3, E4, E5, E6, E7.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [|split; [exact H9| exact H10]].
  intros g. exact (H8 g).
Qed.
Lemma ptrs_in_step_seq P st : ptrs_in P st -> ptrs_in P (step_seq st).
Proof. intros H. unfold step_seq. destruct (c_seq (ctx st) =? 255); (apply ptrs_in_upd_ctx_scalar; [..|exact H]; reflexivity). Qed.
Lemma ptrs_in_put_meta P st g mr :
  optr_in P (m_prev mr) -> optr_in P (m_next mr) -> optr_in P (m_mem mr) ->
  ptrs_in P st -> ptrs_in P (put_meta g mr st).
Proof.
  intros Q1 Q2 Q3 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx put_meta set_metas s_metas s_areas s_groups] in *.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [|auto]. intros g'. unfold get_meta_rec. cbn [s_metas put_meta set_metas].
  destruct (decide (g' = g)) as [->|NE].
  - rewrite lookup_insert_eq. cbn. auto.
  - rewrite lookup_insert_ne by congruence. apply H8.
Qed.
Lemma ptrs_in_put_group P st b mo ai :
  P (fst b) -> optr_in P mo -> ptrs_in P st -> ptrs_in P (put_group b mo ai st).
Proof.
  intros Q1 Q2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx put_group set_groups s_metas s_areas s_groups get_meta_rec] in *.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [exact H8|]. split; [exact H9|].
  intros b' gh Hb'. destruct (decide (b' = b)) as [->|NE].
  - rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. cbn. auto.
  - rewrite lookup_insert_ne in Hb' by congruence. exact (H10 b' gh Hb').
Qed.
Lemma ptrs_in_hdr_havoc P st b : ptrs_in P st -> ptrs_in P (hdr_havoc b st).
Proof. intros H; exact H. Qed.
Lemma ptrs_in_set_slots P st v : ptrs_in P st -> ptrs_in P (set_slots v st).
Proof. intros H; exact H. Qed.

End CANSEC1.
End MallocKit_A2.

Module MallocKit_B3.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. Import MM13. Import MM13.MallocKit_B. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
  unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
  destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma usages_set_usage st sc v : 0 <= sc < 48 ->
  usages (set_usage sc v st) = upd (usages st) (Z.to_nat sc) (wz v).
Proof.
  intros Hsc. unfold usages.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite usage_set_usage.
  destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

End CANSEC1.
Ltac ctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.

Section CANSEC2. Context {rc : runConstT}.
Lemma unmap_seq_set st i v j :
  unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
  unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma unmap_seqs_set st i v : 0 <= i < 32 ->
  unmap_seqs (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) = upd (unmap_seqs st) (Z.to_nat i) (b8 v).
Proof.
  intros Hi. unfold unmap_seqs.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite unmap_seq_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

Lemma step_seq_eq st :
  step_seq st = if c_seq (ctx st) =? 255
                then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
                else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma record_seq_eq sc st :
  record_seq sc st = if sc_in_seq_range sc
                     then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
                     else st.
Proof. reflexivity. Qed.

Lemma conc_upd_ctx st f q : conc (upd_ctx f st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma pw_upd_ctx st f q : pw (upd_ctx f st) q = pw st q. Proof. destruct q; reflexivity. Qed.
Lemma oconc_upd_ctx st f q : oconc (upd_ctx f st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma oconc_set_active st sc v q : oconc (set_active sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
Lemma meta_slot_upd_ctx st f q : meta_slot st q -> meta_slot (upd_ctx f st) q. Proof. intros H; exact H. Qed.
Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q. Proof. intros H; exact H. Qed.
Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q. Proof. intros H; exact H. Qed.

End CANSEC2.
Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
                           ?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.

Section CANSEC3. Context {rc : runConstT}.
Definition mw_ok (mr : meta) : Prop :=
  0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
  intros (LI & FB & SCR & ML).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof.
  intros (LI & FB & SCR & ML).
  change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia.
  replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_shr6_range mr : mw_ok mr -> 0 <= Z.shiftr (meta_word mr) 6 < 2^64.
Proof. intros H. pose proof (meta_word_range mr H). destruct H as (LI & FB & SCR & ML). rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof.
  intros (LI & FB & SCR & ML).
  assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^6) with 64. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof.
  intros (LI & FB & SCR & ML).
  rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.

Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof.
  intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land. reflexivity.
Qed.



Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
  intros Hf Ha.
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
  intros Hf Ha. split; [apply Z.land_nonneg; lia|].
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof.
  intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
  rewrite sxv_mod32. reflexivity.
Qed.

Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof.
  intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof.
  intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
  rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.

End CANSEC3.
Ltac unmask64 K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
End MallocKit_B3.
