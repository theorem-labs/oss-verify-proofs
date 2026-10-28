(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocKit_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require KStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_AB.
Import ListNotations.
Open Scope Z_scope.

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

#[using="Hconc"] Lemma pw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

#[using="Hmetas"] Lemma get_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

#[using="P HP Hconc"] Lemma meta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
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
Context {HCEIL : HasCeiling}.
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
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma nr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma nr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite nr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma nr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma nr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite nr_lookup_new in H. inversion H. auto.
  - right. rewrite nr_lookup_old in H by exact NE. auto.
Qed.
#[using="r0"] Lemma nr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.
#[using="r0"] Lemma nr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite nr_lookup_new. reflexivity. Qed.
#[using="Type"] Lemma nr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="st m' rid L ZF"] Lemma nr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

#[using="rid RF"] Lemma nr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="Type"] Lemma ticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.

#[using="Type"] Lemma dr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma dr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
  intros H. rewrite dr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
#[using="Type"] Lemma dr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite dr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma dr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite dr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma dr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

#[using="Type"] Lemma ticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
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