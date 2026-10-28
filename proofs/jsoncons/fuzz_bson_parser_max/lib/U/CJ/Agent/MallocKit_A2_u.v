(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u MallocTree_u MallocKit_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require KStep.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_AB_u.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)

Lemma area_rep_extP m a ar : (s_areas st) !! a = Some ar -> area_rep st m a ar -> area_rep st' m a ar.
Proof.
  intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold area_rep. rewrite (Hconc a Pa). rewrite (pw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite get_meta_rec_extP, meta_cells_extP. apply A2. exact Hk.
Qed.

Lemma group_rep_extP m b gh : (s_groups st) !! b = Some gh -> group_rep st m b gh -> group_rep st' m b gh.
Proof.
  intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (pw_extP _ Pg). auto.
Qed.
End PEXT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on (m m' : mem) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

Lemma bytes_at_agree m m' A bs : bytes_at asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma wr_at_agree m m' A n : wr_at asegs m A n -> agree_on m m' A n -> wr_at asegs m' A n.
Proof.
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree m m' A cs : rw_cells asegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_agree; eauto.
Qed.

Lemma u64arr_agree m m' A ws : u64arr asegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros [HB HW] AG. split.
  - eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply wr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma u8arr_agree m m' A bs : u8arr asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
Proof. intros [HB HW] AG. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.

Lemma agree_on_sub m m' A n A' n' : agree_on m m' A n -> A <= A' -> A' + n' <= A + n -> agree_on m m' A' n'.
Proof. intros AG H1 H2 a Ha. apply AG. lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

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
(* [comment removed for export] *)
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma nr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
(* [comment removed for export] *)
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
(* [comment removed for export] *)

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
(* [comment removed for export] *)

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
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
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
End CEIL_WRAP_1.

(* [comment removed for export] *)
