(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
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

#[using="Hconc HP P"] Lemma meta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). (first [ pose proof ((H8 g)) as dR_1; dand3 dR_1 as X1 X2 X3 | destruct (H8 g) as (X1 & X2 & X3) ]).
  unfold meta_cells. rewrite !pw_extP by assumption. reflexivity.
Qed.

#[using="Hctx Hconc HP P"] Lemma mrep_ctx_extP m : mrep_ctx st m -> mrep_ctx st' m.
Proof.
  intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : ctx_head_cells st' = ctx_head_cells st).
  { unfold ctx_head_cells. rewrite Hctx. rewrite !pw_extP by assumption. reflexivity. }
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply pw_extP. apply (H6 (Z.of_nat a)). }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
  { unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
    rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
  unfold mrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

#[using="Hmetas Hconc HP P"] Lemma area_rep_extP m a ar : (s_areas st) !! a = Some ar -> area_rep st m a ar -> area_rep st' m a ar.
Proof.
  (intros Ha; (first [ intro dR_26; dand3 dR_26 as A1 A2 A3 | intros (A1 & A2 & A3) ])). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold area_rep. rewrite (Hconc a Pa). rewrite (pw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite get_meta_rec_extP, meta_cells_extP. apply A2. exact Hk.
Qed.

#[using="Hconc HP P"] Lemma group_rep_extP m b gh : (s_groups st) !! b = Some gh -> group_rep st m b gh -> group_rep st' m b gh.
Proof.
  (intros Hb; (first [ intro dR_27; dex1 dR_27 as w8; destruct dR_27 as [R Hw8] | intro dR_27; dand3 dR_27 as w8 R Hw8 | intros (w8 & R & Hw8) ])). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (pw_extP _ Pg). auto.
Qed.
Definition agree_on (m m' : mem) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).
End PEXT.

Lemma bytes_at_agree m m' A bs : bytes_at rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
  ((first [ intro dR_28; dand3 dR_28 as H0 H1 HB | intros (H0 & H1 & HB) ]); intros AG). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma wr_at_agree m m' A n : wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof.
  ((first [ intro dR_29; dand3 dR_29 as H0 H1 HW | intros (H0 & H1 & HW) ]); intros AG). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree m m' A cs : rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_agree; eauto.
Qed.

Lemma u64arr_agree m m' A ws : u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
  intros [HB HW] AG. split.
  - eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply wr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma u8arr_agree m m' A bs : u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. intros [HB HW] AG. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.
Lemma agree_on_sub m m' A n A' n' : agree_on m m' A n -> A <= A' -> A' + n' <= A + n -> agree_on m m' A' n'.
Proof. intros AG H1 H2 a Ha. apply AG. lia. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma mrep_agree : forall st m m',
  mrep st m ->
  agree_on m m' MLOCK 4 -> agree_on m m' LIBC 0x418 -> agree_on m m' GOT_SSP 8 -> agree_on m m' SSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  mrep st m'.
Proof.
  (intros st m m'; (first [ intro dR_30; dand6 dR_30 as WF CX GL AR GR SH | intros (WF & CX & GL & AR & GR & SH) ]); intros AGL AGC AGS1 AGS2 AGA AGG AGR).
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - (first [ dand6 CX as C1 C2 C3 C4 C5 C6 | destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]). unfold mrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    unfold LIBC, CTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - (first [ dand5 GL as G1 G2 G3 G4 G5 | destruct GL as (G1 & G2 & G3 & G4 & G5) ]). unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A, LIBC, GOT_SSP, SSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. (first [ pose proof ((AR a ar Ha)) as dR_4; dand3 dR_4 as A1 A2 A3 | destruct (AR a ar Ha) as (A1 & A2 & A3) ]). pose proof (AGA a ar Ha) as AG.
    split; [|split].
    + eapply rw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. eapply rw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
    + eapply rw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. (first [ pose proof ((GR b gh Hb)) as dR_5; dex1 dR_5 as w8; destruct dR_5 as [R Hw8] | pose proof ((GR b gh Hb)) as dR_5; dand3 dR_5 as w8 R Hw8 | destruct (GR b gh Hb) as (w8 & R & Hw8) ]). exists w8. split; [|exact Hw8].
    eapply rw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
    + eapply wr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply bytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

End CEIL.
Lemma mmap_len_round_up l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply KLink.round_up_pg_eq. Qed.
(* [comment removed for export] *)
Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read, shadow0. cbn. rewrite !lookup_empty. reflexivity. Qed.

Section NEWREGION.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : mrep st m.
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
#[using="r0"] Lemma nr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma nr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite nr_lookup_new in H. inversion H. auto.
  - right. rewrite nr_lookup_old in H by exact NE. auto.
Qed.
#[using="r0"] Lemma nr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.
(* [comment removed for export] *)
Lemma nr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="ZF L rid m' st"] Lemma nr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

(* [comment removed for export] *)
#[using="RF rid"] Lemma nr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="ZF RF XC LEN XA X0 PT MR r0 L rid m' m Rr"] Lemma nr_regions_wf : regions_wf st'.
Proof.
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_6; dand5 dR_6 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  assert (RFimg : ranges_free p0_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  split; [exact RS|]. split; [|split; [|split]].
  - intros q r Hq. destruct (nr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + unfold r0. cbn. fold L. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact RFimg.
    + exact (WR q r H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (nr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (nr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r0]. fold L. pose proof (nr_old_disjoint q2 r2 H2'). pose proof nr_lr_lo_new. lia.
    + cbn [r_base r_len r0]. fold L. pose proof (nr_old_disjoint q1 r1 H1'). pose proof nr_lr_lo_new. lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. (first [ pose proof ((WA a ar Ha)) as dR_7; dex1 dR_7 as r; destruct dR_7 as [Hr REST] | pose proof ((WA a ar Ha)) as dR_7; dand3 dR_7 as r Hr REST | destruct (WA a ar Ha) as (r & Hr & REST) ]).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
    exists r. rewrite nr_lookup_old by exact Pa. auto.
  - intros b gh Hb. (first [ pose proof ((WG b gh Hb)) as dR_8; dex1 dR_8 as r; destruct dR_8 as [Hr REST] | pose proof ((WG b gh Hb)) as dR_8; dand3 dR_8 as r Hr REST | destruct (WG b gh Hb) as (r & Hr & REST) ]).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
    exists r. rewrite nr_lookup_old by exact Pb. auto.
Qed.

#[using="ZF AG RF XC LEN XA X0 FRs PT MR r0 L rid m"] Lemma mrep_new_region : mrep st' m'.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). (first [ pose proof (WF) as dR_9; dand5 dR_9 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  assert (RI : forall b n, In (b, n) p0_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  (* [comment removed for export] *)
  assert (MR1 : mrep st m').
  { eapply mrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold MLOCK in *; lia.
    - intros a Ha. apply AG; unfold LIBC in *; lia.
    - intros a Ha. apply AG; unfold GOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold SSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      (first [ pose proof ((area_conc st a ar WF Ha)) as dR_10; dex1 dR_10 as ra; dand9 dR_10 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st a ar WF Ha)) as dR_10; dand10 dR_10 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]).
      pose proof (area_lr_lo st a ar ra WF Ha Hra). pose proof (nr_old_disjoint _ _ Hra).
      (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). apply AG; lia.
    - intros b gh Hb a0 Ha0.
      (first [ pose proof ((group_conc st b gh WF Hb)) as dR_11; dex1 dR_11 as rb; dand8 dR_11 as Hrb Cb Kb Sb0 Sb1 SbA RB0 RBC | pose proof ((group_conc st b gh WF Hb)) as dR_11; dand9 dR_11 as rb Hrb Cb Kb Sb0 Sb1 SbA RB0 RBC | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC) ]).
      pose proof (lr_lo_group rb Kb). pose proof (nr_old_disjoint _ _ Hrb). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). apply AG; lia.
    - intros q r Hq Hk a0 Ha0. (first [ pose proof ((WR q r Hq)) as dR_12; dand5 dR_12 as B0 _ _ BC _ | destruct (WR q r Hq) as (B0 & _ & _ & BC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      pose proof (lr_lo_group r Hk). pose proof (nr_old_disjoint _ _ Hq). apply AG; lia. }
  (first [ pose proof (MR1) as dR_13; dand6 dR_13 as _ CX1 GL1 AR1 GR1 SH1 | pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1) ]).
  assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply nr_conc; exact Hq).
  split; [exact nr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
  - eapply (mrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
  - intros a ar Ha. eapply (area_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
  - intros b gh Hb. eapply (group_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
  - intros q r Hq Hk. destruct (nr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      cbn [r_kind r0] in Hk. unfold shadow_rep. cbn [r_base r_len r0]. fold L.
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
      * intros o v Ho Hc. rewrite nr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
        rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
        unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
    + eapply shadow_rep_ext; [apply nr_shadow|]. exact (SH1 q r H Hk).
Qed.

(* [comment removed for export] *)

Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : mrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (MLOCK <= a < MLOCK + 4 \/ LIBC <= a < LIBC + 0x418 \/ GOT_SSP <= a < GOT_SSP + 8 \/ SSP_GUARD <= a < SSP_GUARD + 8
   \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
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

#[using="AG PT Hr MR r m"] Lemma mrep_drop_region : mrep st' m'.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). (first [ pose proof (WF) as dR_14; dand5 dR_14 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply dr_conc; exact Hq).
  (first [ pose proof ((WR rid r Hr)) as dR_15; dand5 dR_15 as B0 _ RL0 BC RFr | destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
            r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
    by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *)
    split; [exact RS|]. split; [|split; [|split]].
    + intros q rq Hq. destruct (dr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
    + intros q1 r1 q2 r2 H1 H2 NE. destruct (dr_lookup_inv _ _ H1) as [_ H1']. destruct (dr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
    + intros a ar Ha. (first [ pose proof ((WA a ar Ha)) as dR_16; dex1 dR_16 as ra; destruct dR_16 as [Hra REST] | pose proof ((WA a ar Ha)) as dR_16; dand3 dR_16 as ra Hra REST | destruct (WA a ar Ha) as (ra & Hra & REST) ]).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
      exists ra. rewrite dr_lookup_old by exact Pa. auto.
    + intros b gh Hb. (first [ pose proof ((WG b gh Hb)) as dR_17; dex1 dR_17 as rb; destruct dR_17 as [Hrb REST] | pose proof ((WG b gh Hb)) as dR_17; dand3 dR_17 as rb Hrb REST | destruct (WG b gh Hb) as (rb & Hrb & REST) ]).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
      exists rb. rewrite dr_lookup_old by exact Pb. auto.
  - (* [comment removed for export] *)
    eapply (mrep_ctx_extP st st' _ PT Hconc eq_refl).
    (first [ dand6 CX as C1 C2 C3 C4 C5 C6 | destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]). unfold mrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x30000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x30000 \/ 0x64000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
    assert (AGC : agree_on m m' LIBC 0x418).
    { intros a Ha. unfold LIBC in Ha. apply AG; [lia| lia| right; left; unfold LIBC; lia]. }
    unfold LIBC, CTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply u8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - (first [ dand5 GL as G1 G2 G3 G4 G5 | destruct GL as (G1 & G2 & G3 & G4 & G5) ]). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x30000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x30000 \/ 0x64000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
    unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A, LIBC, GOT_SSP, SSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
    + eapply rw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
    + eapply rw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
  - intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
    eapply (area_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
    (first [ pose proof ((area_conc st a ar WF Ha)) as dR_20; dex1 dR_20 as ra; dand9 dR_20 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st a ar WF Ha)) as dR_20; dand10 dR_20 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]).
    pose proof (area_lr_lo st a ar ra WF Ha Hra). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
    pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
    assert (AGA : agree_on m m' (conc st a) 4096).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
    (first [ pose proof ((AR a ar Ha)) as dR_21; dand3 dR_21 as A1 A2 A3 | destruct (AR a ar Ha) as (A1 & A2 & A3) ]). split; [|split].
    + eapply rw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
    + intros k0 Hk0. eapply rw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
    + eapply rw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
  - intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
    eapply (group_rep_extP st st' _ PT Hconc); [exact Hb|].
    (first [ pose proof ((group_conc st b gh WF Hb)) as dR_22; dex1 dR_22 as rb; dand8 dR_22 as Hrb Cb Kb Sb0 Sb1 SbA RB0 RBC | pose proof ((group_conc st b gh WF Hb)) as dR_22; dand9 dR_22 as rb Hrb Cb Kb Sb0 Sb1 SbA RB0 RBC | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC) ]).
    assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
    pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    (first [ pose proof ((GR b gh Hb)) as dR_23; dex1 dR_23 as w8; destruct dR_23 as [R Hw8] | pose proof ((GR b gh Hb)) as dR_23; dand3 dR_23 as w8 R Hw8 | destruct (GR b gh Hb) as (w8 & R & Hw8) ]). exists w8. split; [|exact Hw8].
    eapply rw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
    right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
  - intros q rq Hq Hk. destruct (dr_lookup_inv q rq Hq) as [NE H].
    eapply shadow_rep_ext; [apply dr_shadow; exact NE|].
    (first [ pose proof ((WR q rq H)) as dR_24; dand5 dR_24 as Bq _ _ BCq _ | destruct (WR q rq H) as (Bq & _ & _ & BCq & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
    assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
    destruct (SH q rq H Hk) as [HWr HB]. split.
    + eapply wr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply bytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

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
Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma mrep_put_group_new : forall st m b g ai r (w8 : byte),
  mrep st m -> (s_groups st) !! b = None ->
  (s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
  rw_cells rsegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
  mrep (put_group b (Some g) ai st) m.
Proof.
  (intros st m b g ai r w8; (first [ intro dR_31; dand6 dR_31 as WF CX GL AR GR SH | intros (WF & CX & GL & AR & GR & SH) ]); intros Hb Hr Hk B0 B16 BA R Hw8).
  (first [ pose proof (WF) as dR_25; dand5 dR_25 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
  - split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
    + rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
  - intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
    + rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.
(* [comment removed for export] *)
Lemma ptrs_in_upd_ctx_scalar P st f :
  (forall c, c_free_meta_head (f c) = c_free_meta_head c) -> (forall c, c_avail_meta (f c) = c_avail_meta c) ->
  (forall c, c_meta_area_head (f c) = c_meta_area_head c) -> (forall c, c_meta_area_tail (f c) = c_meta_area_tail c) ->
  (forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) -> (forall c, c_active (f c) = c_active c) ->
  (forall c, c_brk (f c) = c_brk c) ->
  ptrs_in P st -> ptrs_in P (upd_ctx f st).
Proof.
  (intros E1 E2 E3 E4 E5 E6 E7; (first [ intro dR_32; dand10 dR_32 as H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) ])).
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
  (intros Q1 Q2 Q3; (first [ intro dR_33; dand10 dR_33 as H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) ])).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx put_meta set_metas s_metas s_areas s_groups] in *.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [|auto]. intros g'. unfold get_meta_rec. cbn [s_metas put_meta set_metas].
  destruct (decide (g' = g)) as [->|NE].
  - rewrite lookup_insert_eq. cbn. auto.
  - rewrite lookup_insert_ne by congruence. apply H8.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mrep_set_mmap_counter : forall st m v,
  mrep st m -> 0 <= v < 2^32 ->
  mrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (CTX + 12)) (le4 (wz v))).
Proof.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(CTX + 12, CTX + 16)] m m (CTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold CTX; lia) ltac:(rewrite L4; unfold CTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (CTX + 12)) (le4 (wz v)) (wmono_refl rsegs m)) as WM.
  eapply (mrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold CTX. lia.
  - left.
    pose proof (rw_cells_write rsegs m CTX (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (CTX + Z.of_nat 12) with (CTX + 12) in W by reflexivity.
    unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
    unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
    unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
    unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
    unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.

End CEIL2.

