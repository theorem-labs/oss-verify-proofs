(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocKit_A MallocKit_AB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocKit_A2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require KArith. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMalloc_fp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMallocKit_A2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.agree_on"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RLIBC"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RGOT_SSP"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "Corelib.Init.Logic.eq"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.land"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.put_group"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_mmap_counter"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

#[using="Hconc"] Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

#[using="Hmetas"] Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

#[using="P HP Hconc"] Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
  ddestruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). ddestruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

#[using="P HP Hconc Hctx"] Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
  intros H. ddestruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : ctx_head_cells st' = ctx_head_cells st).
  { unfold ctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
  { unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
    rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

#[using="P HP Hconc Hmetas"] Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
  (intros Ha dd_H; ddestruct dd_H as (A1 & A2 & A3)). ddestruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

#[using="P HP Hconc"] Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
  (intros Hb dd_H; ddestruct dd_H as (w8 & R & Hw8)). ddestruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

#[using="Type"] Lemma rbytes_at_agree m m' A bs : bytes_at rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
  (intros dd_H; ddestruct dd_H as (H0 & H1 & HB); intros AG). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

#[using="Type"] Lemma rwr_at_agree m m' A n : wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof.
  (intros dd_H; ddestruct dd_H as (H0 & H1 & HW); intros AG). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree m m' A cs : rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree m m' A ws : u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree m m' A bs : u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A2 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))P,(3.VhRP,R3.R2.)P,(4.R3.R2.$5.+4.)P,(4.R4.R3.$6.+418.)P,(4.R5.R4.$7.+8.)P,(4.R6.R5.$8.+8.)P,Pa,$9.Par,$:.P,(;.(2.$:.)(<.$9.$:.(=.$9.(>.$?.$10.$11.$12.)(13.$?.$10.$14.$11.$12.$15.)$:.)(16.$9.(>.$?.$10.$11.$12.)(13.$?.$10.$14.$11.$12.$15.)$:.)R2.(17.R:.))(18.$:.R1.))(4.R:.R9.(19.R;.R3.)+1000.)P,Pb,$9.Pgh,$1:.P,(;.(2.$1:.)(<.$9.$1:.(=.$9.(>.$?.$10.$11.$12.)(13.$?.$10.$14.$11.$12.$15.)$1:.)(16.$9.(>.$?.$10.$11.$12.)(13.$?.$10.$14.$11.$12.$15.)$1:.)R2.(1;.R;.))(18.$1:.R1.))(4.R;.R:.(19.R<.R3.)+9.)P,Prid,$?.Pr,$1<.P,(;.(2.$1<.)(<.$?.$1<.(=.$?.$10.$14.$1<.)(16.$?.$10.$14.$1<.)R2.(1=.R<.))(18.$1<.R1.))P,(;.$1>.(1?.R2.)$20.)(4.R=.R<.(21.R3.)(22.(23.R3.)))(3.VhRP,R;.R9.)")
(* [comment removed for export] *).
Proof.
  (intros st m m' dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros AGL AGC AGS1 AGS2 AGA AGG AGR).
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - ddestruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. ddestruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= rceil.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite rnr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rnr_lookup_new in H. inversion H. auto.
  - right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
#[using="r0"] Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="st m' rid L ZF"] Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

(* [comment removed for export] *)
#[using="rid RF"] Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="m m' rid L r0 MR PT X0 XA LEN XC RF ZF"] Lemma rnr_regions_wf : rregions_wf st'.
Proof.
  pose proof MR as (WF & _). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  assert (RFimg : ranges_free ref_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  split; [exact (conj RS RPRS)|]. split; [|split; [|split]].
  - intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
    + exact (WR q r H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. ddestruct (WA a ar Ha) as (r & Hr & REST).
    ddestruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
    exists r. rewrite rnr_lookup_old by exact Pa. auto.
  - intros b gh Hb. ddestruct (WG b gh Hb) as (r & Hr & REST).
    ddestruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
    exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

#[using="m rid L r0 MR PT FRs X0 XA LEN XC RF AG ZF"] Lemma rmrep_new_region : rmrep st' m'.
Proof.
  dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. rceilb.
  (* [comment removed for export] *)
  assert (MR1 : rmrep st m').
  { eapply rmrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold RMLOCK in *; lia.
    - intros a Ha. apply AG; unfold RLIBC in *; lia.
    - intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
      rceilb. apply AG; lia.
    - intros b gh Hb a0 Ha0.
      ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
      pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). rceilb. apply AG; lia.
    - intros q r Hq Hk a0 Ha0. ddestruct (WR q r Hq) as (B0 & _ & _ & BC & _). rceilb.
      pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
  dpose MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
  assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
  split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
  - eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
  - intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
  - intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
  - intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
      * intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
        rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
        unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
    + eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.


End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A2 ()) "Pa,$11.P,(24.(25.=R1.)(26.R1.(27.+2.+40.)))P,(28.(26.R2.(29.Vr,))(25.(2:.(21.Vr,)(22.(23.Vr,)))R2.))P,(28.(24.(25.$5.R3.)(26.R3.(2:.$5.+4.)))(28.(24.(25.$6.R3.)(26.R3.(2:.$6.+418.)))(28.(24.(25.$7.R3.)(26.R3.(2:.$7.+8.)))(28.(24.(25.$8.R3.)(26.R3.(2:.$8.+8.)))(2;.$?.Lq,$?.(2;.$1<.Lrq,$1<.(24.(;.(2.$1<.)(<.$?.$1<.(=.$?.$10.$14.$1<.)(16.$?.$10.$14.$1<.)R2.(1=.Vst,))(18.$1<.R1.))(24.(25.(29.R1.)R5.)(26.R5.(2:.(21.R1.)(22.(23.R1.))))))))))))(;.(2.(1.&8.))A1.Vm',(2<.R4.)A1.Vm,(2<.R4.))")
(* [comment removed for export] *).

#[using="Type"] Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
  intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
#[using="Type"] Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

#[using="m r MR Hr PT AG"] Lemma rmrep_drop_region : rmrep st' m'.
Proof.
  dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
  ddestruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). rceilb.
  assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
            r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
    by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *)
    split; [exact (conj RS RPRS)|]. split; [|split; [|split]].
    + intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
    + intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
    + intros a ar Ha. ddestruct (WA a ar Ha) as (ra & Hra & REST).
      ddestruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
      exists ra. rewrite rdr_lookup_old by exact Pa. auto.
    + intros b gh Hb. ddestruct (WG b gh Hb) as (rb & Hrb & REST).
      ddestruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
      exists rb. rewrite rdr_lookup_old by exact Pb. auto.
  - (* [comment removed for export] *)
    eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
    ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x48000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x48000 \/ 0x7e000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
    assert (AGC : agree_on m m' RLIBC 0x418).
    { intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - ddestruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x48000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x48000 \/ 0x7e000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
    unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
    + eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
    + eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
  - intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
    eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
    ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). rceilb.
    assert (NE : fst a <> rid) by (ddestruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
    pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
    assert (AGA : agree_on m m' (conc st a) 4096).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. dexists (fst a), ra. split; [exact Hra|]. lia. }
    ddestruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
    + intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
  - intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
    eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    assert (NE : fst b <> rid) by (ddestruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
    pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). rceilb.
    ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
    right; right; right; right. dexists (fst b), rb. split; [exact Hrb|]. lia.
  - intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
    eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
    ddestruct (WR q rq H) as (Bq & _ & _ & BCq & _). rceilb.
    pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
    assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. dexists q, rq. split; [exact H|]. lia. }
    destruct (SH q rq H Hk) as [HWr HB]. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

#[using="Type"] Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
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
#[using="Type"] Lemma rmrep_put_group_new : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A2 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pb,(2=.$?.$11.)Pg,$9.Pai,$11.Pr,$1<.Pw8,(1.&8.)P,(3.VhRP,R7.R6.)P,(;.(2.$1:.)(<.(2=.$?.$11.)$1:.(=.$9.(>.$?.$10.$11.$12.)(13.$?.$10.$14.$11.$12.$15.)$1:.)(16.$9.(>.$?.$10.$11.$12.)(13.$?.$10.$14.$11.$12.$15.)$1:.)R6.(1;.R8.))(2>.$1:.))P,(;.(2.$1<.)(<.$?.$1<.(=.$?.$10.$14.$1<.)(16.$?.$10.$14.$1<.)(2?.$?.$11.R7.)(1=.R9.))(18.$1<.R4.))P,(;.$1>.(1?.R5.)$20.)P,(25.=(30.$?.$11.R9.))P,(25.(2:.(30.$?.$11.R:.)+10.)(22.(23.R7.)))P,(;.$11.(31.(30.$?.$11.R;.)+10.)=)P,(32.$33.R=.(19.R>.R<.)(34.$35.(36.(37.R>.(18.$9.R;.)))(34.$35.(38.R8.)(39.$35.))))P,(;.$11.(3:.(3;.&8.R9.)+1?.)(3:.R;.+1?.))(3.VhRP,(3<.R>.(18.$9.R=.)R<.R10.)R?.)")
(* [comment removed for export] *).
Proof.
  (intros st m b g ai r w8 dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros Hb Hr Hk B0 B16 BA R Hw8).
  dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
  - split; [exact (conj RS RPRS)|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
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
(* [comment removed for export] *)

#[using="Type"] Lemma rmrep_set_mmap_counter : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A2 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pv,$11.P,(3.VhRP,R3.R2.)P,(24.(25.=R2.)(26.R2.(27.+2.+20.)))(3.VhRP,(3=.(3>.R3.)R5.)(3?.R4.(2<.(2:.$40.+<.))(41.(42.R3.))))")
(* [comment removed for export] *).
Proof.
  intros st m v MR Hv. dpose MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write rsegs m RCTX (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
    unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.


End RP_1.
