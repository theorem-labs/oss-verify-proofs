(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM22.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W9.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM06.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM21.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RF_malloc_enf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RMallocKit_A2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14. Import MM14. Export MM14.MallocKit_A2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM22.RMalloc_fp.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
  intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : rctx_head_cells st' = rctx_head_cells st).
  { unfold rctx_head_cells, rsecw. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
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

Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
  intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
  intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

Lemma rbytes_at_agree m m' A bs : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m' A bs.
Proof.
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rwr_at_agree m m' A n : wr_at (run_segments psegs rc_inp rc_sp rc_mb) m A n -> agree_on m m' A n -> wr_at (run_segments psegs rc_inp rc_sp rc_mb) m' A n.
Proof.
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree m m' A cs : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' A cs.
Proof.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree m m' A ws : u64arr (run_segments psegs rc_inp rc_sp rc_mb) m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr (run_segments psegs rc_inp rc_sp rc_mb) m' A ws.
Proof.
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree m m' A bs : u8arr (run_segments psegs rc_inp rc_sp rc_mb) m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr (run_segments psegs rc_inp rc_sp rc_mb) m' A bs.
Proof. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Lemma rmrep_agree : forall st m m',
  rmrep st m ->
  agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x418 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep st m'.
Proof.
  intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
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
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
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
Hypothesis XC : x + L <= ATOP.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite rnr_regions. apply lookup_insert_eq. Qed.
Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rnr_lookup_new in H. inversion H. auto.
  - right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma rnr_regions_wf : rregions_wf st'.
Proof.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RFimg : ranges_free ref_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS). exact HI. }
  split; [exact RS|]. split; [|split; [|split]].
  - intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
    + exact (WR q r H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
    exists r. rewrite rnr_lookup_old by exact Pa. auto.
  - intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
    exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

Lemma rmrep_new_region : rmrep st' m'.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS). exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. atop_facts.
  assert (MR1 : rmrep st m').
  { eapply rmrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold RMLOCK in *; lia.
    - intros a Ha. apply AG; unfold RLIBC in *; lia.
    - intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
      atop_facts. apply AG; lia.
    - intros b gh Hb a0 Ha0.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
      pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). atop_facts. apply AG; lia.
    - intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). atop_facts.
      pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
  pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
  assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
  split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
  - eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
  - intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
  - intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
  - intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    +
      cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
      * intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
        rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
        unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
    + eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x418 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
   \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).

Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
  intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma rmrep_drop_region : rmrep st' m'.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
  destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). atop_facts.
  assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
            r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
    by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
  split; [|split; [|split; [|split; [|split]]]].
  -
    split; [exact RS|]. split; [|split; [|split]].
    + intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
    + intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
    + intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
      exists ra. rewrite rdr_lookup_old by exact Pa. auto.
    + intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
      exists rb. rewrite rdr_lookup_old by exact Pb. auto.
  -
    eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x95000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
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
  - destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x95000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
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
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). atop_facts.
    assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
    pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
    assert (AGA : agree_on m m' (conc st a) 4096).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
    destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
    + intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
  - intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
    eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
    pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). atop_facts.
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
    right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
  - intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
    eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
    destruct (WR q rq H) as (Bq & _ & _ & BCq & _). atop_facts.
    pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
    assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
    destruct (SH q rq H Hk) as [HWr HB]. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
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

Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
  rmrep st m -> (s_groups st) !! b = None ->
  (s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m.
Proof.
  intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
  pose proof WF as (RS & WR & DJ & WA & WG).
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


Lemma rmrep_set_mmap_counter : forall st m v,
  rmrep st m -> 0 <= v < 2^32 ->
  rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write (run_segments psegs rc_inp rc_sp rc_mb) m RCTX (rctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
    unfold rctx_head_cells, rsecw, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
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

End CANSEC1.
End RMallocKit_A2.

Module RASlot_M0.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W9. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM06. Import MM06. Import MM06.ASlot_W18. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM01. Import MM01. Import MM01.ASlot_M0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rgmf_of_facts st LB sc g :
  RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
  intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
  pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
  pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  constructor.
  - exact MSL.
  - exact AVr.
  - exact FRr.
  - exact MW.
  - exact SC48.
  - exact GSC.
  - exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
    + intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
      change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
      exact (X Hmem Hgh S0).
    + intros o Ho. exact (GU b _ o Hgh Ho).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
  - destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
    exists n, p. split; reflexivity.
Qed.

Lemma rtaf_of_facts st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
  intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
  pose proof (lf_lists _ LF) as (L1 & L2 & L3).
  change (fact_active (strip st)) with (fact_active st).
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  pose proof (lf_links _ LF) as LK.
  constructor.
  - intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
    change (lmem (strip st) g) with (lmem st g) in LM.
    split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
  - intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
    change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
    split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
    split; [exact SCn|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
    exact (LKn n Hn).
  - intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
    change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
    split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
    exact (LKp p Hp).
  - pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
  0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= ATOP
  /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x14000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x14000 \/ 0x22000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x23000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x23000 \/ 0x95000 <= r_base r).
Proof.
  intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. atop_facts. lia.
Qed.

Lemma rmalloc_fp_cases_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < ATOP.
Proof.
  intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
  atop_facts.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). atop_facts. lia.
  - right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). atop_facts. lia.
  - right. atop_facts. lia.
Qed.

Lemma rmalloc_fp_image_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> ATOP <= lo ->
  0x10000 <= a < 0x95000 -> RCTX <= a < RCTX + 928 \/ 0x741cc <= a < 0x741d0.
Proof.
  intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
  atop_facts.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact (rstatics_reserved _ RS1))). lia.
Qed.

Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
  rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
  ATOP <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
  intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
    destruct AUX as (av & vs & r & rnd & _ & _ & _ & HH). atop_facts. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL in Ha.
    destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
  rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 A cs ->
  sp <= A -> ATOP <= A -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' A cs.
Proof.
  intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.
End CANSEC1.
End RASlot_M0.

Module RF_malloc_join.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08. Import MM08. Import MM08.F_malloc_enf. Import MM08.F_malloc_join.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocTree. Import PM22. Import PM22.RMallocKit_A. Import PM22.RMalloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RF_malloc_enf. Import PM02. Import PM02.RAllocSlot_iface.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
    rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1 ->
    stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp + -48) ->
    rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
    rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1b3bc) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rmrep st2 m1 -> ticks_ok st2 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1 -> stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp) ->
    rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).


Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
  lo <= a < sp \/ a < ATOP.
Proof.
  intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  atop_facts.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - right. atop_facts. lia.
Qed.

Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
  rmrep st m0 -> rmrep st2 m2 ->
  rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A cs ->
  sp' <= A -> ATOP <= A -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' A cs.
Proof.
  intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> ATOP <= lo ->
  0x22000 <= a < 0x95000 -> RCTX <= a < RCTX + 928 \/ 0x741cc <= a < 0x741d0.
Proof.
  intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  atop_facts.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  -
    exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) (rstatics_reserved _ RS)). lia.
Qed.

Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
  rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
  ATOP <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
  intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
    destruct AUX as (av & vs & r & rnd & _ & _ & _ & HH). atop_facts. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
    destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.
End CANSEC1.
End RF_malloc_join.
