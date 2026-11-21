(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_enframe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2.MallocKit_AB OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.Malloc_fp OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_AS.MallocNat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_AS OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.Malloc_fp.ASlot_W1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_I OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0.ASlot_W3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0.ASlot_W5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0.ASlot_W6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B.F_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_mm_syscalls.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.

Module RMallocKit_A2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_malloc_free MallocTree MallocKit_A.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2.MallocKit_AB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Export MallocKit_A2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require KStepLite.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B RMallocKit_B2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMalloc_fp.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : rctx_head_cells st' = rctx_head_cells st).
  { unfold rctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
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
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

Lemma rbytes_at_agree m m' A bs : bytes_at psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at psegs m' A bs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rwr_at_agree m m' A n : wr_at psegs m A n -> agree_on m m' A n -> wr_at psegs m' A n.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree m m' A cs : rw_cells psegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells psegs m' A cs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree m m' A ws : u64arr psegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr psegs m' A ws.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree m m' A bs : u8arr psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr psegs m' A bs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Lemma rmrep_agree : forall st m m',
  rmrep st m ->
  agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x418 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep st m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
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
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.
Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). rewrite rnr_regions. apply lookup_insert_eq. Qed.
Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rnr_lookup_new in H. inversion H. auto.
  - right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.
Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold lr_lo, r0. cbn. destruct k; lia. Qed.

Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma rnr_regions_wf : rregions_wf st'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RFimg : ranges_free ref_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
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
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in XC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (MR1 : rmrep st m').
  { eapply rmrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold RMLOCK in *; lia.
    - intros a Ha. apply AG; unfold RLIBC in *; lia.
    - intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
      unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. apply AG; lia.
    - intros b gh Hb a0 Ha0.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
      pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. apply AG; lia.
    - intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in BC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
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
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. exact H. Qed.

Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. exact H. Qed.
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
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.
Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma rmrep_drop_region : rmrep st' m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
  destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in BC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
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
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x28000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x28000 \/ 0x5b000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
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
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x28000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x28000 \/ 0x5b000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
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
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
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
    pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
    right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
  - intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
    eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
    destruct (WR q rq H) as (Bq & _ & _ & BCq & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in BCq; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
    assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
    destruct (SH q rq H Hk) as [HWr HB]. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
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
  rw_cells psegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
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
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write psegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl psegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write psegs m RCTX (rctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
    unfold rctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
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
End WithCeiling0.
End RMallocKit_A2.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.

Module RASlot_I.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_I.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.Malloc_fp OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_AS.MallocNat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_AS OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.Malloc_fp.ASlot_W1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_I.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RMallocRep RMallocTree.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMalloc_fp OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RAllocSlot_iface.
Import ListNotations.
Local Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (@ISTF_g ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rimplT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
  eapply rimplT_bind; [eapply rimplT_reach; exact H|].
  intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv2 st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom psegs)).

Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. exact H. Qed.

Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot R' full_lay fuel st sc req k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
                             | None => False end)).
  - apply alloc_slot_nat.
  - eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
  - intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
  - intros s' ms' [].
Qed.

Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m ->
  tp = Z_to_bv 64 0x3a490 ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta R' st k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
                             | None => False end)).
  - apply alloc_meta_nat.
  - eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
  - intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
  - intros s' ms' [].
Qed.
End WithCeiling0.
End RASlot_I.


Module RMallocKit_A3.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2 MallocKit_A3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2.MallocKit_AB OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RMallocKit_A2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMalloc_fp.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmrep_set_bounce : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write psegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl psegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
    apply (u8arr_write psegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.

End WithCeiling0.
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame psegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write psegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write psegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv psegs mX |- _ =>
      apply (mem_inv_store psegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Ltac rraw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write psegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv psegs mX |- _ =>
      apply (mem_inv_store psegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

End WithCeiling1.
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | first [ cbn [cells_wf cell_wf meta_cells ctx_head_cells ctx_tail_cells rctx_head_cells]; solve [repeat split] | cbn; tauto ]]);
    clear MUq WMq CH end.

Ltac rmchunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Section WithCeiling2. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some gh ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono psegs m m' ->
  rw_cells psegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
  pose proof (rmrep_del_group st m b MR) as MR1.
  assert (MR2 : rmrep (del_group b st) m').
  { eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
    intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
    pose proof (round_up_pg_ge (r_len r)).
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
      destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
      rewrite lookup_delete_ne in Hb2 by congruence.
      destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
      destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
      + rewrite E, Hr in Hr2. inversion Hr2; subst r2.
        assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
        assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
      + destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
    - change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
      destruct (N.eq_dec q (fst b)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
        rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold RGOT_SSP in R8. lia.
    - unfold RSSP_GUARD in R9. lia. }
  rewrite <- put_group_del.
  eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
  unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

Lemma rmrep_set_group_ai : forall st m m' b g ai0 ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono psegs m m' ->
  rw_cells psegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (set_group_active_idx b ai st) m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
  eapply rmrep_regroup; eauto.
Qed.

Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
  ov_read_bytes psegs m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m (_ & (HD & _) & _) CR.
  destruct HD as [[_ HB] _]. unfold rctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
  rewrite (bytes_at_read psegs m RCTX _ 12 1 HB).
  all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
  change (Z.to_nat 12) with 12%nat.
  unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
  rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End WithCeiling2.
End RMallocKit_A3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_get_meta OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_mm_syscalls OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RMallocKit_A2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMalloc_fp OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RF_enframe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RF_malloc_entry OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RAllocSlot_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RASlot_I OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RMallocKit_A3.

Module RASlot_W2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_malloc_enframe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2.MallocKit_AB OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_A3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.Malloc_fp OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_AS.MallocNat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_AS OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.Malloc_fp.ASlot_W1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_I OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0.ASlot_W3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0.ASlot_W5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.ASlot_W0.ASlot_W6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B.F_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_mm_syscalls.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require RF_malloc_small.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_get_meta OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RMallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_mm_syscalls OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RMallocKit_A2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RMalloc_fp OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RF_enframe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RF_malloc_entry OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_ntf_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RF_malloc_small.RAllocSlot_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RASlot_I OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RMallocKit_A3.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 junk; C8 rr_guard; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk psegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono psegs m0 m ->
  evt psegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom psegs)
      /\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp) /\ rmrep st' m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21cf0) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros MR' MI FR ST LO LOLE MU WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold RSSP_GUARD, rta_frame, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl psegs m) as WMs.
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

Lemma rfin_walk :
  forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
  bv_unsigned gw = G ->
  rw_cells psegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk psegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists (a1' a2' a3' : word) m' k,
      0 <= k < 32 /\ lowbit mask = 2 ^ k /\
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom psegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21630) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros HG FR ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
  unfold meta_cells in CH. rewrite <- HG in CH.
  destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
  assert (P2 : 0 < 2 ^ k <= mask).
  { destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  unfold rta_frame, RSSP_GUARD, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl psegs m) as WMg.
  step.
  lazymatch goal with H : rw_cells psegs ?mc (bv_unsigned gw) ?cs |- _ =>
    apply (rw_cells_congr psegs mc (bv_unsigned gw) cs
             (meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
    [| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
     | reflexivity | cbn; tauto ];
    rewrite HG in H;
    pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
  end.
  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. step. step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv psegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
  step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.
  step.
  rewrite ?LB in MR1.
  eapply evt_mono.
  { eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
      [exact MR1 | assumption | exact FR | exact ST | unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia | lia | exact MU | exact WM]. }
  cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
  do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.
End WithCeiling0.
End RASlot_W2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP.RASlot_W4.RASlot_W2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section ENTRY.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

Lemma ras_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  a0 = Z_to_bv 64 sc ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists (a1' : word) m' junk,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 rr_guard a1' (pw st (active st sc)) a3 a4 a5 a6 a7
                   a1 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (match active st sc with None => 0x21670 | Some _ => 0x214f4 end)) fc None m' (seg_rom psegs)
      /\ rw_cells psegs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk psegs m' lo (bv_unsigned sp + -144)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rmrep st m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until fc. intros HA ST LO MI. subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _). unfold wz in G4.
  unfold ralloc_slot_entry, RCTX, RMLOCK, RGOT_SSP, RSSP_GUARD, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step.
  rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  pose proof (rmrep_active_read st _ sc (wa (370576 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
  step. clear RDA.
  step.
  replace (370568 + sc * 8 + 88) with (370576 + 80 + 8 * sc) by lia.
  replace (370568 + sc * 8) with (370568 + 8 * sc) by lia.
  lazymatch goal with H : rw_cells psegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  step. if_cases K; zify_cond K.
  - destruct (active st sc) as [g|] eqn:HA.
    { exfalso. pose proof (rmeta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _).
      unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
  - destruct (active st sc) as [g|] eqn:HA.
    2:{ exfalso. apply K. reflexivity. }
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End ENTRY.

Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
      (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.

Lemma rt1_fin_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr <> 0 -> mem_inv psegs m ->
  evt psegs (fun ms' =>
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) (wz (sxv (m_avail mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x21630) fc None m (seg_rom psegs))
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x214f4) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until fc. intros AVNZ MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
  pose proof (sxv_range (m_avail mr)) as RA.
  step. rewrite sx32_wz_sxv by lia.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
  { exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
  step. step.
  apply evt_done. reflexivity.
Qed.

Lemma rt1_deq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr = 0 -> mem_inv psegs m ->
  evt psegs (fun ms' =>
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz 0) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x21518) fc None m (seg_rom psegs))
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x214f4) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. unfold pw, wz. reflexivity.
Qed.

Lemma rt1_next_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr <> 0 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists m',
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz (sxv (m_freed mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x21558) fc None m' (seg_rom psegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rmrep (set_active sc (m_next mr) st) m')
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x214f4) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
  pose proof (sxv_range (m_freed mr)) as RF.
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. step.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
  { exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.
  clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok psegs _ _ (actives st) sc (Z_to_bv 64 (370576 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (370576 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.
  step.
  apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End T1.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

Lemma rdeq_self_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_next mr = Some g -> mem_inv psegs m ->
  evt psegs (fun ms' => exists m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (wz 0) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x21670) fc None m' (seg_rom psegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rmrep (put_meta g (clr mr) (set_active sc None st)) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21518) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok psegs _ _ (actives st) sc (Z_to_bv 64 (370576 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish0 (370576 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
  set (st1 := set_active sc None st) in MR1.
  assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).
  rmeta_open G MUg WMg.
  rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
  st1. st1.
  rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.
  pose proof (rmrep_active_read _ _ sc (wa (370576 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. unfold wz.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

Lemma rdeq_other_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nx pv : aptr),
  m_next mr = Some nx -> m_prev mr = Some pv -> nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  mem_inv psegs m ->
  let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
  let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
  let st3 := set_active sc (Some nx) st2 in
  let st4 := put_meta g (clr mr) st3 in
  evt psegs (fun ms' => exists (a1' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st nx)) a1' (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x21558) fc None m' (seg_rom psegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m m'
      /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rmrep st4 m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21518) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _).
  pose proof (rmeta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _).
  assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  step. clear CH.
  rmeta_open (conc st pv) MUp WMp.
  rmchunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. step. clear CH.
  rmeta_open (conc st nx) MUn WMn.
  rmchunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  pose proof (rmrep_active_read st2 _ sc (wa (370576 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.
  step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
  unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. clear CH. step.
  pose proof MR2 as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok psegs _ _ (actives st2) sc (wa (370576 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
  rraw_store_finish0 (370576 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
  fold st3 in MR3.
  assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).
  rmeta_open G MUg WMg.
  rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
  replace (get_meta_rec st3 g) with mr in CH.
  2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1.
  rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.
  pose proof (rmrep_active_read _ _ sc (wa (370576 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
  change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
End DEQ.

Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

Lemma rm_act_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  full_skip st g = false -> mem_inv psegs m ->
  evt psegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' (wz (sxv f)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x21584) fc None m (seg_rom psegs))
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21558) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until fc. intros NSK MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { apply evt_done. do 2 eexists. reflexivity. }
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  { apply evt_done. do 2 eexists. reflexivity. }
  exfalso. unfold full_skip in NSK. fold mr f in NSK.
  assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
  rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.

Lemma rm_skip_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mn : aptr),
  full_skip st g = true -> m_next mr = Some mn -> meta_slot st mn ->
  0 <= m_freed (get_meta_rec st mn) < 2^32 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' (wz (sxv (m_freed (get_meta_rec st mn)))) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x21584) fc None m' (seg_rom psegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rmrep (set_active sc (Some mn) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21558) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until mn. intros FSK GN MSn FNR MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
  apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.
  step. clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok psegs _ _ (actives st) sc (Z_to_bv 64 (370576 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (370576 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
  rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
  step. rewrite sx32_wz_sxv by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End M.
End WithCeiling0.
