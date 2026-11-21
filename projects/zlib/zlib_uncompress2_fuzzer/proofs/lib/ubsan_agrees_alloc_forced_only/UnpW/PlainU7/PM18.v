(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require RunHit.  (* a worker (A1) miss kit *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require PM22.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require PM03.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require PM17.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RF_am_K2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. Import MM07.F_am_K. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02. Import MM02. Import MM02.F_am_K2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM03. Import PM03.RMallocKit_A2. Import PM17. Import PM17.RF_am_K.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Lemma rmrep_agree_but_ctx : forall st st' m m',
  rmrep st m ->
  s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_statics st' = s_statics st ->
  A2.agree_on m m' RMLOCK 4 -> A2.agree_on m m' RLIBC 0x68 -> A2.agree_on m m' RGOT_SSP 8 -> A2.agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> A2.agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> A2.agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> A2.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep_ctx st' m' ->
  rmrep st' m'.
Proof.
  intros st st' m m' (WF & CX & GL & AR & GR & SH) ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGA AGG AGR CX'.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - exact (rregions_wf_restatics _ _ ER EA EG ERs WF).
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
    unfold rarea_rep. rewrite !Hconc.
    assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
    assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
    rewrite PW. split; [|split].
    + eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
    + eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
    unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
    + eapply RA2.rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctx_mid_agree : forall st st' m m',
  rmrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
                               /\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
  s_regions st' = s_regions st ->
  A2.agree_on m m' (RCTX + 80) 832 ->
  u64arr (run_segments psegs rc_inp rc_sp rc_mb) m' (RCTX + 80) (actives st') /\ u64arr (run_segments psegs rc_inp rc_sp rc_mb) m' (RCTX + 464) (usages st')
  /\ u8arr (run_segments psegs rc_inp rc_sp rc_mb) m' (RCTX + 848) (unmap_seqs st') /\ u8arr (run_segments psegs rc_inp rc_sp rc_mb) m' (RCTX + 880) (bouncess st').
Proof.
  intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _) HX ER AG.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
  assert (E3 : usages st' = usages st).
  { unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st).
  { unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
  assert (E5 : bouncess st' = bouncess st).
  { unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
  rewrite E2, E3, E4, E5.
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold RCTX in *.
  split; [|split; [|split]].
  - eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rarea_in_live : forall st a ar r x, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
  intros st a ar r x WF Ha Hr Hx. destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
  rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
  pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.

Lemma rgroup_in_live : forall st b gh r x, rregions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
  conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
  intros st b gh r x WF Hb Hr Hx. destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
  rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

(* [comment removed for export] *)
Lemma rimage_clear_of_ranges_free st lo n x : s_reserved st = ref_reserved -> ranges_free (live_ranges st) lo n = true ->
  0x10000 <= x < 0x95000 -> ~ (lo <= x < lo + n).
Proof.
  intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= ATOP.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
Lemma rgr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
  rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
  - rewrite lookup_insert_eq in H. left. split; congruence.
  - rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma rgr_conc q : conc st' q = conc st q.
Proof.
  unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
  - rewrite E, rgr_lookup_new, Hr. reflexivity.
  - rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

Lemma rgr_regions_wf : rregions_wf st'.
Proof.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
    cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
    apply ranges_free_intro. intros b n HI.
    pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
    assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite (rstatics_reserved _ RS); exact HI)).
    (* a worker (B1): ref_reserved = the image's entries ++ the vDSO pair's (each of positive length) *)
    unfold ref_reserved in HI. apply in_app_or in HI. destruct HI as [HI|HI].
    + destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
    + pose proof (RunHit.vdso_resvZ_pos _ _ _ _ _ HI). lia.
  - intros q1 r1 q2 r2 H1 H2 NE.
    assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
              r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
    { intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
      replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
      - left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
        pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
        destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
      - right. exact D. }
    destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + exact (OLD q2 r2 H2' NE2).
    + destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
    destruct (decide (fst a = rid)) as [E|NE].
    + exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
      cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      rewrite LEN in A1. repeat split; try assumption; lia.
    + exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
  - intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
    assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
    exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.

Lemma rmrep_grow_region : rmrep st' m.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
  assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
  split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    replace (rctx_head_cells st') with (rctx_head_cells st) by (unfold rctx_head_cells, rsecw; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
    replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
    replace (ctx_tail_cells st') with (ctx_tail_cells st).
    2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
  - intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
    unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
    split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
  - intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
    exists w8. rewrite rgr_conc, PW. split; assumption.
  - intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
    destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + exfalso. apply NK. exact Hk.
    + exact (SH q rq H Hk).
Qed.

Lemma rptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
  impl (run_segments psegs rc_inp rc_sp rc_mb) (at_node (run_segments psegs rc_inp rc_sp rc_mb)) (enode n dec) (epost P) ms ->
  (forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
  impl (run_segments psegs rc_inp rc_sp rc_mb) (at_node (run_segments psegs rc_inp rc_sp rc_mb)) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
  intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec' rsp) as [a|] eqn:E.
  - destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
  - cbn. apply evt_done. exact I.
Qed.

End CANSEC1.
End RF_am_K2.

Module RMallocKit_A3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM22. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Lemma rmrep_set_bounce : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof.
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
    apply (u8arr_write (run_segments psegs rc_inp rc_sp rc_mb) m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX |- _ =>
      apply (mem_inv_store (run_segments psegs rc_inp rc_sp rc_mb) mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
Ltac rraw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX |- _ =>
      apply (mem_inv_store (run_segments psegs rc_inp rc_sp rc_mb) mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof.
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

End CANSEC2.
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; ftauto]);
    clear MUq WMq CH end.

(* [comment removed for export] *)
Ltac rmchunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Section CANSEC3.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some gh ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m'.
Proof.
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
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (set_group_active_idx b ai st) m'.
Proof.
  intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
  eapply rmrep_regroup; eauto.
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
  ov_read_bytes (run_segments psegs rc_inp rc_sp rc_mb) m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof.
  intros st m (_ & (HD & _) & _) CR.
  destruct HD as [[_ HB] _]. unfold rctx_head_cells, rsecw in HB. cbn [cells_bytes cbytes app] in HB.
  rewrite (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) m RCTX _ 12 1 HB).
  all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
  change (Z.to_nat 12) with 12%nat.
  unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
  rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

End CANSEC3.
End RMallocKit_A3.
