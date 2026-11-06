(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA MmStep StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed XB_mmap_fixed_srz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf7 AsanWf8 AsanWf9 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanRepX AsanFrame AsanRealloc AsanRefillMB AsanRepEnqB AsanRepRefillB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_qrepL BF_qrep B_iface BX_unreg BX_Exit BF_place BF_fakestack_rep BF_kit BF_kit2 BF_poison BF_free_kit BF_qkit BF_mmfix1 BF_unwind BF_gbb BF_free5 BF_free5s BF_free6 BF_free12 BF_ldealloc1 BF_ldealloc4 B_policy5 B_slack5 B_budget5 B_mmchk5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 B_bframe BF_alloc_iface BF_populate_iface BF_dput_iface BF_free_iface BF_refill_iface BF_tkit BF_ainv_kit BF_statics BF_popdefs BF_pop0 BF_popT BF_caT BF_refill_room BF_refillT BF_ldcT BF_deallocT1 BF_free1d BF_free3 BF_free4 BF_deallocT2 BF_deallocT3 BF_deallocT4 BF_deallocT5 BF_deallocT6 BF_roomBI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Model.
Variable E : aenv.
#[local] Notation SB := (ae_space_beg E).

(* [comment removed for export] *)
Lemma arun_recycle : forall a5 gq1 emp popped kept fr orc res,
  kBatchSize * zlen (as_gq a5) <= gq_bytes a5 ->
  rmerge (as_gq a5) = (gq1, emp) -> pop_prefix gq1 (qbytes gq1) kQuarantineMin = (popped, kept) ->
  arun fr (do_recycle E (emp ++ popped) (upd_gq (fun _ => kept) a5)) orc = Some res ->
  arun fr (recycle E a5) orc = Some res.
Proof.
  intros a5 gq1 emp popped kept fr orc res GE MG PP RUN.
  unfold recycle. eapply arun_bind_pl; [apply arun_aget|]. cbv beta zeta.
  unfold acheck. unfold gq_bytes in GE. replace (kBatchSize * zlen (as_gq a5) <=? qbytes (as_gq a5)) with true by (symmetry; apply Z.leb_le; exact GE).
  eapply arun_bind_pl; [apply arun_aret|].
  unfold rmerge in MG. rewrite MG. rewrite PP.
  eapply arun_bind_pl; [apply arun_aupd|]. exact RUN.
Qed.

(* [comment removed for export] *)
Lemma arun_afree_core_recycle : forall (sx a2 a4 : astate) cb cm aid key fid fd orcd evsd orcd' fe orce evse orce'
    gq1 emp popped kept fr orcr a' evsr orcr',
  let a5 := xfer_st a4 in
  as_chunks sx !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  arun fd (depot_put E key (upd_ts (ts_on_free (cm_n cm)) sx)) orcd = Some (a2, ONorm fid, evsd, orcd') ->
  arun fe (enqueue E cb (cm_n cm) (AsanRepFlipB.s3 a2 cb cm aid fid)) orce = Some (a4, ONorm tt, evse, orce') ->
  kThreadQuarantineMax < tq_bytes a4 -> kQuarantineMax < gq_bytes a4 + tq_bytes a4 ->
  kBatchSize * zlen (as_gq a5) <= gq_bytes a5 ->
  rmerge (as_gq a5) = (gq1, emp) -> pop_prefix gq1 (qbytes gq1) kQuarantineMin = (popped, kept) ->
  arun fr (do_recycle E (emp ++ popped) (upd_gq (fun _ => kept) a5)) orcr = Some (a', ONorm tt, evsr, orcr') ->
  exists fuel orc evs orc'', arun fuel (afree_core E key (cb + 16) sx) orc = Some (a', ONorm tt, evs, orc'').
Proof.
  intros until orcr'. cbv zeta. intros Hcm ST UB RUNd RUNe TQ GQ GE MG PP RUNr.
  destruct (arun_orc_app2 _ _ _ _ _ _ _ RUNd) as (ud & _ & Rd). destruct (arun_orc_app2 _ _ _ _ _ _ _ RUNe) as (ue & _ & Re).
  destruct (arun_orc_app2 _ _ _ _ _ _ _ RUNr) as (ur & _ & Rr).
  exists (fd + (fe + fr))%nat, (ud ++ ue ++ ur), (evsd ++ (evse ++ evsr)), [].
  unfold afree_core. eapply arun_bind_pl; [apply arun_aget|]. cbv beta zeta.
  unfold kChunkHeaderSize. replace (cb + 16 - 16) with cb by lia. rewrite Hcm, ST, UB, Z.eqb_refl. cbn [negb].
  eapply arun_bind_pl; [apply arun_aupd|].
  eapply arun_abind; [apply (Rd (ue ++ ur))|].
  eapply arun_bind_pl; [apply arun_aupd|].
  eapply arun_abind; [exact (Re ur)|].
  unfold drain_if_needed. eapply arun_bind_pl; [apply arun_aget|]. cbv beta.
  replace (kThreadQuarantineMax <? tq_bytes a4) with true by (symmetry; apply Z.ltb_lt; exact TQ).
  eapply arun_bind_pl; [apply arun_aupd|]. eapply arun_bind_pl; [apply arun_aget|]. cbv beta.
  replace (kQuarantineMax <? gq_bytes (upd_tq (fun _ => []) (upd_gq (fun g => g ++ as_tq a4) a4))) with true.
  2:{ symmetry. apply Z.ltb_lt. unfold gq_bytes in GQ |- *. unfold tq_bytes in GQ. cbn [as_gq upd_tq upd_gq]. rewrite qbytes_app. exact GQ. }
  pose proof (Rr []) as X. rewrite app_nil_r in X.
  exact (arun_recycle (xfer_st a4) gq1 emp popped kept fr ur _ GE MG PP X).
Qed.

(* [comment removed for export] *)
Lemma arun_do_recycle_cons : forall b rest a0 a1 a2 f1 o1 e1 f2 o2 e2 f3 o3 res,
  in_primary SB (b_addr b) = true -> ((b_addr b - SB) / kRegionSize) mod kNumClasses = kBatchClass ->
  arun f1 (recycle_items E (b_items b) a0) o1 = Some (a1, ONorm tt, e1, []) ->
  arun f2 (local_dealloc E kBatchClass (b_addr b) a1) o2 = Some (a2, ONorm tt, e2, []) ->
  arun f3 (do_recycle E rest a2) o3 = Some res ->
  exists f e, arun f (do_recycle E (b :: rest) a0) (o1 ++ o2 ++ o3) = Some (fst (fst (fst res)), snd (fst (fst res)), e, snd res).
Proof.
  intros b rest a0 a1 a2 f1 o1 e1 f2 o2 e2 f3 o3 [[[s3 o3'] e3] orc3] IP CL R1 R2 R3. cbn [fst snd].
  destruct (arun_orc_app2 _ _ _ _ _ _ _ R1) as (u1 & E1 & R1'). rewrite app_nil_r in E1. subst u1.
  destruct (arun_orc_app2 _ _ _ _ _ _ _ R2) as (u2 & E2 & R2'). rewrite app_nil_r in E2. subst u2.
  exists (f1 + (f2 + f3))%nat, (e1 ++ (e2 ++ e3)). cbn [do_recycle].
  eapply arun_abind; [apply (R1' (o2 ++ o3))|].
  rewrite IP. unfold acheck. rewrite CL, Z.eqb_refl.
  eapply arun_abind; [eapply arun_bind_pl; [apply arun_aret| apply (R2' o3)]| exact R3].
Qed.

(* [comment removed for export] *)
Lemma arun_recycle_items_cons : forall x rest a0 a1 f1 o1 e1 f2 o2 res,
  arun f1 (qcb_recycle E x a0) o1 = Some (a1, ONorm tt, e1, []) ->
  arun f2 (recycle_items E rest a1) o2 = Some res ->
  exists f e, arun f (recycle_items E (x :: rest) a0) (o1 ++ o2) = Some (fst (fst (fst res)), snd (fst (fst res)), e, snd res).
Proof.
  intros x rest a0 a1 f1 o1 e1 f2 o2 [[[s2 o2'] e2] orc2] R1 R2. cbn [fst snd].
  destruct (arun_orc_app2 _ _ _ _ _ _ _ R1) as (u1 & E1 & R1'). rewrite app_nil_r in E1. subst u1.
  exists (f1 + f2)%nat, (e1 ++ e2). cbn [recycle_items]. eapply arun_abind; [apply (R1' o2)| exact R2].
Qed.

(* [comment removed for export] *)
Lemma merge_aux_bytes : forall rest cur acc,
  let '(l, o) := merge_batches_aux cur rest acc in qbytes l + qbytes o = b_size cur + qbytes rest + qbytes acc.
Proof.
  intros rest. induction rest as [|nx rest IH]; intros cur acc; cbn [merge_batches_aux].
  - rewrite BF_qkit.qbytes_cons, !BF_qkit.qbytes_nil. lia.
  - destruct (zlen (b_items cur) + zlen (b_items nx) <=? kBatchCap).
    + set (cur' := mkBatch _ _ _). specialize (IH cur' (acc ++ [mkBatch (b_addr nx) [] kBatchSize])).
      destruct (merge_batches_aux cur' rest _) as [l o]. rewrite BF_qkit.qbytes_app, BF_qkit.qbytes_cons, BF_qkit.qbytes_nil in IH. subst cur'. cbn [b_size] in IH.
      rewrite BF_qkit.qbytes_cons. lia.
    + specialize (IH nx acc). destruct (merge_batches_aux nx rest acc) as [l' o']. rewrite !BF_qkit.qbytes_cons. lia.
Qed.
Lemma rmerge_bytes : forall gq l o, BF_deallocT4.rmerge gq = (l, o) -> qbytes l + qbytes o = qbytes gq.
Proof.
  intros gq l o H. unfold BF_deallocT4.rmerge in H.
  match type of H with (if ?b then _ else _) = _ => destruct b end; [| injection H as <- <-; rewrite BF_qkit.qbytes_nil; lia].
  unfold merge_batches in H. destruct gq as [|b rest]; [injection H as <- <-; rewrite BF_qkit.qbytes_nil; lia|].
  pose proof (merge_aux_bytes rest b []) as M. rewrite H in M. rewrite BF_qkit.qbytes_cons. rewrite BF_qkit.qbytes_nil in M. lia.
Qed.
Lemma apl_app_r : forall l1 l2, apl (l1 ++ l2) -> apl l2.
Proof. intros l1 l2. induction l1 as [|x l1 IH]; intros H; [exact H|]. apply IH. exact (proj2 H). Qed.
End Model.


(* [comment removed for export] *)
Section DeallocT7.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation RI := (ae_region_info E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation INST := 0xaaf58.
#[local] Notation CA := (ae_thread E0 + kThrCache).
#[local] Notation PP := (BF_caT.PP E0 FSB0 HR0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).

Lemma IC0_T7 : ae_ic E0 = both_ic.
Proof. pose proof ENV0 as X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC0 & _). exact IC0. Qed.
(* [comment removed for export] *)
Definition R3 : BF_deallocT3.R3_stmt E0 := BF_qrep.R3_holds E0 IC0_T7.
Definition R4 : BF_deallocT4.R4_stmt E0 := BF_qrep.R4_holds E0 IC0_T7.
#[local] Notation LDC := (ldc_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK (BF_deallocT6.R5b E0) (BF_deallocT6.R6 E0)).
#[local] Notation ITEMP := (qitem_prim_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK).
#[local] Notation ITEMS := (qitem_sec_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u64arr_agree : forall (m m' : mem) A0 ws,
  (forall x, A0 <= x < A0 + 8 * Z.of_nat (length ws) -> m' (wa x) = m (wa x)) ->
  u64arr bsegs m A0 ws -> u64arr bsegs m' A0 ws.
Proof.
  intros m m' A0 ws AG [(B0 & B1 & BR) (W0 & W1 & WR)]. rewrite u64s_length in B1, BR.
  split; [split; [exact B0| split; [rewrite u64s_length; exact B1|]]|].
  - rewrite u64s_length. intros k Hk. rewrite <- (BR k Hk). unfold mrd. rewrite AG by lia. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros k Hk. specialize (WR k Hk). unfold wview in *. rewrite AG by lia. exact WR.
Qed.
Lemma bcellsn_agree : forall (m m' : mem) l k,
  bcellsn m l k -> (forall b x, In b l -> b_addr b <= x < b_addr b + 24 -> m' (wa x) = m (wa x)) -> bcellsn m' l k.
Proof.
  intros m m' l. induction l as [|b l IH]; intros k BC AG; [exact I|]. cbn [bcellsn] in BC |- *. destruct BC as [Hb Hl].
  split; [| apply IH; [exact Hl| intros b' x Hb' Hx; apply (AG b' x); [right; exact Hb'| exact Hx]]].
  eapply (rw_cells_agree bsegs m m'); [| exact Hb]. cbn. intros x Hx. apply (AG b x); [left; reflexivity| clear -Hx; lia].
Qed.
Lemma bitemsl_agree : forall (m m' : mem) l,
  bitemsl m l -> (forall b x, In b l -> b_addr b + 24 <= x < b_addr b + 8192 -> m' (wa x) = m (wa x)) -> bitemsl m' l.
Proof.
  intros m m' l. induction l as [|b l IH]; intros BI AG; [exact I|]. cbn [bitemsl] in BI |- *. destruct BI as [(junk & ARR & LEN) Hl].
  split; [| apply IH; [exact Hl| intros b' x Hb' Hx; apply (AG b' x); [right; exact Hb'| exact Hx]]].
  exists junk. split; [| exact LEN]. eapply (u64arr_agree m m'); [| exact ARR]. rewrite length_app, length_map.
  intros x Hx. apply (AG b x); [left; reflexivity| clear -Hx LEN; lia].
Qed.

(* [comment removed for export] *)
Lemma bitems_words : forall (m : mem) b, bitems m b ->
  exists ws, u64arr bsegs m (b_addr b + 24) ws /\ length ws = 1021%nat /\ (forall k x, nth_error (b_items b) k = Some x -> nth_error ws k = Some (wz x)).
Proof.
  intros m b (junk & ARR & LEN). exists (map (fun z => wz z) (b_items b) ++ junk). split; [exact ARR|]. split; [rewrite length_app, length_map; exact LEN|].
  intros k x Hk. apply (BF_tkit.nth_error_map_app (b_items b) junk k x). exact Hk.
Qed.

(* [comment removed for export] *)
Lemma blk_vs_anybatch : forall E P D (sx : astate) b x cm,
  AWf E P D sx -> as_chunks sx !! x = Some cm -> In b ((as_tq sx ++ as_gq sx) ++ D) ->
  blk_hi sx cm <= b_addr b \/ b_addr b + 8192 <= blk_lo cm.
Proof.
  intros E P D sx b x cm WF Hx Hb. pose proof WF as (WE & WR & _ & [K1 _] & WQ & (_ & _ & S3 & _) & _).
  destruct (batch_block E D sx b WQ ltac:(unfold all_batches; rewrite app_assoc; exact Hb)) as (CV & _ & _ & NCB).
  assert (CS : class_size kBatchClass = 8192) by reflexivity. assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E sx kBatchClass _ HB24 WR CV) as [I1 I2].
  destruct (K1 _ _ Hx) as (ECB & KNr & ERZ & KP & _). unfold blk_lo, blk_hi.
  destruct (cm_prim cm) as [c|] eqn:PC.
  - destruct KP as (FP & Ec & CVc & _). pose proof (chunk_beg_loc E P D sx x cm WF Hx) as CL. rewrite PC in CL. destruct CL as (Hc & _).
    destruct (carved_blocks_disjoint E sx c (cm_alloc_beg cm) kBatchClass (b_addr b) Hc HB24 WR CVc CV) as [[-> EQ]|DJ].
    + exfalso. apply NCB. exists x, cm. split; [exact Hx| exact EQ].
    + clear -DJ CS. lia.
  - destruct KP as (FP & sc & Hsc & Hab & Hms & _). destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SP & _).
    pose proof (map_size_facts (cm_n cm)) as (_ & MG & _). rewrite <- Hms in MG.
    unfold kPageSize, kRegionSize, kSpaceSize in *. clear -I1 I2 SP Hab MG CS Hms. lia.
Qed.

(* [comment removed for export] *)
Lemma ci_of_batch : forall E P l (ai : astate) b, AWf E P l ai -> In b l -> as_cache_inited ai = true.
Proof.
  intros E P l ai b WF Hb. pose proof WF as (_ & _ & (_ & WC2 & _) & _ & (_ & QD & _) & _).
  destruct (QD b Hb) as ((k & K0 & Ek & KB) & _). change (class_size kBatchClass) with 8192 in KB.
  destruct (as_cache_inited ai) eqn:CI0; [reflexivity| exfalso].
  destruct (WC2 eq_refl) as [_ RE]. unfold region_of, get_region in KB. rewrite RE, lookup_empty in KB. cbn in KB. clear -K0 KB. nia.
Qed.

(* [comment removed for export] *)
Lemma sechi_of : forall E P l (ai : astate) nd Fq, AWf E P l ai -> BI nd Fq ai -> fst (ae_img E) = 0x10000 -> 0x5f3000 <= snd (ae_img E) ->
  forall sc, In sc (as_sec ai) -> 0x603000 <= sc_map_beg sc.
Proof.
  intros E P l ai nd Fq WF HBI EI1 EI2 sc Hsc.
  pose proof WF as (WE & _ & _ & [K1 _] & _ & (_ & _ & S3 & _) & _). pose proof HBI as (_ & B6 & _ & SC & _).
  destruct (SC sc Hsc) as (x & cm & Hx & PC & Hab & Hms). destruct (S3 sc Hsc) as (_ & AM & _ & _ & _ & _ & RSV).
  pose proof (RSV _ (proj1 (wf_env_img _ WE))) as X. rewrite EI1 in X. cbn [fst snd] in X.
  destruct (K1 _ _ Hx) as (_ & KNr & _ & KP & _). rewrite PC in KP. destruct KP as [FP _]. destruct (B6 _ _ Hx) as [N1 _].
  assert (NS : ~ cm_n cm <= 64512) by (intros LE; pose proof (proj2 (from_primary_iff (cm_n cm) ltac:(clear -N1; lia)) LE); congruence).
  pose proof (map_size_facts (cm_n cm)) as (_ & MG & _). pose proof (needed_ge (cm_n cm)) as NG. pose proof (rz_size_pos (cm_n cm)) as RP.
  unfold app_mem in AM. rewrite kHighMemBeg_val in AM. unfold kPageSize in *. clear -AM X EI2 Hms MG NG NS RP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LOOP.
(* [comment removed for export] *)
Variables (s : aps) (mo : Model) (m : mem) (lo U C C' cb B : Z) (key : list Z) (K : TSet) (cm : chunkmeta) (aid fid : Z) (a2 a4 : astate).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x8 x9 x18 x19 x20 : word) (F : bvmap 5 word) (fc : bv 32).
#[local] Notation a := (aps_alloc s).
#[local] Notation n := (cm_n cm).
Hypothesis KN : K [].
Hypothesis HU : bv_unsigned sp = U.
Hypothesis HC1 : 1 <= C.
Hypothesis HCS : FSLACK <= C'.
Hypothesis AIV : AINVc a m mo.
Hypothesis FB : fbudget_pre a.
Hypothesis LIVE : In (cb + 16, n) (live_blocks a).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= U - K_FREE.
Hypothesis SPA : U mod 16 = 0.
Hypothesis SPH : U < 2^47.
Hypothesis TP : tp = wz 0x5e1550.
Hypothesis Hcm : as_chunks a !! cb = Some cm.
Hypothesis ST : cm_state cm = CAllocated aid.
Hypothesis UB : cm_user_beg cm = cb + 16.
Hypothesis E4sec : as_sec a4 = as_sec a.
Hypothesis WF4 : AWf E0 [] [] a4.
Hypothesis HCB : 0x603000 <= cb /\ cb + 16 + 8 * BF_free1d.l8 n <= alloc_ceiling /\ cb mod 16 = 0.
Hypothesis HNHI : 0 <= n / 2^32 < 256.
Hypothesis HNLO : 0 <= n mod 2^32 < 2^32.
(* [comment removed for export] *)
Hypothesis KONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     dealloc_post_state E0 FSB0 HR0 L0 RES0 EB0 PL0 a a' m m' mo mo' s C C' (cb + 16) n lo U key ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K.

(* [comment removed for export] *)
Definition LINV (l : list batch) (ai : astate) (mi : mem) (moi : Model) : Prop :=
     (* [comment removed for export] *)
     AWf E0 [] l ai /\ ARep bsegs E0 (DepotR bsegs E0) ai mi /\ AKern E0 ai moi /\ res_ok ai /\ depot_inv E0 ai /\ sstats_ok ai /\ csmall ai
  /\ BI (zlen l) fzero ai
  /\ as_tq ai = [] /\ gq_bytes ai <= kQuarantineMax
  /\ RTOKc (C - 1) (C' - DSLACK) (sA ai s) moi
  /\ m_fs moi = m_fs mo /\ m_fds moi = m_fds mo /\ m_tid moi = m_tid mo
  /\ as_nprim_ever ai = as_nprim_ever a /\ as_residue ai = as_residue a /\ as_ndepot_ins ai = as_ndepot_ins a + 1
  /\ as_node_blocks ai = as_node_blocks a4 /\ as_store_blocks ai = as_store_blocks a4 /\ (forall sc, In sc (as_sec ai) -> In sc (as_sec a))
  /\ Permutation (live_blocks a) ((cb + 16, n) :: live_blocks ai)
  /\ (forall b, In b l -> items_live ai (b_items b))
  /\ (forall a' fr orcr evsr orcr', arun fr (do_recycle E0 l ai) orcr = Some (a', ONorm tt, evsr, orcr') ->
        exists fuel orc evs orc'', arun fuel (afree_core E0 key (cb + 16) a) orc = Some (a', ONorm tt, evs, orc''))
     (* [comment removed for export] *)
  /\ mem_inv bsegs mi /\ rt_misc5 FSB0 PL0 E0 mi
  /\ put_frame ra sp s0 s1 s2 s3 s4 s5 s6 T B mi
  /\ tmpc (U - 160) mi l
  /\ rw_cells bsegs mi (U - 128) [C8 (wz (T + 208)); C8 (wz B); C8 (wz n); C8 (wz (T + 80)); C8 (wz (INST + 728)); C8 (wz 0x36df4)]
  /\ bcells mi l /\ bitemsl mi l /\ Forall (bok lo T) l /\ bapart l /\ qbytes l <= 2^30
  /\ (exists W, munch W m mi /\ Forall (aw_ok E0 a a4 lo U) W
               /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W).


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma itemW_high_agree : forall l (ai : astate) moi xc cmx usp (mi m' : mem),
  AWf E0 [] l ai -> AKern E0 ai moi -> as_chunks ai !! xc = Some cmx ->
  match cm_prim cmx with Some c => rg_mapped_fa (get_region ai c) + kFreeArrayMapSize <= kFreeArraySize /\ 4 * (rg_num_freed (get_region ai c) + hint c) <= kFreeArraySize | None => True end ->
  alloc_ceiling <= lo -> lo <= usp ->
  munch (item_W E0 ai xc cmx usp) mi m' -> forall z, usp <= z < 2^64 -> m' (wa z) = mi (wa z).
Proof.
  intros l ai moi xc cmx usp mi m' WF AK Hx RM LOC' LOU MU z Hz. pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB.
  pose proof WF as (WE & WR & WC & [K1 _] & WQ & (S1 & S2 & S3 & S4 & S5) & WD).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _). pose proof (wf_env_thread _ WE) as (_ & _ & WT & _).
  pose proof (wf_env_ptr _ WE) as (_ & _ & PAB & _).
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (K1 _ _ Hx) as (ECB & KNr & ERZ & KP & _).
  pose proof (chunk_user_in_block E0 [] l ai xc cmx WF Hx) as (U1 & U2 & U3). unfold user_lo, user_hi, blk_lo, blk_hi, kChunkHeaderSize in U1, U2, U3.
  assert (LBL : last_beg ai + 32 <= alloc_ceiling).
  { unfold last_beg. destruct (BF_deallocT2.snoc_case (as_sec ai)) as [E|(l' & y & E)]; rewrite E; [cbn; clear -CR; lia|].
    rewrite rev_app_distr. cbn [rev app]. assert (Hy : In y (as_sec ai)) by (rewrite E; apply in_app_iff; right; left; reflexivity).
    destruct (S3 y Hy) as (_ & _ & Y3 & Y4 & Y5 & _). clear -Y3 Y4 Y5. unfold kPageSize in Y5. Z.div_mod_to_equations. lia. }
  apply MU. rewrite wa_unsigned by (clear -Hz LOU LOC' CR; lia). unfold item_W. cbv zeta.
  destruct (cm_prim cmx) as [c|] eqn:PC.
  - destruct KP as (FP & Ec & CVc & _). pose proof (chunk_beg_loc E0 [] l ai xc cmx WF Hx) as CL. rewrite PC in CL. destruct CL as (Hc & _).
    pose proof (carved_in_space E0 ai c _ Hc WR CVc) as [I1 I2]. destruct (proj2 WR c Hc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). cbv zeta in R1, R3, R5, R7, R8.
    pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as [_ CSZ]. pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as HR.
    unfold ldc_W. cbv zeta. unfold free_array, region_beg, ae_region_info. rewrite KHB in WE2.
    cbn [outside app]. unfold K_ITEM, K_LDC, kThrStats, kThrCache, kThrCacheStats, kPerClassSize, kRegSize, kShadowBase, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize, kRegionSize, kSpaceSize, kLargestClassID in *.
    unfold region_of in R1, R3, R5, R7, R8. destruct RM as [RM1 RM2].
    clear -Hz LOC' LOU CR WT G1 G3 I1 I2 R1 R3 R5 R7 R8 RM1 RM2 CSZ HR Hc U1 U2 U3 KNr WE2 WE5. repeat split; try exact I; Z.div_mod_to_equations; lia.
  - destruct KP as (FP & sc & Hsc & Hab & Hms & _). destruct (S3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    cbn [outside app]. unfold K_ITEM, kThrStats, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kShadowBase, kChunksBlockCount, kPageSize in *.
    rewrite Hab, Hms in *. pose proof (map_size_facts (cm_n cmx)) as (_ & MG & M2P). unfold kPageSize in MG, M2P. rewrite <- Hms in *.
    clear -Hz LOC' LOU CR WT PAB LBL M3 M4 U1 U2 U3 KNr MG M2P Hab. repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.

Lemma itemW_batch_agree : forall l (ai : astate) moi xc cmx usp (mi m' : mem) b',
  AWf E0 [] l ai -> AKern E0 ai moi -> as_chunks ai !! xc = Some cmx ->
  match cm_prim cmx with Some c => rg_mapped_fa (get_region ai c) + kFreeArrayMapSize <= kFreeArraySize /\ 4 * (rg_num_freed (get_region ai c) + hint c) <= kFreeArraySize | None => True end ->
  In b' ((as_tq ai ++ as_gq ai) ++ l) -> bok lo T b' -> alloc_ceiling <= lo -> lo <= usp - K_ITEM -> usp < 2^47 ->
  munch (item_W E0 ai xc cmx usp) mi m' -> forall z, b_addr b' <= z < b_addr b' + 8192 -> m' (wa z) = mi (wa z).
Proof.
  intros l ai moi xc cmx usp mi m' b' WF AK Hx RM Hb' BOK LOC' LOU UH MU z Hz. unfold K_ITEM in LOU. pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB.
  pose proof WF as (WE & WR & WC & [K1 _] & WQ & (S1 & S2 & S3 & S4 & S5) & WD).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _). pose proof (wf_env_ptr _ WE) as (_ & _ & PAB & PAR & _).
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (K1 _ _ Hx) as (ECB & KNr & ERZ & KP & _).
  pose proof (chunk_user_in_block E0 [] l ai xc cmx WF Hx) as (U1 & U2 & U3). unfold user_lo, user_hi, blk_lo, blk_hi, kChunkHeaderSize in U1, U2, U3.
  pose proof (blk_vs_anybatch E0 [] l ai b' xc cmx WF Hx Hb') as BVB. unfold blk_lo, blk_hi in BVB.
  pose proof BOK as (B1 & B2 & B3 & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  destruct (batch_block E0 l ai b' WQ ltac:(unfold all_batches; rewrite app_assoc; exact Hb')) as (CV & _).
  pose proof (carved_in_space E0 ai kBatchClass _ HB24 WR CV) as [I1 I2]. pose proof (carved_range E0 ai kBatchClass _ HB24 WR CV) as [J1 J2].
  change (class_size kBatchClass) with 8192 in I2, J2. unfold region_beg, kBatchClass in J1, J2.
  assert (LBL : last_beg ai + 32 <= b_addr b' \/ b_addr b' + 8192 <= last_beg ai + 24).
  { unfold last_beg. destruct (BF_deallocT2.snoc_case (as_sec ai)) as [E|(l' & y & E)]; rewrite E; [cbn; left; clear -B1; lia|].
    rewrite rev_app_distr. cbn [rev app]. assert (Hy : In y (as_sec ai)) by (rewrite E; apply in_app_iff; right; left; reflexivity).
    destruct (S3 y Hy) as (_ & _ & Y3 & Y4 & Y5 & Y6 & _). clear -Y3 Y4 Y5 Y6 I1 I2. unfold kPageSize, kRegionSize, kSpaceSize in *. Z.div_mod_to_equations. lia. }
  apply MU. rewrite wa_unsigned by (clear -Hz B1 B2 LOU UH; lia). unfold item_W. cbv zeta.
  destruct (cm_prim cmx) as [c|] eqn:PC.
  - destruct KP as (FP & Ec & CVc & _). pose proof (chunk_beg_loc E0 [] l ai xc cmx WF Hx) as CL. rewrite PC in CL. destruct CL as (Hc & _).
    destruct (proj2 WR c Hc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). cbv zeta in R1, R3, R5, R7, R8. unfold region_of in R1, R3, R5, R7, R8.
    pose proof (carved_in_space E0 ai c _ Hc WR CVc) as [Ic1 Ic2].
    pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as [_ CSZ]. pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as HR.
    unfold ldc_W. cbv zeta. unfold free_array, region_beg, ae_region_info.
    cbn [outside app]. unfold K_ITEM, K_LDC, kThrStats, kThrCache, kThrCacheStats, kPerClassSize, kRegSize, kShadowBase, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize, kRegionSize, kSpaceSize, kLargestClassID in *.
    destruct RM as [RM1 RM2].
    clear -Hz B1 B2 B3 LOU LOC' CR I1 I2 J1 J2 BVB R1 R3 R5 R7 R8 RM1 RM2 CSZ HR Hc U1 U2 U3 KNr Ic1 Ic2 G3 WE5. unfold rg_num_freed, zlen in *. repeat split; try exact I; Z.div_mod_to_equations; lia.
  - destruct KP as (FP & sc & Hsc & Hab & Hms & _). destruct (S3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    cbn [outside app]. unfold K_ITEM, kThrStats, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kShadowBase, kChunksBlockCount, kPageSize, kSpaceSize, kRegionSize in *.
    pose proof (map_size_facts (cm_n cmx)) as (_ & MG & M2P). unfold kPageSize in MG, M2P. rewrite <- Hms in *.
    clear -Hz B1 B2 B3 LOU LOC' CR I1 I2 G1 G3 PAR LBL M3 M4 M6 U1 U2 U3 KNr MG M2P Hab. repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma loop_exit : forall ai mi moi (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  LINV [] ai mi moi -> stk bsegs mi lo (U - 160) ->
  realizes_cfg acfg bsegs (mkCfg (drl_ret gp tp s10 s11 F fc (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9
                                         xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mi) moi) K.
Proof.
  intros until xt6. intros LI SK.
  destruct LI as (WF & REP & AK & RES & DI & SS & CS & HBI & TQ & GQ & TOK & Ffs & Ffds & Ftid & Enp & Eres & Endi & Enb & Esb & SECi & PLIVE & ILIVE & RUNK
                  & MI & RT & PF & TC & FRR & BC & BIT & BOK & BAP & QBYT & (W & MU & AWOK & AVOID)).
  pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & GLE).
  assert (ENV : ENVOK E0 FSB0 (sA ai s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof WF as (WE & _).
  set (P0 := PP (sA ai s) moi).
  pose proof (BF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA ai s) moi R0 R0' ATK) as KIP0.
  assert (AKs : AKern E0 (aps_alloc (sA ai s)) moi) by exact AK.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= U -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 (sA ai s) moi AKs WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  unfold tmpc in TC. pose proof (BF_kit3.rwc_join_at bsegs mi _ _ _ _ TC FRR ltac:(cbn; clear; lia)) as FR10. cbn [app] in FR10.
  set (Q1 := fun ms : machine_state => exists (m9 : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ms = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m9 (seg_rom bsegs)
        /\ mem_inv bsegs m9 /\ stk bsegs m9 lo U /\ wmono bsegs mi m9 /\ (forall z, m9 z = mi z)).
  eapply (rzA_seg_cfg bsegs (aSc (sA ai s)) (aNc (sA ai s)) (aEBc (sA ai s)) P0 Q1).
  { unfold drl_ret. rewrite (ret_pc_even 0x34934) by (clear; lia).
    replace (U - 160) with (U - 80 + -80) by (clear; lia).
    eapply (recycle_tail P0 gp tp (wz (INST + 728)) (wz (T + 80)) (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 xt6 F fc Q1 (U - 80) lo 0
              LOC ltac:(clear -LO; lia) ltac:(clear; lia) ltac:(intros y k H1 H2; apply PSTK; [exact H1| clear -H2; lia]) mi);
      [exact MI| replace (U - 80 + -80) with (U - 160) by (clear; lia); exact SK| replace (U - 80 + -80) with (U - 160) by (clear; lia); exact FR10|].
    intros m' MI' SK' MU' WM'. rewrite (ret_pc_even 0x36df4) by (clear; lia).
    eapply evtA_cut.
    { replace (U - 80) with (bv_unsigned sp - 80) by (rewrite HU; reflexivity).
      eapply (put_epi P0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' lo T B cb (n / 2^32) (n mod 2^32) n LOC ltac:(rewrite HU; clear -SPH; lia) HCB HNHI HNLO
                ltac:(rewrite HU; exact PSTK) _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0); rewrite ?HU; [exact SK'| clear -LO; lia| exact MI'|].
      unfold put_frame. unfold put_frame in PF. rewrite HU in PF |- *. eapply (rw_cells_agree bsegs mi m'); [| exact PF]. intros z _. apply MU'. exact I. }
    intros ms9 HP. unfold put_ret_post in HP. destruct HP as (m9 & -> & MU9 & WM9 & MI9 & SK9). rewrite HU in SK9.
    apply evtA_done. unfold Q1. exists m9. do 14 eexists.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact SK9|]. split; [exact (wmono_trans _ _ _ _ WM' WM9)|].
    intros z. transitivity (m' z); [apply MU9; exact I| apply MU'; exact I]. }
  { exact KIP0. }
  intros ms9 mo9 HQ AG9 KIP9. unfold Q1 in HQ.
  destruct HQ as (m9 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MI9 & SK9 & WM9 & AG).
  pose proof (magree_frame _ _ AG9) as (Ffds9 & Fvm9 & Flz9 & Ffs9 & Fh9 & Ftid9 & _). destruct KIP9 as [KIA9 _].
  assert (REP9 : ARep bsegs E0 (DepotR bsegs E0) ai m9).
  { apply (ARep_high_agree E0 [] [] ai mi m9 lo REP WF (renv_of E0 PL0 ENV0 PL0OK [] ai moi WF AK EI1 EI2) LOC WM9). intros z _ _. apply AG. }
  eapply KONT. unfold dealloc_post_state.
  split; [exact SK9|].
  split. { exists W. split; [eapply munch_trans; [exact MU| intros x _; apply AG]|]. split; [| exact AVOID].
           eapply Forall_impl; [| exact AWOK]. intros iv Hiv. apply (aw_ok_mono E0 a a ai a4 lo U U iv); [| rewrite Enb; intros x Hx; exact Hx| rewrite Esb; intros x Hx; exact Hx| clear; lia| exact Hiv].
           intros sc [Hsc|Hsc]; [left; exact Hsc| left; rewrite <- E4sec; exact Hsc]. }
  split. { apply (RUNK ai 0%nat [] [] []). reflexivity. }
  split. { split; [exact REP9|]. split; [exact WF|]. split; [exact (AKern_frame _ _ _ _ Fvm9 Flz9 AK)|]. split; [exact RES|].
           split; [split; [unfold tq_bytes; rewrite TQ; cbn; unfold kThreadQuarantineMax; clear; lia| exact GQ]|].
           split; [exact DI|]. split; [unfold AsanBudget2.binv; exact HBI|].
           split; [exact MI9|]. split; [apply (rt_misc5_agree E0 FSB0 PL0 mi m9 RT); intros z _; apply AG|]. split; [exact SS| exact CS]. }
  split. { unfold FSLACK. unfold DSLACK in TOK. exact (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG9 KIA9). }
  split; [rewrite Ffs9; exact Ffs|]. split; [rewrite Ffds9; exact Ffds|]. split; [rewrite Ftid9; exact Ftid|].
  split; [unfold facct; rewrite Enp, Eres, Endi; clear; repeat split; lia| exact PLIVE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RUNKI (rest : list batch) (bb : Z) (xs : list Z) (ai : astate) : Prop :=
  forall a1 f1 o1 e1, arun f1 (recycle_items E0 xs ai) o1 = Some (a1, ONorm tt, e1, []) ->
  forall ab f2 o2 e2, arun f2 (local_dealloc E0 kBatchClass bb a1) o2 = Some (ab, ONorm tt, e2, []) ->
  forall a' f3 o3 e3 o3', arun f3 (do_recycle E0 rest ab) o3 = Some (a', ONorm tt, e3, o3') ->
  exists fuel orc evs orc'', arun fuel (afree_core E0 key (cb + 16) a) orc = Some (a', ONorm tt, evs, orc'').

(* [comment removed for export] *)
Definition IINV (b : batch) (rest : list batch) (ws : list word) (j8 : list byte) (i : Z) (ai : astate) (mi : mem) (moi : Model) : Prop :=
     AWf E0 [] (b :: rest) ai /\ ARep bsegs E0 (DepotR bsegs E0) ai mi /\ AKern E0 ai moi /\ res_ok ai /\ depot_inv E0 ai /\ sstats_ok ai /\ csmall ai
  /\ BI (zlen (b :: rest)) fzero ai
  /\ as_tq ai = [] /\ gq_bytes ai <= kQuarantineMax
  /\ RTOKc (C - 1) (C' - DSLACK) (sA ai s) moi
  /\ m_fs moi = m_fs mo /\ m_fds moi = m_fds mo /\ m_tid moi = m_tid mo
  /\ as_nprim_ever ai = as_nprim_ever a /\ as_residue ai = as_residue a /\ as_ndepot_ins ai = as_ndepot_ins a + 1
  /\ as_node_blocks ai = as_node_blocks a4 /\ as_store_blocks ai = as_store_blocks a4 /\ (forall sc, In sc (as_sec ai) -> In sc (as_sec a))
  /\ Permutation (live_blocks a) ((cb + 16, n) :: live_blocks ai)
  /\ (forall b', In b' rest -> items_live ai (b_items b')) /\ items_live ai (skipn (Z.to_nat i) (b_items b))
  /\ (forall x, In x (firstn (Z.to_nat i) (b_items b)) -> as_chunks ai !! x = None)
  /\ RUNKI rest (b_addr b) (skipn (Z.to_nat i) (b_items b)) ai
  /\ mem_inv bsegs mi /\ rt_misc5 FSB0 PL0 E0 mi
  /\ put_frame ra sp s0 s1 s2 s3 s4 s5 s6 T B mi /\ tmpc (U - 160) mi rest
  /\ rw_cells bsegs mi (U - 128) [C8 (wz (T + 208)); C8 (wz B); C8 (wz n); C8 (wz (T + 80)); C8 (wz (INST + 728)); C8 (wz 0x36df4)]
  /\ drl_fr_lo (U - 160) mi j8 /\ drl_fr_cb (U - 160) (wz (T + 208)) (wz B) mi /\ drl_fr_hi (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 mi
  /\ rw_cells bsegs mi (b_addr b) [C8 (wz (bhd rest)); C8 (wz (b_size b)); C8 (wz (bcnt b))] /\ u64arr bsegs mi (b_addr b + 24) ws
  /\ bcells mi rest /\ bitemsl mi rest /\ Forall (bok lo T) (b :: rest) /\ bapart (b :: rest) /\ qbytes rest <= 2^30
  /\ (exists W, munch W m mi /\ Forall (aw_ok E0 a a4 lo U) W
               /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W).

Lemma hsb_of : forall P l (ai : astate), AWf E0 P l ai -> 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Proof.
  intros P l ai WF. pose proof WF as ((WE1 & WE2 & WE3 & WE4 & WE5 & _) & _). rewrite B_bundle.kHighMemBeg_val in WE2.
  split; [clear -WE2 WE3; lia|]. split; [clear -WE1; Z.div_mod_to_equations; nia| clear -WE4 WE5; unfold kSpaceSize in WE4 |- *; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sh_excluded_false : forall z,
  (z < ae_fs_beg E0 \/ ae_fs_beg E0 + ae_fs_len E0 <= z) -> (z < ae_iarena E0 \/ ae_iarena E0 + kIArenaLen <= z) ->
  (z < SB + kSpaceSize \/ SB + kSpaceSize + kPageSize <= z) -> sh_excluded E0 z = false.
Proof.
  intros z H1 H2 H3. unfold sh_excluded, in_fakestack, in_iarena, in_reginfo.
  apply orb_false_intro; [apply orb_false_intro|]; apply (proj2 (andb_false_iff _ _));
    [destruct H1 as [H|H]| destruct H2 as [H|H]| destruct H3 as [H|H]]; (try (left; apply Z.leb_gt; exact H)); right; apply Z.ltb_ge; exact H.
Qed.
(* [comment removed for export] *)
Lemma resv_excl : forall P l (ai : astate) moi z, AWf E0 P l ai -> AKern E0 ai moi ->
  SB <= z < SB + kSpaceSize -> sh_excluded E0 z = false.
Proof.
  intros P l ai moi z WF AK Hz. pose proof (proj1 WF) as WE. pose proof (wf_env_resv _ WE) as (_ & V2 & V3 & _).
  pose proof (wf_env_fs _ WE) as (_ & _ & F0 & _ & F4 & _). pose proof (wf_env_iarena _ WE) as (_ & _ & _ & I4 & _). unfold kIArenaLen in I4.
  apply sh_excluded_false; unfold kIArenaLen, kSpaceSize, kPageSize in *; clear -Hz V2 V3 F0 F4 I4; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ldcRM (ai : astate) (c : Z) : Prop :=
  rg_mapped_fa (get_region ai c) + kFreeArrayMapSize <= kFreeArraySize /\ 4 * (rg_num_freed (get_region ai c) + hint c) <= kFreeArraySize.

Lemma ldcW_high_agree : forall P l (ai : astate) moi c usp (mi m' : mem),
  AWf E0 P l ai -> AKern E0 ai moi -> 1 <= c <= kLargestClassID -> ldcRM ai c -> alloc_ceiling <= lo -> lo <= usp ->
  munch (ldc_W E0 ai c usp) mi m' -> forall z, usp <= z < 2^64 -> m' (wa z) = mi (wa z).
Proof.
  intros P l ai moi c usp mi m' WF AK Hc [RM1 RM2] LOC' LOU MU z Hz. pose proof alloc_ceiling_range as CR.
  pose proof WF as (WE & WR & _). pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _). pose proof (wf_env_thread _ WE) as (_ & _ & WT & _).
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (proj2 WR c Hc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). cbv zeta in R1, R3, R5, R7, R8. unfold region_of in R1, R3, R5, R7, R8.
  pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as HR.
  apply MU. rewrite wa_unsigned by (clear -Hz LOU LOC' CR; lia). unfold ldc_W. cbv zeta. unfold free_array, region_beg, ae_region_info.
  cbn [outside app]. unfold K_LDC, kThrStats, kThrCache, kThrCacheStats, kPerClassSize, kRegSize, kShadowBase, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize, kRegionSize, kSpaceSize, kLargestClassID in *.
  unfold rg_num_freed, zlen in *. clear -Hz LOC' LOU CR WT G3 R1 R3 R5 R7 R8 RM1 RM2 HR Hc WE5. repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.

Lemma ldcW_batch_agree : forall P l (ai : astate) moi c usp (mi m' : mem) b',
  AWf E0 P l ai -> AKern E0 ai moi -> 1 <= c <= kLargestClassID -> ldcRM ai c ->
  In b' ((as_tq ai ++ as_gq ai) ++ l) -> bok lo T b' -> alloc_ceiling <= lo -> lo <= usp - K_LDC -> usp < 2^47 ->
  munch (ldc_W E0 ai c usp) mi m' -> forall z, b_addr b' <= z < b_addr b' + 8192 -> m' (wa z) = mi (wa z).
Proof.
  intros P l ai moi c usp mi m' b' WF AK Hc [RM1 RM2] Hb' BOK LOC' LOU UH MU z Hz. unfold K_LDC in LOU. pose proof alloc_ceiling_range as CR.
  pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (proj2 WR c Hc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). cbv zeta in R1, R3, R5, R7, R8. unfold region_of in R1, R3, R5, R7, R8.
  pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as HR.
  pose proof BOK as (B1 & B2 & B3 & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  destruct (batch_block E0 l ai b' WQ ltac:(unfold all_batches; rewrite app_assoc; exact Hb')) as (CV & _).
  pose proof (carved_in_space E0 ai kBatchClass _ HB24 WR CV) as [I1 I2]. pose proof (carved_range E0 ai kBatchClass _ HB24 WR CV) as [J1 J2].
  change (class_size kBatchClass) with 8192 in I2, J2. unfold region_beg, kBatchClass in J1, J2.
  apply MU. rewrite wa_unsigned by (clear -Hz B1 B2 LOU UH; lia). unfold ldc_W. cbv zeta. unfold free_array, region_beg, ae_region_info.
  cbn [outside app]. unfold K_LDC, kThrStats, kThrCache, kThrCacheStats, kPerClassSize, kRegSize, kShadowBase, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize, kRegionSize, kSpaceSize, kLargestClassID in *.
  unfold rg_num_freed, zlen in *. clear -Hz B1 B2 B3 LOU CR I1 I2 J1 J2 R1 R3 R5 R7 R8 RM1 RM2 HR Hc. repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.

Lemma ldcW_awok : forall P l (ai : astate) moi c usp,
  AWf E0 P l ai -> AKern E0 ai moi -> 1 <= c <= kLargestClassID -> ldcRM ai c -> lo <= usp - K_LDC -> usp <= U ->
  Forall (aw_ok E0 a a4 lo U) (ldc_W E0 ai c usp).
Proof.
  intros P l ai moi c usp WF AK Hc [RM1 RM2] LOU UU. unfold K_LDC in LOU. pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB.
  pose proof WF as (WE & WR & _). pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _). rewrite KHB in WE2.
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (proj2 WR c Hc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). cbv zeta in R1, R3, R5, R6, R7, R8. unfold region_of in R1, R3, R5, R6, R7, R8.
  pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as HR.
  assert (EXCL : forall z, SB <= z < SB + kSpaceSize -> sh_excluded E0 z = false) by (intros z Hz; exact (resv_excl P l ai moi z WF AK Hz)).
  unfold ldc_W. cbv zeta. unfold free_array, region_beg, ae_region_info.
  unfold K_LDC, kThrStats, kThrCache, kThrCacheStats, kPerClassSize, kRegSize, kShadowBase, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize, kRegionSize, kSpaceSize, kLargestClassID in *.
  unfold rg_num_freed, zlen in *.
  repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
  - left. clear -LOU UU. lia.
  - do 2 right; left. exists (T + kThrCache, kPerClassSize * kNumClasses). split; [unfold arep_thr_ranges; do 3 right; left; reflexivity| cbn [fst snd]; unfold kThrCache, kPerClassSize, kNumClasses; clear -Hc; lia].
  - do 2 right; left. exists (T + kThrCacheStats + 16, 16). split; [unfold arep_thr_ranges; do 4 right; left; reflexivity| cbn [fst snd]; unfold kThrCacheStats; clear; lia].
  - do 2 right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrStats; clear; lia].
  - do 3 right; left. change kResvLen with 137439023104. clear -G1 G3 Hc. lia.
  - do 3 right; left. change kResvLen with 137439023104. clear -G1 G3 Hc R5 R8 HR RM2. lia.
  - do 3 right; left. change kResvLen with 137439023104. clear -G1 G3 Hc R5 RM1. lia.
  - do 8 right. split.
    + right. rewrite KHB. unfold B_base.A_SB. clear -G1 G3 Hc R5 RM1 WE2 WE3 WE5 CR. Z.div_mod_to_equations. lia.
    + intros z Hz. apply EXCL. unfold B_base.A_SB in Hz |- *. unfold kSpaceSize. clear -Hz G1 G3 Hc R5 R6 RM1 WE1 WE2 WE3. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma live_old_loc : forall P l (ai : astate) moi blo bsz,
  AWf E0 P l ai -> AKern E0 ai moi -> Permutation (live_blocks a) ((cb + 16, n) :: live_blocks ai) ->
  In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) ->
  exists k cmk, as_chunks ai !! k = Some cmk /\ (exists ik, cm_state cmk = CAllocated ik) /\ blk_lo cmk + 16 <= blo /\ blo + bsz <= blk_hi ai cmk /\ 1 <= bsz
  /\ blo + bsz <= alloc_ceiling /\ (blo + bsz <= kLowAppEnd \/ kHighMemBeg <= blo)
  /\ ((exists c', 1 <= c' <= kLargestClassID /\ SB + c' * kRegionSize <= blk_lo cmk /\ blk_hi ai cmk <= SB + c' * kRegionSize + kFreeArrayOffset
                   /\ ae_resv_beg E0 <= SB /\ SB + kSpaceSize + kPageSize <= ae_resv_beg E0 + kResvLen)
      \/ (exists sc, In sc (as_sec ai) /\ blk_lo cmk = sc_map_beg sc + kPageSize /\ blk_hi ai cmk = sc_map_beg sc + sc_map_size sc
             /\ (sc_map_beg sc + sc_map_size sc <= SB \/ SB + kSpaceSize <= sc_map_beg sc)
             /\ (sc_map_beg sc + sc_map_size sc <= T \/ T + 4096 <= sc_map_beg sc)
             /\ (sc_map_beg sc + sc_map_size sc <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= sc_map_beg sc)
             /\ (sc_map_beg sc + sc_map_size sc <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= sc_map_beg sc))).
Proof.
  intros P l ai moi blo bsz WF AK PL LIVEb NEb.
  assert (LIVEi : In (blo, bsz) (live_blocks ai)).
  { pose proof (Permutation_in _ PL LIVEb) as X. destruct X as [E|X]; [exfalso; exact (NEb (eq_sym E))| exact X]. }
  destruct (BF_tkit.live_block_loc E0 P l ai blo bsz WF LIVEi) as (k & cmk & Hk & UBk & Nk & N1 & B1 & B2 & LOCk).
  destruct (BF_refillT.live_block_whereG E0 P l ai blo bsz WF LIVEi) as (_ & W1 & W2 & _).
  pose proof WF as (WE & WR & _ & [K1 _] & _ & (_ & _ & S3 & _) & _).
  assert (STk : exists ik, cm_state cmk = CAllocated ik).
  { unfold live_blocks, chunk_list in LIVEi. apply in_map_iff in LIVEi. destruct LIVEi as ([k' cm'] & E1 & Hin). apply filter_In in Hin. destruct Hin as [Hin AL]. cbn in AL, E1.
    destruct (K1 _ _ Hk) as (_ & _ & _ & _ & KS). destruct (cm_state cmk) as [ik|qi qj] eqn:SK; [exists ik; reflexivity| exfalso].
    apply (proj2 (list_elem_of_In _ _)) in Hin. apply elem_of_map_to_list in Hin. injection E1 as E2 E3.
    pose proof (AsanClient.chunks_disjoint E0 P l ai k cmk k' cm' WF Hk Hin) as DJ.
    pose proof (chunk_user_in_block E0 P l ai k' cm' WF Hin) as (V1 & V2 & V3). unfold user_lo, user_hi in V1, V2. rewrite ?E2, ?E3 in V1. rewrite ?E2, ?E3 in V2.
    destruct (K1 _ _ Hin) as (_ & Nk' & _). rewrite ?E3 in Nk'.
    destruct (Z.eq_dec k k') as [<-|NE]; [rewrite Hk in Hin; injection Hin as <-; destruct (cm_state cmk); [discriminate| discriminate]|].
    destruct (DJ NE); clear -H B1 B2 V1 V2 N1; lia. }
  exists k, cmk. split; [exact Hk|]. split; [exact STk|]. split; [exact B1|]. split; [exact B2|]. split; [exact N1|]. split; [exact W1|]. split; [exact W2|].
  destruct (cm_prim cmk) as [c'|] eqn:PC.
  - left. destruct LOCk as (Hc' & L1 & L2). exists c'. pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3).
    destruct (proj2 WR c' Hc') as (_ & _ & R3 & _). cbv zeta in R3. unfold region_of in R3. unfold region_beg in L1, L2.
    split; [exact Hc'|]. split; [exact L1|]. split; [clear -L2 R3; lia|]. split; [exact G1| exact G3].
  - right. destruct LOCk as (sc & Hsc & L1 & L2). exists sc. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SP & RSV).
    split; [exact Hsc|]. split; [exact L1|]. split; [exact L2|]. split; [exact SP|].
    split; [exact (RSV _ (proj1 (wf_env_thread _ WE)))|]. split; [exact (RSV _ (proj2 (proj2 (proj2 (proj2 (wf_env_resv _ WE))))))| exact (RSV _ (proj1 (wf_env_ptr _ WE)))].
Qed.

Lemma ldcW_avoid : forall P l (ai : astate) moi c usp,
  AWf E0 P l ai -> AKern E0 ai moi -> 1 <= c <= kLargestClassID -> ldcRM ai c ->
  Permutation (live_blocks a) ((cb + 16, n) :: live_blocks ai) -> alloc_ceiling <= lo -> lo <= usp - K_LDC ->
  Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv)
         (ldc_W E0 ai c usp).
Proof.
  intros P l ai moi c usp WF AK Hc [RM1 RM2] PL LOC' LOU. unfold K_LDC in LOU. pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof WF as (WE & WR & _). pose proof (wf_env_thread _ WE) as (_ & _ & WT & WT4 & _).
  destruct (proj2 WR c Hc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). cbv zeta in R1, R3, R5, R6, R7, R8. unfold region_of in R1, R3, R5, R6, R7, R8.
  pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as HR.
  unfold ldc_W. cbv zeta. unfold free_array, region_beg, ae_region_info.
  repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
    destruct (live_old_loc P l ai moi blo bsz WF AK PL LIVEb NEb) as (k & cmk & Hk & _ & B1 & B2 & N1 & W1 & W2 & LOCk); rewrite KHB, KLE in W2 |]); [.. | apply Forall_nil];
    unfold K_LDC, kThrStats, kThrCache, kThrCacheStats, kPerClassSize, kRegSize, kShadowBase, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize, kRegionSize, kSpaceSize, kPageSize, kResvLen, kPtrArrayLen, kLargestClassID in *;
    unfold rg_num_freed, zlen in *.
  - right; right. clear -LOU LOC' W1. lia.
  - right. destruct LOCk as [(c' & Hc' & L1 & L2 & G1 & G3)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)]; [clear -Hc Hc' L1 L2 G1 G3 B1 B2 WT4; lia| clear -Hc L1 L2 RT B1 B2; lia].
  - right. destruct LOCk as [(c' & Hc' & L1 & L2 & G1 & G3)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)]; [clear -Hc Hc' L1 L2 G1 G3 B1 B2 WT4; lia| clear -Hc L1 L2 RT B1 B2; lia].
  - right. destruct LOCk as [(c' & Hc' & L1 & L2 & G1 & G3)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)]; [clear -Hc Hc' L1 L2 G1 G3 B1 B2 WT4; lia| clear -Hc L1 L2 RT B1 B2; lia].
  - right. destruct LOCk as [(c' & Hc' & L1 & L2 & G1 & G3)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)]; [clear -Hc Hc' L1 L2 B1 B2; lia|].
    pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). unfold kSpaceSize, kPageSize, kResvLen in G3. clear -Hc L1 L2 RV B1 B2 G1 G3. lia.
  - right. destruct LOCk as [(c' & Hc' & L1 & L2 & G1 & G3)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)]; [clear -Hc Hc' L1 L2 B1 B2 R5 R8 HR RM2; lia| clear -Hc L1 L2 SP B1 B2 R5 R8 HR RM2; lia].
  - right. destruct LOCk as [(c' & Hc' & L1 & L2 & G1 & G3)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)]; [clear -Hc Hc' L1 L2 B1 B2 R5 RM1; lia| clear -Hc L1 L2 SP B1 B2 R5 RM1; lia].
  - right. pose proof (wf_env_resv _ WE) as (V1 & V2 & V3 & V4 & _). rewrite KHB in V1. unfold kSpaceSize in V3.
    clear -Hc W1 W2 B1 B2 N1 R5 RM1 V1 V2 V3 V4 CR. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition itemRM (ai : astate) (cmx : chunkmeta) : Prop :=
  match cm_prim cmx with
  | Some c => rg_mapped_fa (get_region ai c) + kFreeArrayMapSize <= kFreeArraySize /\ 4 * (rg_num_freed (get_region ai c) + hint c) <= kFreeArraySize
  | None => True end.

(* [comment removed for export] *)
Lemma itemW_awok : forall l (ai : astate) moi xc cmx usp,
  AWf E0 [] l ai -> AKern E0 ai moi -> as_chunks ai !! xc = Some cmx -> itemRM ai cmx -> (forall sc, In sc (as_sec ai) -> In sc (as_sec a)) ->
  (forall sc, In sc (as_sec ai) -> 0x603000 <= sc_map_beg sc) ->
  lo <= usp - K_ITEM -> usp <= U ->
  Forall (aw_ok E0 a a4 lo U) (item_W E0 ai xc cmx usp).
Proof.
  intros l ai moi xc cmx usp WF AK Hx RM SECi SECHI LOU UU. unfold K_ITEM in LOU. unfold itemRM in RM. pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof WF as (WE & WR & WC & [K1 _] & WQ & (S1 & S2 & S3 & S4 & S5) & WD).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _). rewrite KHB in WE2.
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (K1 _ _ Hx) as (ECB & KNr & ERZ & KP & _).
  pose proof (chunk_user_in_block E0 [] l ai xc cmx WF Hx) as (U1 & U2 & U3). unfold user_lo, user_hi, blk_lo, blk_hi, kChunkHeaderSize in U1, U2, U3.
  assert (TST : forall x y, T + kThrStats <= x -> y <= T + kThrStats + 368 -> aw_ok E0 a a4 lo U (x, y)).
  { intros x y H1 H2. unfold aw_ok. cbn [fst snd]. do 2 right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; clear -H1 H2; lia]. }
  unfold item_W. cbv zeta. destruct (cm_prim cmx) as [c|] eqn:PC.
  - destruct KP as (FP & Ec & CVc & _). pose proof (chunk_beg_loc E0 [] l ai xc cmx WF Hx) as CL. rewrite PC in CL. destruct CL as (Hc & _).
    pose proof (carved_in_space E0 ai c _ Hc WR CVc) as [Ic1 Ic2]. pose proof (carved_range E0 ai c _ Hc WR CVc) as [Jc1 Jc2].
    pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as [_ CSZ].
    assert (EXCL : forall z, SB <= z < SB + kSpaceSize -> sh_excluded E0 z = false) by (intros z Hz; exact (resv_excl [] l ai moi z WF AK Hz)).
    destruct RM as [RM1 RM2].
    apply Forall_app. split; [| apply Forall_app; split; [| exact (ldcW_awok [] l ai moi c usp WF AK Hc (conj RM1 RM2) ltac:(unfold K_LDC; clear -LOU; lia) UU)]].
    + apply Forall_cons; [unfold aw_ok; cbn [fst snd]; left; unfold K_ITEM; clear -LOU UU; lia|]. apply Forall_cons; [apply TST; unfold kThrStats; clear; lia| apply Forall_nil].
    + unfold region_beg, kFreeArrayOffset, kRegionSize, kSpaceSize, kLargestClassID in *.
      repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
      * do 3 right; left. change kResvLen with 137439023104. clear -G1 G3 Ic1 Ic2 U1 U2 U3 KNr. lia.
      * do 3 right; left. change kResvLen with 137439023104. clear -G1 G3 Ic1 Ic2 U1 U2 U3 KNr CSZ. lia.
      * do 8 right. split.
        -- right. rewrite KHB. unfold B_base.A_SB, kShadowBase. clear -G1 G3 Ic1 Ic2 Jc2 Hc U1 U2 U3 KNr WE2 WE3 WE5 CR. Z.div_mod_to_equations. lia.
        -- intros z Hz. apply EXCL. unfold B_base.A_SB, kShadowBase in Hz |- *. unfold kSpaceSize. clear -Hz Ic1 Ic2 Jc2 Hc U1 U2 U3 KNr. Z.div_mod_to_equations. lia.
  - destruct KP as (FP & sc0 & Hsc0 & Hab & Hms & _). destruct (S3 sc0 Hsc0) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). unfold kPageSize in M1, M5, Hab.
    pose proof (SECHI sc0 Hsc0) as A0HI.
    assert (SECNE : as_sec ai <> []) by (intros E; rewrite E in Hsc0; exact Hsc0).
    set (lsc := List.last (as_sec ai) sc0).
    assert (LASTIN : In lsc (as_sec ai)) by (subst lsc; apply BF_deallocT6.last_In; exact SECNE).
    assert (LB : last_beg ai = sc_map_beg lsc).
    { unfold last_beg. subst lsc. destruct (exists_last SECNE) as (l' & y & E). rewrite E. rewrite rev_app_distr. cbn [rev app]. rewrite (List.last_last l' y sc0). reflexivity. }
    destruct (S3 lsc LASTIN) as (_ & _ & _ & Ls4 & Ls5 & _). unfold kPageSize in Ls5.
    unfold kThrStats, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kChunksBlockCount. rewrite LB.
    Ltac inst := right; left; exists (aic_instance both_ic, 3632); split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear; lia].
    repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
    + left. unfold K_ITEM. clear -LOU UU. lia.
    + do 2 right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrStats; clear; lia].
    + inst. + inst. + inst. + inst.
    + do 4 right; left. unfold kPtrArrayLen. clear. lia.
    + do 5 right; left. exists lsc. split; [left; exact (SECi lsc LASTIN)| clear -Ls4 Ls5; Z.div_mod_to_equations; lia].
    + do 2 right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrStats; clear; lia].
    + do 8 right. rewrite Hab, <- Hms. replace (sc_map_beg sc0 + 4096 - 4096) with (sc_map_beg sc0) by (clear; lia). split.
      -- unfold app_mem in M2. rewrite KHB, KLE in M2. rewrite KHB, KLE. unfold B_base.A_SB, kShadowBase, LSHI.
         clear -M1 M2 M3 M4 M5 A0HI CR. Z.div_mod_to_equations. lia.
      -- intros z Hz. unfold B_base.A_SB, kShadowBase in Hz. pose proof (M7 _ (proj1 (wf_env_fs _ WE))) as Xfs. pose proof (M7 _ (proj1 (wf_env_iarena _ WE))) as Xia.
         pose proof (M7 _ (proj2 (proj2 (proj2 (proj2 (wf_env_resv _ WE)))))) as Xrs. cbn [fst snd] in Xfs, Xia, Xrs.
         apply sh_excluded_false; unfold B_base.A_SB; unfold kIArenaLen, kSpaceSize, kPageSize in *; clear -Hz M1 M4 M5 Xfs Xia Xrs G1 G3; Z.div_mod_to_equations; lia.
    + do 5 right; left. exists sc0. rewrite Hab, <- Hms. split; [left; exact (SECi sc0 Hsc0)| unfold kPageSize; clear -M4; lia].
Qed.

(* [comment removed for export] *)
Lemma itemW_avoid : forall l (ai : astate) moi xc cmx qi qj usp,
  AWf E0 [] l ai -> AKern E0 ai moi -> as_chunks ai !! xc = Some cmx -> cm_state cmx = CQuarantined qi qj -> itemRM ai cmx ->
  (forall sc, In sc (as_sec ai) -> 0x603000 <= sc_map_beg sc) ->
  Permutation (live_blocks a) ((cb + 16, n) :: live_blocks ai) -> alloc_ceiling <= lo -> lo <= usp - K_ITEM ->
  Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv)
         (item_W E0 ai xc cmx usp).
Proof.
  intros l ai moi xc cmx qi qj usp WF AK Hx STx RM SECHI PL LOC' LOU. unfold K_ITEM in LOU. unfold itemRM in RM.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof WF as (WE & WR & WC & [K1 _] & WQ & (S1 & S2 & S3 & S4 & S5) & WD).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _). rewrite KHB in WE2. pose proof (wf_env_thread _ WE) as (_ & _ & WT & WT4 & _). pose proof (wf_env_ptr _ WE) as (_ & _ & PAB & PAR & _).
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  pose proof (hsb_of [] l ai WF) as (HSB1 & _).
  destruct (K1 _ _ Hx) as (ECB & KNr & ERZ & KP & _).
  pose proof (chunk_user_in_block E0 [] l ai xc cmx WF Hx) as (U1 & U2 & U3). unfold user_lo, user_hi, blk_lo, blk_hi, kChunkHeaderSize in U1, U2, U3.
  (* [comment removed for export] *)
  assert (OLD : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) ->
            exists k cmk, as_chunks ai !! k = Some cmk /\ blk_lo cmk + 16 <= blo /\ blo + bsz <= blk_hi ai cmk /\ 1 <= bsz
            /\ blo + bsz <= alloc_ceiling /\ (blo + bsz <= 0x7fff7000 \/ 0x10007fff8000 <= blo)
            /\ (blk_hi ai cmx <= blk_lo cmk \/ blk_hi ai cmk <= blk_lo cmx)
            /\ ((exists c', 1 <= c' <= kLargestClassID /\ SB + c' * kRegionSize <= blk_lo cmk /\ blk_hi ai cmk <= SB + c' * kRegionSize + kFreeArrayOffset
                             /\ ae_resv_beg E0 <= SB /\ SB + kSpaceSize + kPageSize <= ae_resv_beg E0 + kResvLen)
                \/ (exists sc, In sc (as_sec ai) /\ blk_lo cmk = sc_map_beg sc + kPageSize /\ blk_hi ai cmk = sc_map_beg sc + sc_map_size sc
                       /\ (sc_map_beg sc + sc_map_size sc <= SB \/ SB + kSpaceSize <= sc_map_beg sc)
                       /\ (sc_map_beg sc + sc_map_size sc <= T \/ T + 4096 <= sc_map_beg sc)
                       /\ (sc_map_beg sc + sc_map_size sc <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= sc_map_beg sc)
                       /\ (sc_map_beg sc + sc_map_size sc <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= sc_map_beg sc)))).
  { intros blo bsz LIVEb NEb. destruct (live_old_loc [] l ai moi blo bsz WF AK PL LIVEb NEb) as (k & cmk & Hk & [ik STk] & B1 & B2 & N1 & W1 & W2 & LOCk).
    rewrite KHB, KLE in W2. exists k, cmk.
    assert (NEk : xc <> k) by (intros <-; rewrite Hx in Hk; injection Hk as <-; rewrite STx in STk; discriminate).
    pose proof (AsanClient.chunks_disjoint E0 [] l ai xc cmx k cmk WF Hx Hk NEk) as DJ.
    repeat (split; [assumption|]). exact LOCk. }
  assert (TIV : forall x y blo bsz, T <= x -> y <= T + 4096 -> In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> y <= x \/ y <= blo \/ blo + bsz <= x).
  { intros x y blo bsz H1 H2 LIVEb NEb. destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & W2 & DJ & LOCk). right.
    destruct LOCk as [(c' & Hc' & L1 & L2 & R1 & R2)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)];
      unfold kRegionSize, kFreeArrayOffset, kSpaceSize, kPageSize, kResvLen, kLargestClassID in *; [clear -H1 H2 B1 B2 L1 L2 R1 R2 Hc' WT4; lia| clear -H1 H2 B1 B2 L1 L2 RT; lia]. }
  unfold item_W. cbv zeta. destruct (cm_prim cmx) as [c|] eqn:PC.
  - destruct KP as (FP & Ec & CVc & _). pose proof (chunk_beg_loc E0 [] l ai xc cmx WF Hx) as CL. rewrite PC in CL. destruct CL as (Hc & _).
    destruct RM as [RM1 RM2].
    apply Forall_app. split; [| apply Forall_app; split; [| exact (ldcW_avoid [] l ai moi c usp WF AK Hc (conj RM1 RM2) PL LOC' ltac:(unfold K_LDC; clear -LOU; lia))]].
    + apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; intros blo bsz LIVEb NEb.
      * destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & _). right; right. unfold K_ITEM. clear -LOU LOC' W1. lia.
      * apply TIV; [unfold kThrStats; clear; lia| unfold kThrStats; clear; lia| exact LIVEb| exact NEb].
    + unfold blk_lo, blk_hi in OLD.
      repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb; destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & W2 & DJ & _)|]); [.. | apply Forall_nil].
      * right. rewrite PC in DJ. clear -B1 B2 N1 DJ U1 U2 U3 KNr. lia.
      * right. rewrite PC in DJ. clear -B1 B2 N1 DJ U1 U2 U3 KNr. lia.
      * right. pose proof (carved_in_space E0 ai c _ Hc WR CVc) as [Ic1 Ic2]. pose proof (carved_range E0 ai c _ Hc WR CVc) as [Jc1 Jc2].
        unfold region_beg, kFreeArrayOffset, kRegionSize, kSpaceSize, kLargestClassID, kShadowBase in *.
        clear -B1 B2 N1 W1 W2 Ic1 Ic2 Jc2 Hc U1 U2 U3 KNr G1 G3 WE2 WE5 CR. Z.div_mod_to_equations. lia.
  - destruct KP as (FP & sc0 & Hsc0 & Hab & Hms & _). destruct (S3 sc0 Hsc0) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). unfold kPageSize in M1, M5, Hab.
    pose proof (SECHI sc0 Hsc0) as A0HI.
    assert (SECNE : as_sec ai <> []) by (intros E; rewrite E in Hsc0; exact Hsc0).
    set (lsc := List.last (as_sec ai) sc0).
    assert (LASTIN : In lsc (as_sec ai)) by (subst lsc; apply BF_deallocT6.last_In; exact SECNE).
    assert (LB : last_beg ai = sc_map_beg lsc).
    { unfold last_beg. subst lsc. destruct (exists_last SECNE) as (l' & y & E). rewrite E. rewrite rev_app_distr. cbn [rev app]. rewrite (List.last_last l' y sc0). reflexivity. }
    destruct (S3 lsc LASTIN) as (_ & _ & _ & Ls4 & Ls5 & Ls6 & _). unfold kPageSize in Ls5. pose proof (SECHI lsc LASTIN) as LHI.
    unfold kThrStats, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kChunksBlockCount. rewrite LB. rewrite Hab, <- Hms.
    replace (sc_map_beg sc0 + 4096 - kPageSize) with (sc_map_beg sc0) by (unfold kPageSize; clear; lia).
    unfold blk_lo, blk_hi in OLD. rewrite Hab, <- Hms in OLD.
    assert (OLDlo : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> 0x603000 <= blo /\ blo + bsz <= alloc_ceiling).
    { intros blo bsz LIVEb NEb. destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & W2 & DJ & LOCk). split; [| exact W1].
      destruct LOCk as [(c' & Hc' & L1 & L2 & R1 & R2)|(sc & Hsc & L1 & L2 & _)]; [unfold kRegionSize in L1; clear -B1 L1 HSB1 Hc'; lia|].
      pose proof (SECHI sc Hsc). unfold kPageSize in L1. clear -B1 L1 H. lia. }
    repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb|]); [.. | apply Forall_nil].
    + destruct (OLDlo blo bsz LIVEb NEb) as [O1 O2]. right; right. unfold K_ITEM. clear -LOU LOC' O2. lia.
    + apply TIV; [clear; lia| clear; lia| exact LIVEb| exact NEb].
    + destruct (OLDlo blo bsz LIVEb NEb) as [O1 O2]. right; left. clear -O1. lia.
    + destruct (OLDlo blo bsz LIVEb NEb) as [O1 O2]. right; left. clear -O1. lia.
    + destruct (OLDlo blo bsz LIVEb NEb) as [O1 O2]. right; left. clear -O1. lia.
    + destruct (OLDlo blo bsz LIVEb NEb) as [O1 O2]. right; left. clear -O1. lia.
    + destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & W2 & DJ & LOCk). right.
      destruct LOCk as [(c' & Hc' & L1 & L2 & R1 & R2)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)];
        unfold kRegionSize, kFreeArrayOffset, kSpaceSize, kPageSize, kResvLen, kPtrArrayLen, kLargestClassID in *; [clear -B1 B2 N1 L1 L2 Hc' R1 R2 PAR; lia| clear -B1 B2 N1 L1 L2 RP; lia].
    + destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & W2 & DJ & LOCk). right.
      destruct LOCk as [(c' & Hc' & L1 & L2 & R1 & R2)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)].
      * pose proof (carved_in_space E0 ai kBatchClass) as _x. clear _x.
        unfold kRegionSize, kFreeArrayOffset, kSpaceSize, kPageSize, kResvLen, kLargestClassID in *. clear -B1 B2 N1 L1 L2 Hc' Ls4 Ls5 Ls6. lia.
      * destruct (Z.eq_dec (sc_map_beg sc) (sc_map_beg lsc)) as [EQ|NE'].
        -- pose proof (AsanWf8.NoDup_map_inj_In _ _ _ _ S4 Hsc LASTIN EQ) as ->. unfold kPageSize in L1. clear -B1 B2 N1 L1 L2. lia.
        -- destruct (S5 sc lsc Hsc LASTIN ltac:(intros ->; exact (NE' eq_refl))) as [D|D]; unfold kPageSize in L1; clear -B1 B2 N1 L1 L2 D Ls4 Ls5; lia.
    + apply TIV; [clear; lia| clear; lia| exact LIVEb| exact NEb].
    + destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & W2 & DJ & LOCk). right. unfold kShadowBase.
      clear -B1 B2 N1 W1 W2 M3 M4 A0HI CR. Z.div_mod_to_equations. lia.
    + destruct (OLD blo bsz LIVEb NEb) as (k & cmk & Hk & B1 & B2 & N1 & W1 & W2 & DJ & LOCk). right.
      destruct LOCk as [(c' & Hc' & L1 & L2 & R1 & R2)|(sc & Hsc & L1 & L2 & SP & RT & RV & RP)].
      * unfold kRegionSize, kFreeArrayOffset, kSpaceSize, kPageSize, kResvLen, kLargestClassID in *. clear -B1 B2 N1 L1 L2 Hc' M4 M6. lia.
      * destruct (Z.eq_dec (sc_map_beg sc) (sc_map_beg sc0)) as [EQ|NE'].
        -- pose proof (AsanWf8.NoDup_map_inj_In _ _ _ _ S4 Hsc Hsc0 EQ) as ->. exfalso. rewrite PC in DJ. unfold kPageSize in L1, L2, DJ.
           pose proof (map_size_facts (cm_n cmx)) as (_ & _ & M2P). unfold kPageSize in M2P. rewrite <- Hms in M2P. clear -DJ L1 L2 B1 B2 N1 M2P. lia.
        -- destruct (S5 sc sc0 Hsc Hsc0 ltac:(intros ->; exact (NE' eq_refl))) as [D|D]; unfold kPageSize in L1; clear -B1 B2 N1 L1 L2 D M4; lia.
Qed.

(* [comment removed for export] *)
Lemma item_sstats : forall (ai a' : astate) xc cmx, sstats_ok ai -> item_same ai a' xc cmx -> sstats_ok a'.
Proof.
  intros ai a' xc cmx [S1 S2] [SC SP]. unfold sstats_ok, sec_bytes in *. rewrite !fold_right_sumZ in *.
  destruct (cm_prim cmx).
  - destruct SP as (E1 & E2 & _). rewrite E1, E2. split; [exact S1| exact S2].
  - destruct SP as (sc & Hsc & _ & _ & PM & C1 & C2 & _). rewrite C1, C2, S1. rewrite <- (sumZ_perm _ _ _ PM). cbn [sumZ]. unfold sumZ. cbn [fold_right]. split; [clear; lia| exact S2].
Qed.
Lemma csmall_delete : forall (ai a' : astate) xc, csmall ai -> as_chunks a' = delete xc (as_chunks ai) -> csmall a'.
Proof.
  intros ai a' xc CS E k cmk Hk. rewrite E in Hk. rewrite lookup_delete in Hk. destruct (decide (xc = k)); [discriminate|]. exact (CS k cmk Hk).
Qed.

Lemma skipn_nth_cons : forall {X} (l : list X) i w, nth_error l i = Some w -> skipn i l = w :: skipn (Datatypes.S i) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] w H; cbn in H |- *; try discriminate; [injection H as ->; reflexivity|]. apply IH. exact H.
Qed.
Lemma firstn_succ_snoc : forall {X} (l : list X) i w, nth_error l i = Some w -> firstn (Datatypes.S i) l = firstn i l ++ [w].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] w H; cbn in H |- *; try discriminate; [injection H as ->; reflexivity|]. rewrite (IH i w H). reflexivity.
Qed.

Ltac agh H AG := eapply (rw_cells_agree bsegs _ _); [| exact H]; cbn; intros z Hz; apply AG.
Ltac agw H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn].

(* [comment removed for export] *)
Lemma item_step : forall b rest ws j8 (i : Z) ai mi moi (it : word) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  length ws = 1021%nat -> (forall k x, nth_error (b_items b) k = Some x -> nth_error ws k = Some (wz x)) ->
  0 <= i < bcnt b -> nth_error ws (Z.to_nat i) = Some it ->
  IINV b rest ws j8 i ai mi moi -> stk bsegs mi lo (U - 160 + -112) ->
  (forall aj mj moj (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     IINV b rest ws j8 (i + 1) aj mj moj -> stk bsegs mj lo (U - 160 + -112) ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR (wz 0x34bf0) (wz (U - 160 + -112)) gp tp t0' t1' t2' (wz (U - 160)) (wz INST) a0' a1' a2' a3' a4' a5' a6' a7'
                     (wz 0xaaf98) (wz 0xab208) (wz (b_addr b)) (wz (2^37)) (wz (bcnt b)) (wz (b_addr b + 152 + 8 * i)) (wz (bcnt b + 16)) (wz (16 + i)) s10 s11 t3' t4' t5' t6')
                     F (wz 0x34bf0) fc None mj (seg_rom bsegs)) moj) K) ->
  realizes_cfg acfg bsegs (mkCfg (drl_call gp tp s10 s11 F fc (U - 160) (U - 160) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (b_addr b) (bcnt b) i it mi) moi) K.
Proof.
  intros until xt6. intros LWS WSI HI HIT II SK KI.
  destruct II as (WF & REP & AK & RES & DI & SS & CS & HBI & TQ & GQ & TOK & Ffs & Ffds & Ftid & Enp & Eres & Endi & Enb & Esb & SECi & PLIVE & RLIVE & ILIVE & GONE & RUNK
                  & MI & RT & PF & TC & FRR & FLO & FCB & FHI & BH & BWS & BC & BIT & BOK & BAP & QBYT & (W & MU & AWOK & AVOID)).
  pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  pose proof AIV as (_ & Hwf & _). pose proof FB as (BU1 & BU2 & BU3). unfold kInitialCredit in BU3.
  assert (NP12 : 0 <= as_nprim_ever ai <= 12000) by (rewrite Enp; clear -BU1 BU2 BU3; lia).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 (sA ai s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  (* [comment removed for export] *)
  set (ni := Z.to_nat i) in *.
  destruct (nth_error (b_items b) ni) as [x|] eqn:NX.
  2:{ exfalso. apply nth_error_None in NX. subst ni. clear -NX HI. lia. }
  rewrite (WSI _ _ NX) in HIT. injection HIT as <-.
  pose proof (skipn_nth_cons _ _ _ NX) as SKx.
  destruct (ILIVE x ltac:(rewrite SKx; left; reflexivity)) as (cmx & qi & qj & Hx & STx).
  pose proof WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  assert (XIN : In x (b_items b)) by exact (nth_error_In _ _ NX).
  assert (NB : ~ In (b_addr b) (map b_addr (as_tq ai ++ as_gq ai) ++ map b_addr rest)).
  { pose proof Q2 as Q2'. unfold all_batches in Q2'. rewrite app_assoc, map_app in Q2'. cbn [map] in Q2'. exact (proj2 (NoDup_remove _ _ _ Q2')). }
  assert (NIB : forall b0, In b0 (as_tq ai ++ as_gq ai) -> ~ In x (b_items b0)).
  { intros b0 Hb0 Hin.
    assert (A1 : In b0 (all_batches (b :: rest) ai)) by (unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb0).
    assert (A2 : In b (all_batches (b :: rest) ai)) by (unfold all_batches; rewrite app_assoc; apply in_app_iff; right; left; reflexivity).
    pose proof (Q3 b0 b x A1 A2 Hin XIN) as ->. apply NB. apply in_app_iff. left. apply in_map. exact Hb0. }
  (* [comment removed for export] *)
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  assert (GAPR : kFreeArrayMapSize <= gapR ai).
  { pose proof (M2_sharp_BI _ _ ai HBI) as M. unfold gapR, kBatchPages, kFreeArrayMapSize. clear -M. lia. }
  assert (RMX : itemRM ai cmx /\ match cm_prim cmx with Some c => rg_mapped_fa (get_region ai c) + kFreeArrayMapSize <= kFreeArraySize | None => True end).
  { unfold itemRM. destruct (cm_prim cmx) as [c|] eqn:PC; [| split; exact I].
    pose proof (chunk_beg_loc E0 [] (b :: rest) ai x cmx WF Hx) as CL. rewrite PC in CL. destruct CL as (Hc & _).
    pose proof (rooms_of_BI E0 [] (b :: rest) _ _ ai c WF HBI Hc NP12) as (Rm1 & Rm2 & Rm3 & Rm4). cbv zeta in Rm1, Rm2, Rm3, Rm4.
    pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as HR.
    destruct (proj2 WR c Hc) as (Rg1 & _). cbv zeta in Rg1. unfold region_of in Rg1. pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; clear -Hc; lia)) as [_ CSZ].
    assert (QN : 0 <= (rg_mapped_user (get_region ai c) + kUserMapSize - rg_alloc_user (get_region ai c)) / class_size c) by (apply Z.div_pos; [unfold kUserMapSize; clear -Rg1; lia| clear -CSZ; lia]).
    split; [| exact Rm4]. split; [exact Rm4|]. unfold kFreeArrayMapSize, kFreeArraySize in *. clear -Rm2 HR QN. lia. }
  destruct RMX as [RM RFA].
  (* [comment removed for export] *)
  unfold drl_call. unfold drl_fr_cb in FCB.
  assert (POSTK : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     item_post E0 FSB0 HR0 L0 RES0 EB0 PL0 (b :: rest) ai a' x cmx mi m' moi mo' (sA ai s) (C - 1) (C' - DSLACK) lo (U - 160 + -112) ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR (wz 0x34bf0) (wz (U - 160 + -112)) gp tp t0' t1' t2' (wz (U - 160)) (wz INST) a0' a1' a2' a3' a4' a5' a6' a7'
                     (wz 0xaaf98) (wz 0xab208) (wz (b_addr b)) (wz (2^37)) (wz (bcnt b)) (wz (b_addr b + 152 + 8 * i)) (wz (bcnt b + 16)) (wz (16 + i)) s10 s11 t3' t4' t5' t6')
                     F (ret_pc (wz 0x34bf0)) fc None m' (seg_rom bsegs)) mo') K).
  2:{ destruct (cm_prim cmx) as [c|] eqn:PC.
      - eapply (ITEMP (wz 0x34bf0) gp tp xt0 xt1 xt2 (wz (U - 160)) (wz INST) xa2 xa3 xa4 xa5 xa6 xa7
                  (wz 0xaaf98) (wz 0xab208) (wz (b_addr b)) (wz (2^37)) (wz (bcnt b)) (wz (b_addr b + 152 + 8 * i)) (wz (bcnt b + 16)) (wz (16 + i)) s10 s11 xt3 xt4 xt5 xt6
                  (wz B) F fc mi moi (sA ai s) (b :: rest) cmx x c qi qj (U - 160 + -104) lo (U - 160 + -112) (C - 1) (C' - DSLACK) K KN TOK);
          cbn [aps_alloc sA aps_set_alloc];
          [exact REP| exact WF| exact AK| exact RES| exact MI| exact RT| exact Hx| exact STx| exact PC| exact NIB| exact GAPR| exact RFA| exact SK| exact LOC
          | unfold K_ITEM; clear -LO; lia| clear -SPA; Z.div_mod_to_equations; lia| clear -SPH; lia| exact TP| clear; lia| clear -SPH; lia| unfold kThrCache; exact FCB| exact POSTK].
      - eapply (ITEMS (wz 0x34bf0) gp tp xt0 xt1 xt2 (wz (U - 160)) (wz INST) xa2 xa3 xa4 xa5 xa6 xa7
                  (wz 0xaaf98) (wz 0xab208) (wz (b_addr b)) (wz (2^37)) (wz (bcnt b)) (wz (b_addr b + 152 + 8 * i)) (wz (bcnt b + 16)) (wz (16 + i)) s10 s11 xt3 xt4 xt5 xt6
                  (wz B) F fc mi moi (sA ai s) (b :: rest) cmx x qi qj (U - 160 + -104) lo (U - 160 + -112) (C - 1) (C' - DSLACK) K KN TOK);
          cbn [aps_alloc sA aps_set_alloc];
          [exact REP| exact WF| exact AK| exact RES| exact MI| exact RT| exact Hx| exact STx| exact PC| exact NIB
          | exact (sechi_of E0 [] (b :: rest) ai _ _ WF HBI EI1 EI2)| exact (ci_of_batch E0 [] (b :: rest) ai b WF (or_introl eq_refl))
          | exact SK| exact LOC| unfold K_ITEM; clear -LO; lia| clear -SPA; Z.div_mod_to_equations; lia| clear -SPH; lia| exact TP| clear; lia| clear -SPH; lia| unfold kThrCache; exact FCB| exact POSTK]. }
  (* [comment removed for export] *)
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' a' POST. rewrite (ret_pc_even 0x34bf0) by (clear; lia).
  destruct POST as (RUN' & REP' & WF' & AK' & TOK' & Ffs' & Ffds' & Ftid' & SK' & MI' & RT' & MU' & SAME').
  rewrite BF_popT.sA_sA in TOK'. pose proof SAME' as [SC _].
  pose proof SC as (Xch & Xtq & Xgq & Xptr & Xnp & Xres & Xev & Xnd & Xnb & Xsb & Xks & Xfr & Xst & Xci & Xcm & Xia & Xoom & Xrg & Xfa & Xrb & Xlive).
  destruct RUN' as (fr & orr & evr & orr' & RUN'). destruct (arun_orc_app2 _ _ _ _ _ _ _ RUN') as (ur & _ & Rr). pose proof (Rr []) as RUNx. rewrite app_nil_r in RUNx.
  assert (AGH : forall z, U - 160 + -112 <= z < 2^64 -> m' (wa z) = mi (wa z))
    by exact (itemW_high_agree (b :: rest) ai moi x cmx (U - 160 + -112) mi m' WF AK Hx RM LOC ltac:(clear -LO; lia) MU').
  assert (AGB : forall b', In b' (b :: rest) -> forall z, b_addr b' <= z < b_addr b' + 8192 -> m' (wa z) = mi (wa z)).
  { intros b' Hb'. apply (itemW_batch_agree (b :: rest) ai moi x cmx (U - 160 + -112) mi m' b' WF AK Hx RM); [| exact (proj1 (Forall_forall _ _) BOK b' Hb')| exact LOC| unfold K_ITEM; clear -LO; lia| clear -SPH; lia| exact MU'].
    apply in_app_iff. right. exact Hb'. }
  assert (Hni1 : Z.to_nat (i + 1) = Datatypes.S ni) by (subst ni; clear -HI; lia).
  apply (KI a' m' mo'); [| exact SK']. unfold IINV. rewrite Hni1. rewrite (firstn_succ_snoc _ _ _ NX). rewrite SKx in RUNK.
  split; [exact WF'|]. split; [exact REP'|]. split; [exact AK'|].
  split; [exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (qcb_recycle_res E0 x) RES RUNx)|].
  split; [exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (qcb_recycle_di E0 x) DI RUNx)|].
  split; [exact (item_sstats ai a' x cmx SS SAME')|]. split; [exact (csmall_delete ai a' x CS Xch)|].
  split; [exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (qcb_recycle_cnt E0 _ _ ai x HBI) eq_refl RUNx)|].
  split; [rewrite Xtq; exact TQ|]. split; [unfold gq_bytes; rewrite Xgq; exact GQ|]. split; [exact TOK'|].
  split; [rewrite Ffs'; exact Ffs|]. split; [rewrite Ffds'; exact Ffds|]. split; [rewrite Ftid'; exact Ftid|].
  split; [rewrite Xnp; exact Enp|]. split; [rewrite Xres; exact Eres|]. split; [rewrite Xnd; exact Endi|]. split; [rewrite Xnb; exact Enb|]. split; [rewrite Xsb; exact Esb|].
  split. { intros sc Hsc. apply SECi. pose proof SAME' as [_ SP]. destruct (cm_prim cmx); [destruct SP as (E1 & _); rewrite <- E1; exact Hsc|].
           destruct SP as (sc0 & _ & _ & _ & PM & _). eapply Permutation_in; [exact PM| right; exact Hsc]. }
  split; [etransitivity; [exact PLIVE| apply perm_skip; symmetry; exact Xlive]|].
  split. { intros b' Hb' y Hy. destruct (RLIVE b' Hb' y Hy) as (cmy & iy & jy & Hcy & STy). exists cmy, iy, jy. split; [| exact STy].
           rewrite Xch. rewrite lookup_delete_ne; [exact Hcy|]. intros ->.
           assert (A1 : In b' (all_batches (b :: rest) ai)) by (unfold all_batches; rewrite app_assoc; apply in_app_iff; right; right; exact Hb').
           assert (A2 : In b (all_batches (b :: rest) ai)) by (unfold all_batches; rewrite app_assoc; apply in_app_iff; right; left; reflexivity).
           pose proof (Q3 b' b y A1 A2 Hy XIN) as E. apply NB. apply in_app_iff. right. rewrite <- E. apply in_map. exact Hb'. }
  split. { intros y Hy. destruct (ILIVE y ltac:(rewrite SKx; right; exact Hy)) as (cmy & iy & jy & Hcy & STy). exists cmy, iy, jy. split; [| exact STy].
           rewrite Xch. rewrite lookup_delete_ne; [exact Hcy|]. intros <-. destruct (QD b (or_introl eq_refl)) as (_ & _ & _ & _ & NDb).
           clear -NDb SKx Hy. assert (ND' : List.NoDup (skipn ni (b_items b))).
           { clear -NDb. revert NDb. generalize (b_items b). induction ni as [|k IH]; intros l ND; [exact ND|]. destruct l as [|z l]; [constructor|]. cbn. apply IH. inversion ND; assumption. }
           rewrite SKx in ND'. inversion ND' as [|? ? NI _]; subst. exact (NI Hy). }
  split. { intros y Hy. rewrite Xch. apply in_app_iff in Hy. destruct Hy as [Hy|[<-|[]]].
           - rewrite lookup_delete. destruct (decide (x = y)); [reflexivity| exact (GONE y Hy)].
           - apply lookup_delete_eq. }
  split. { intros a1 f1 o1 e1 R1. destruct (arun_recycle_items_cons E0 x (skipn (Datatypes.S ni) (b_items b)) ai a' fr ur evr f1 o1 _ RUNx R1) as (f' & e' & R'). cbn [fst snd] in R'.
           exact (RUNK a1 f' (ur ++ o1) e' R'). }
  split; [exact MI'|]. split; [exact RT'|].
  split; [unfold put_frame in PF |- *; rewrite HU in PF |- *; agh PF AGH; clear -Hz LO SPH; lia|].
  split; [unfold tmpc in TC |- *; agh TC AGH; clear -Hz LO SPH; lia|].
  split; [agh FRR AGH; clear -Hz LO SPH; lia|].
  split; [unfold drl_fr_lo in FLO |- *; agh FLO AGH; clear -Hz LO SPH; lia|].
  split; [unfold drl_fr_cb; agh FCB AGH; clear -Hz LO SPH; lia|].
  split; [unfold drl_fr_hi in FHI |- *; agh FHI AGH; clear -Hz LO SPH; lia|].
  split; [agh BH (AGB b (or_introl eq_refl)); clear -Hz; lia|].
  split; [eapply (u64arr_agree mi m'); [| exact BWS]; rewrite LWS; intros z Hz; apply (AGB b (or_introl eq_refl)); clear -Hz; lia|].
  split; [eapply bcellsn_agree; [exact BC| intros b' z Hb' Hz; apply (AGB b' (or_intror Hb')); clear -Hz; lia]|].
  split; [eapply bitemsl_agree; [exact BIT| intros b' z Hb' Hz; apply (AGB b' (or_intror Hb')); clear -Hz; lia]|].
  split; [exact BOK|]. split; [exact BAP|]. split; [exact QBYT|].
  exists (W ++ item_W E0 ai x cmx (U - 160 + -112)). split; [| split; apply Forall_app; split; [exact AWOK| | exact AVOID|]].
  - eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']]; intros z Hz;
      apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin.
  - exact (itemW_awok (b :: rest) ai moi x cmx (U - 160 + -112) WF AK Hx RM SECi (sechi_of E0 [] (b :: rest) ai _ _ WF HBI EI1 EI2) ltac:(unfold K_ITEM; clear -LO; lia) ltac:(clear; lia)).
  - exact (itemW_avoid (b :: rest) ai moi x cmx qi qj (U - 160 + -112) WF AK Hx STx RM (sechi_of E0 [] (b :: rest) ai _ _ WF HBI EI1 EI2) PLIVE LOC ltac:(unfold K_ITEM; clear -LO; lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma glue_pols : forall l (ai : astate) moi,
  AWf E0 [] l ai -> AKern E0 ai moi -> RTOKc (C - 1) (C' - DSLACK) (sA ai s) moi ->
  let P := PP (sA ai s) moi in
     KIP (aSc (sA ai s)) (aNc (sA ai s)) (aEBc (sA ai s)) P moi
  /\ (forall y k, lo <= y -> y + Z.of_nat k <= U - 160 -> P (Z_to_bv 64 y, k))
  /\ (forall y k, U - 160 <= y -> y + Z.of_nat k <= U - 160 + 32 -> P (Z_to_bv 64 y, k))
  /\ (forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 y, k))
  /\ (forall b', In b' ((as_tq ai ++ as_gq ai) ++ l) -> forall y k, b_addr b' <= y -> y + Z.of_nat k <= b_addr b' + 8192 -> P (Z_to_bv 64 y, k)).
Proof.
  intros l ai moi WF AK TOK. cbv zeta. pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 (sA ai s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof WF as (WE & WR & _ & _ & WQ & _). assert (AKs : AKern E0 (aps_alloc (sA ai s)) moi) by exact AK.
  split; [exact (BF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA ai s) moi R0 R0' ATK)|].
  split; [intros y k H1 H2; unfold BF_caT.PP; apply (pol_stack' E0 FSB0 HR0 (sA ai s) moi AKs WE ENV0); clear -H1 H2 LOC SPH CR; lia|].
  split; [intros y k H1 H2; unfold BF_caT.PP; apply (pol_stack' E0 FSB0 HR0 (sA ai s) moi AKs WE ENV0); clear -H1 H2 LOC LO SPH CR; lia|].
  split; [intros y k H1 H2; unfold BF_caT.PP; apply (pol_img' E0 FSB0 HR0 (sA ai s) moi AKs WE ENV ENV0); clear -H1 H2; lia|].
  intros b' Hb' y k H1 H2. destruct k as [|k']; [apply acc_ok_empty|]. unfold BF_caT.PP.
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  destruct (batch_block E0 l ai b' WQ ltac:(unfold all_batches; rewrite app_assoc; exact Hb')) as ((q & Q0 & QE & QB) & _).
  destruct (proj2 WR kBatchClass HB24) as (Rg1 & _). cbv zeta in Rg1. unfold region_of in Rg1, QB. change (class_size kBatchClass) with 8192 in QE, QB.
  apply (pol_user E0 FSB0 HR0 (sA ai s) moi [] l AKs WF kBatchClass y (Datatypes.S k') HB24); [| | clear; lia]; cbn [aps_alloc sA aps_set_alloc]; clear -H1 H2 Q0 QE QB Rg1; nia.
Qed.


Lemma IINV_magree : forall b rest ws j8 i ai mi moi mo',
  IINV b rest ws j8 i ai mi moi -> magree moi mo' -> KIA (aSc (sA ai s)) (aNc (sA ai s)) (aEBc (sA ai s)) mo' -> IINV b rest ws j8 i ai mi mo'.
Proof.
  intros b rest ws j8 i ai mi moi mo' II AG KIA'. pose proof (magree_frame _ _ AG) as (Ffds9 & Fvm9 & Flz9 & Ffs9 & Fh9 & Ftid9 & _).
  destruct II as (WF & REP & AK & RES & DI & SS & CS & HBI & TQ & GQ & TOK & Ffs & Ffds & Ftid & REST).
  split; [exact WF|]. split; [exact REP|]. split; [exact (AKern_frame _ _ _ _ Fvm9 Flz9 AK)|]. split; [exact RES|]. split; [exact DI|]. split; [exact SS|]. split; [exact CS|].
  split; [exact HBI|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG KIA')|].
  split; [rewrite Ffs9; exact Ffs|]. split; [rewrite Ffds9; exact Ffds|]. split; [rewrite Ftid9; exact Ftid|]. exact REST.
Qed.

Lemma LINV_magree : forall l ai mi moi mo',
  LINV l ai mi moi -> magree moi mo' -> KIA (aSc (sA ai s)) (aNc (sA ai s)) (aEBc (sA ai s)) mo' -> LINV l ai mi mo'.
Proof.
  intros l ai mi moi mo' LI AG KIA'. pose proof (magree_frame _ _ AG) as (Ffds9 & Fvm9 & Flz9 & Ffs9 & Fh9 & Ftid9 & _).
  destruct LI as (WF & REP & AK & RES & DI & SS & CS & HBI & TQ & GQ & TOK & Ffs & Ffds & Ftid & REST).
  split; [exact WF|]. split; [exact REP|]. split; [exact (AKern_frame _ _ _ _ Fvm9 Flz9 AK)|]. split; [exact RES|]. split; [exact DI|]. split; [exact SS|]. split; [exact CS|].
  split; [exact HBI|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG KIA')|].
  split; [rewrite Ffs9; exact Ffs|]. split; [rewrite Ffds9; exact Ffds|]. split; [rewrite Ftid9; exact Ftid|]. exact REST.
Qed.

(* [comment removed for export] *)
Lemma items_loop : forall (kk : nat) b rest ws j8 (i : Z) ai mi moi (it : word) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  kk = Z.to_nat (bcnt b - i) ->
  length ws = 1021%nat -> (forall k x, nth_error (b_items b) k = Some x -> nth_error ws k = Some (wz x)) ->
  0 <= i < bcnt b -> nth_error ws (Z.to_nat i) = Some it ->
  IINV b rest ws j8 i ai mi moi -> stk bsegs mi lo (U - 160 + -112) ->
  (forall aj mj moj (xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' : word),
      IINV b rest ws j8 (bcnt b) aj mj moj -> stk bsegs mj lo (U - 160 + -112) ->
      realizes_cfg acfg bsegs (mkCfg (drl_bd gp tp s10 s11 F fc (U - 160) (U - 160) (wz 0x34bf0) xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7'
                 (wz (bcnt b)) (wz (b_addr b + 152 + 8 * bcnt b)) (wz (bcnt b + 16)) (wz (16 + bcnt b)) xt3' xt4' xt5' xt6' (b_addr b) mj) moj) K) ->
  realizes_cfg acfg bsegs (mkCfg (drl_call gp tp s10 s11 F fc (U - 160) (U - 160) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (b_addr b) (bcnt b) i it mi) moi) K.
Proof.
  induction kk as [|kk IH]; intros until xt6; intros HK LWS WSI HI HIT II SK BLOCKK; [exfalso; clear -HK HI; lia|].
  eapply (item_step b rest ws j8 i ai mi moi it); [exact LWS| exact WSI| exact HI| exact HIT| exact II| exact SK|].
  intros aj mj moj t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' II' SK'.
  pose proof II' as (WF & _ & AK & _ & _ & _ & _ & _ & _ & _ & TOK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _ & _ & _ & _ & _ & _ & _ & BWS & _ & _ & BOK & _).
  destruct (glue_pols (b :: rest) aj moj WF AK TOK) as (KIP0 & PSTK & PCP & PDAT & PB).
  pose proof (proj1 (Forall_forall _ _) BOK b (or_introl eq_refl)) as (B1 & B2 & B3 & B4 & B5).
  set (P0 := PP (sA aj s) moj) in *.
  set (Q1 := fun ms : machine_state =>
          (i + 1 < bcnt b /\ exists it', nth_error ws (Z.to_nat (i + 1)) = Some it' /\ ms = drl_call gp tp s10 s11 F fc (U - 160) (U - 160) t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (b_addr b) (bcnt b) (i + 1) it' mj)
       \/ (i + 1 = bcnt b /\ ms = drl_bd gp tp s10 s11 F fc (U - 160) (U - 160) (wz 0x34bf0) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
                                   (wz (bcnt b)) (wz (b_addr b + 152 + 8 * (i + 1))) (wz (bcnt b + 16)) (wz (16 + (i + 1))) t3' t4' t5' t6' (b_addr b) mj)).
  eapply (rzA_seg_cfg bsegs (aSc (sA aj s)) (aNc (sA aj s)) (aEBc (sA aj s)) P0 Q1).
  { eapply (drl_item_next P0 gp tp s10 s11 F fc Q1 (U - 160) lo (U - 160) SB LOC ltac:(unfold K_FREE in LO; clear -LO; lia) (hsb_of [] (b :: rest) aj WF) mj (b_addr b) (bcnt b) i ws);
      [clear -HI; lia| clear -HI; lia| exact B5| exact B1| exact B2| exact MI| exact SK'| exact BWS| exact LWS
      | exact (PB b ltac:(apply in_app_iff; right; left; reflexivity))| |].
    - intros it' LT NTH'. apply evtA_done. left. split; [exact LT|]. exists it'. split; [exact NTH'| reflexivity].
    - intros EQ. apply evtA_done. right. split; [exact EQ| reflexivity]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1. destruct KIP1 as [KIA1 _]. pose proof (IINV_magree _ _ _ _ _ _ _ _ mo1 II' AG1 KIA1) as II1.
  destruct HQ1 as [(LT & it' & NTH' & ->)|(EQ & ->)].
  - eapply (IH b rest ws j8 (i + 1) aj mj mo1 it'); [clear -HK HI LT; lia| exact LWS| exact WSI| clear -HI LT; lia| exact NTH'| exact II1| exact SK'| exact BLOCKK].
  - rewrite EQ. eapply BLOCKK; [rewrite EQ in II1; exact II1| exact SK'].
Qed.

(* [comment removed for export] *)
Lemma ldcRM24 : forall l (ai : astate), AWf E0 [] l ai -> BI (zlen l) fzero ai -> 0 <= as_nprim_ever ai <= 12000 ->
  ldcRM ai kBatchClass /\ kFreeArrayMapSize <= gapR ai.
Proof.
  intros l ai WF HBI NP12. assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  pose proof (rooms_of_BI E0 [] l _ _ ai kBatchClass WF HBI HB24 NP12) as (Rm1 & Rm2 & Rm3 & Rm4). cbv zeta in Rm1, Rm2, Rm3, Rm4.
  pose proof WF as (_ & WR & _). destruct (proj2 WR kBatchClass HB24) as (Rg1 & _). cbv zeta in Rg1. unfold region_of in Rg1.
  assert (QN : 0 <= (rg_mapped_user (get_region ai kBatchClass) + kUserMapSize - rg_alloc_user (get_region ai kBatchClass)) / class_size kBatchClass).
  { apply Z.div_pos; [unfold kUserMapSize; clear -Rg1; lia| change (class_size kBatchClass) with 8192; clear; lia]. }
  pose proof (M2_sharp_BI _ _ ai HBI) as M.
  split; [split; [exact Rm4| change (hint kBatchClass) with 1; unfold kFreeArrayMapSize, kFreeArraySize in *; clear -Rm2 QN; lia]|].
  unfold gapR, kBatchPages, kFreeArrayMapSize. clear -M. lia.
Qed.

(* [comment removed for export] *)
Lemma block_step : forall b rest ws j8 aj mj moj (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
  IINV b rest ws j8 (bcnt b) aj mj moj -> stk bsegs mj lo (U - 160 + -112) ->
  (forall ak mk mok (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     LINV rest ak mk mok -> stk bsegs mk lo (U - 160 + -112) ->
     drl_fr_lo (U - 160) mk j8 -> drl_fr_cb (U - 160) (wz (T + 208)) (wz B) mk -> drl_fr_hi (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 mk ->
     realizes_cfg acfg bsegs (mkCfg (drl_latch gp tp s10 s11 F fc (U - 160) (U - 160) (wz 0x34c28) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (wz (b_addr b)) xs6 xs7 xs8 xs9 t3' t4' t5' t6' mk) mok) K) ->
  realizes_cfg acfg bsegs (mkCfg (drl_bd gp tp s10 s11 F fc (U - 160) (U - 160) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 (b_addr b) mj) moj) K.
Proof.
  intros until xt6. intros II SK KL.
  destruct II as (WF & REP & AK & RES & DI & SS & CS & HBI & TQ & GQ & TOK & Ffs & Ffds & Ftid & Enp & Eres & Endi & Enb & Esb & SECi & PLIVE & RLIVE & ILIVE & GONE & RUNK
                  & MI & RT & PF & TC & FRR & FLO & FCB & FHI & BH & BWS & BC & BIT & BOK & BAP & QBYT & (W & MU & AWOK & AVOID)).
  pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  pose proof FB as (BU1 & BU2 & BU3). unfold kInitialCredit in BU3.
  assert (NP12 : 0 <= as_nprim_ever aj <= 12000) by (rewrite Enp; clear -BU1 BU2 BU3; lia).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  rewrite Nat2Z.id in GONE, RUNK. rewrite firstn_all in GONE. rewrite skipn_all in RUNK.
  pose proof WF as (WE & WR & _).
  destruct (AWf_drop_dbatch E0 [] rest aj b WF GONE) as [WFr AV].
  destruct (carved_class_of_addr E0 aj kBatchClass (b_addr b) HB24 WE WR (proj1 AV)) as [IP CL].
  destruct (ldcRM24 (b :: rest) aj WF HBI NP12) as [RM GAPR].
  assert (RMr : ldcRM aj kBatchClass) by exact RM.
  pose proof (hsb_of [] (b :: rest) aj WF) as HSB.
  pose proof (carved_in_space E0 aj kBatchClass _ HB24 WR (proj1 AV)) as [I1 I2]. change (class_size kBatchClass) with 8192 in I2.
  (* [comment removed for export] *)
  destruct (glue_pols (b :: rest) aj moj WF AK TOK) as (KIP0 & PSTK & PCP & PDAT & PB). set (P0 := PP (sA aj s) moj) in *.
  pose proof REP as (Rins & _). pose proof Rins as (I1' & _). unfold ae_instance in I1'. rewrite IC0_T7 in I1'. cbn [aic_instance both_ic kInsSpaceBeg Z.add] in I1'.
  pose proof (BF_kit3.rwc_split bsegs mj _ [C8 (AsanRep.zw SB); C4 (AsanRep.zw 0xffffffff); C4 (AsanRep.zw 0); C8 (AsanRep.zw RI)] [C1 (AsanRep.zb 0)] I1') as [INS4 _].
  set (Q1 := fun ms : machine_state =>
        ms = MS (mkR (wz 0x34c28) (wz (U - 160 + -112)) gp tp xt0 xt1 xt2 (wz (U - 160)) (wz INST) (wz (T + 208)) (wz INST) (wz kBatchClass) (wz (b_addr b)) xa4 xa5 xa6 xa7
                    (wz 0xaaf98) (wz 0xab208) (wz (b_addr b)) (wz (2^37)) xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6) F (wz 0x35068) fc None mj (seg_rom bsegs)).
  eapply (rzA_seg_cfg bsegs (aSc (sA aj s)) (aNc (sA aj s)) (aEBc (sA aj s)) P0 Q1).
  { unfold drl_fr_cb in FCB.
    eapply (drl_bdealloc P0 gp tp s10 s11 F fc Q1 (U - 160) lo (U - 160) SB RI (wz (T + 208)) (wz B) LOC ltac:(clear -LO; lia) HSB PSTK PDAT mj (b_addr b));
      [clear -I1; unfold kRegionSize in I1; lia| exact I2| exact MI| exact SK| exact INS4| exact FCB|].
    unfold class_of_addr. rewrite CL. apply evtA_done. reflexivity. }
  { exact KIP0. }
  intros ms1 mo1 -> AG1 KIP1. destruct KIP1 as [KIA1 _].
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1. pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 AK) as AK1.
  (* [comment removed for export] *)
  eapply (LDC (wz 0x34c28) gp tp xt0 xt1 xt2 (wz (U - 160)) (wz INST) xa4 xa5 xa6 xa7 (wz 0xaaf98) (wz 0xab208) (wz (b_addr b)) (wz (2^37)) xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6
            F fc mj mo1 (sA aj s) rest kBatchClass (b_addr b) lo (U - 160 + -112) (C - 1) (C' - DSLACK) K KN TOK1);
    cbn [aps_alloc sA aps_set_alloc];
    [exact REP| exact WFr| exact AK1| exact RES| exact MI| exact RT| exact HB24| exact AV| exact (ci_of_batch E0 [] (b :: rest) aj b WF (or_introl eq_refl))| exact GAPR| exact (proj1 RM)
    | exact SK| exact LOC| unfold K_LDC; clear -LO; lia| clear -SPA; Z.div_mod_to_equations; lia| clear -SPH; lia| exact TP|].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' a' POST. rewrite (ret_pc_even 0x34c28) by (clear; lia).
  destruct POST as (RUN' & REP' & WF' & AK' & TOK' & Ffs' & Ffds' & Ftid' & SK' & MI' & RT' & WM' & MU' & SAME').
  rewrite BF_popT.sA_sA in TOK'.
  pose proof SAME' as (Xch & Xdd & Xtq & Xgq & Xsec & Xptr & Xsst & Xssl & Xga & Xgm & Xnp & Xres & Xev & Xnd & Xnb & Xsb & Xks & Xfr & Xst & Xci & Xcm & Xia & Xoom & Xoth & Xmu & Xfa & Xrb).
  destruct RUN' as (fr & orr & evr & orr' & RUN'). destruct (arun_orc_app2 _ _ _ _ _ _ _ RUN') as (ur & _ & Rr). pose proof (Rr []) as RUNx. rewrite app_nil_r in RUNx.
  assert (AGH : forall z, U - 160 + -112 <= z < 2^64 -> m' (wa z) = mj (wa z))
    by exact (ldcW_high_agree [] (b :: rest) aj mo1 kBatchClass (U - 160 + -112) mj m' WF AK1 HB24 RM LOC ltac:(clear -LO; lia) MU').
  assert (AGB : forall b', In b' rest -> forall z, b_addr b' <= z < b_addr b' + 8192 -> m' (wa z) = mj (wa z)).
  { intros b' Hb'. apply (ldcW_batch_agree [] (b :: rest) aj mo1 kBatchClass (U - 160 + -112) mj m' b' WF AK1 HB24 RM);
      [| exact (proj1 (Forall_forall _ _) BOK b' (or_intror Hb'))| exact LOC| unfold K_LDC; clear -LO; lia| clear -SPH; lia| exact MU'].
    apply in_app_iff. right. right. exact Hb'. }
  (* [comment removed for export] *)
  assert (HBI' : BI (zlen rest) fzero a').
  { pose proof (BI_detach (zlen (b :: rest)) fzero aj ltac:(rewrite zlen_cons; pose proof (zlen_nonneg rest); lia) HBI) as BI2.
    rewrite zlen_cons in BI2. replace (1 + zlen rest - 1) with (zlen rest) in BI2 by (clear; lia).
    assert (F1 : 1 <= fadd kBatchClass 1 fzero kBatchClass) by (rewrite fadd_eq; unfold fzero; clear; lia).
    pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (local_dealloc_cnt E0 _ _ aj kBatchClass (b_addr b) HB24 BI2 F1) eq_refl RUNx) as [BI3 _].
    eapply BI_Fext; [| exact BI3]. intros c'. unfold fadd, fzero. destruct (c' =? kBatchClass); reflexivity. }
  eapply (KL a' m' mo').
  - unfold LINV.
    split; [exact WF'|]. split; [exact REP'|]. split; [exact AK'|].
    split; [exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (local_dealloc_res E0 kBatchClass (b_addr b)) RES RUNx)|].
    split; [exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (local_dealloc_di E0 kBatchClass (b_addr b)) DI RUNx)|].
    split; [unfold sstats_ok, sec_bytes in SS |- *; rewrite Xsst, Xsec; exact SS|]. split; [intros k cmk Hk; rewrite Xch in Hk; exact (CS k cmk Hk)|].
    split; [exact HBI'|]. split; [rewrite Xtq; exact TQ|]. split; [unfold gq_bytes; rewrite Xgq; exact GQ|]. split; [exact TOK'|].
    split; [rewrite Ffs', Ffs1; exact Ffs|]. split; [rewrite Ffds', Ffds1; exact Ffds|]. split; [rewrite Ftid', Ftid1; exact Ftid|].
    split; [rewrite Xnp; exact Enp|]. split; [rewrite Xres; exact Eres|]. split; [rewrite Xnd; exact Endi|]. split; [rewrite Xnb; exact Enb|]. split; [rewrite Xsb; exact Esb|].
    split; [rewrite Xsec; exact SECi|].
    split; [unfold live_blocks, chunk_list in PLIVE |- *; rewrite Xch; exact PLIVE|].
    split; [intros b' Hb' y Hy; destruct (RLIVE b' Hb' y Hy) as (cmy & iy & jy & Hcy & STy); exists cmy, iy, jy; rewrite Xch; split; [exact Hcy| exact STy]|].
    split. { intros ax fr3 o3 e3 o3' R3. apply (RUNK aj 0%nat [] [] eq_refl a' fr ur evr RUNx ax fr3 o3 e3 o3' R3). }
    split; [exact MI'|]. split; [exact RT'|].
    split; [unfold put_frame in PF |- *; rewrite HU in PF |- *; agh PF AGH; clear -Hz LO SPH; lia|].
    split; [unfold tmpc in TC |- *; agh TC AGH; clear -Hz LO SPH; lia|].
    split; [agh FRR AGH; clear -Hz LO SPH; lia|].
    split; [eapply bcellsn_agree; [exact BC| intros b' z Hb' Hz; apply (AGB b' Hb'); clear -Hz; lia]|].
    split; [eapply bitemsl_agree; [exact BIT| intros b' z Hb' Hz; apply (AGB b' Hb'); clear -Hz; lia]|].
    split; [inversion BOK; assumption|]. split; [exact (proj2 BAP)|]. split; [exact QBYT|].
    exists (W ++ ldc_W E0 aj kBatchClass (U - 160 + -112)). split; [| split; apply Forall_app; split; [exact AWOK| | exact AVOID|]].
    + eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']]; intros z Hz;
        apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin.
    + exact (ldcW_awok [] (b :: rest) aj mo1 kBatchClass (U - 160 + -112) WF AK1 HB24 RM ltac:(unfold K_LDC; clear -LO; lia) ltac:(clear; lia)).
    + exact (ldcW_avoid [] (b :: rest) aj mo1 kBatchClass (U - 160 + -112) WF AK1 HB24 RM PLIVE LOC ltac:(unfold K_LDC; clear -LO; lia)).
  - exact SK'.
  - unfold drl_fr_lo in FLO |- *. agh FLO AGH. clear -Hz LO SPH; lia.
  - unfold drl_fr_cb in FCB |- *. agh FCB AGH. clear -Hz LO SPH; lia.
  - unfold drl_fr_hi in FHI |- *. agh FHI AGH. clear -Hz LO SPH; lia.
Qed.

(* [comment removed for export] *)
Lemma qbytes_ge_len : forall l, Forall (bok lo T) l -> 8192 * blen l <= qbytes l.
Proof.
  intros l H. induction l as [|b l IH]; [cbn; clear; lia|]. inversion H as [|? ? [_ [_ [_ [B4 _]]]] H']; subst.
  specialize (IH H'). unfold qbytes in *. cbn [fold_right length] in *. clear -IH B4. lia.
Qed.

(* [comment removed for export] *)
Lemma iinv_start : forall b rest ws j8 ai mi m1 moi,
  LINV (b :: rest) ai mi moi ->
  drl_fr_lo (U - 160) mi j8 -> drl_fr_cb (U - 160) (wz (T + 208)) (wz B) mi -> drl_fr_hi (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 mi ->
  (forall k x, nth_error (b_items b) k = Some x -> nth_error ws k = Some (wz x)) ->
  munch [(U - 160, U - 160 + 32)] mi m1 -> wmono bsegs mi m1 -> mem_inv bsegs m1 -> tmpc (U - 160) m1 rest ->
  rw_cells bsegs m1 (b_addr b) [C8 (wz (bhd rest)); C8 (wz (b_size b)); C8 (wz (bcnt b))] -> u64arr bsegs m1 (b_addr b + 24) ws ->
  IINV b rest ws j8 0 ai m1 moi.
Proof.
  intros b rest ws j8 ai mi m1 moi LI FLO FCB FHI WSI MU1 WM1 MI1 TC1 BH1 BWS1.
  destruct LI as (WF & REP & AK & RES & DI & SS & CS & HBI & TQ & GQ & TOK & Ffs & Ffds & Ftid & Enp & Eres & Endi & Enb & Esb & SECi & PLIVE & ILIVE & RUNK
                  & MI & RT & PF & TC & FRR & BC & BIT & BOK & BAP & QBYT & (W & MU & AWOK & AVOID)).
  pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 (sA ai s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  assert (AG1 : forall z, (z < U - 160 \/ U - 128 <= z) -> 0 <= z < 2^64 -> m1 (wa z) = mi (wa z)).
  { intros z Hz Rz. apply MU1. rewrite wa_unsigned by exact Rz. cbn [outside]. clear -Hz. repeat split; try exact I; lia. }
  pose proof WF as (WE & WR & _ & _ & WQ & _). assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  destruct (batch_block E0 (b :: rest) ai b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; right; left; reflexivity)) as (CV & _).
  destruct (carved_class_of_addr E0 ai kBatchClass (b_addr b) HB24 WE WR CV) as [IP CL].
  unfold IINV. cbn [Z.to_nat skipn firstn].
  split; [exact WF|]. split; [apply (ARep_high_agree E0 [] (b :: rest) ai mi m1 lo REP WF (renv_of E0 PL0 ENV0 PL0OK _ ai moi WF AK EI1 EI2) LOC WM1); intros z Hz Hlo; apply AG1; [left; clear -Hlo LO; lia| exact Hz]|].
  split; [exact AK|]. split; [exact RES|]. split; [exact DI|]. split; [exact SS|]. split; [exact CS|]. split; [exact HBI|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact TOK|].
  split; [exact Ffs|]. split; [exact Ffds|]. split; [exact Ftid|]. split; [exact Enp|]. split; [exact Eres|]. split; [exact Endi|]. split; [exact Enb|]. split; [exact Esb|]. split; [exact SECi|]. split; [exact PLIVE|].
  split; [intros b' Hb'; apply ILIVE; right; exact Hb'|]. split; [apply ILIVE; left; reflexivity|]. split; [intros x []|].
  split. { intros a1 f1 o1 e1 R1 ab f2 o2 e2 R2 a' f3 o3 e3 o3' R3.
           destruct (arun_do_recycle_cons E0 b rest ai a1 ab f1 o1 e1 f2 o2 e2 f3 o3 _ IP CL R1 R2 R3) as (f & e & R). cbn [fst snd] in R. exact (RUNK a' f _ e o3' R). }
  split; [exact MI1|].
  split. { apply (rt_misc5_agree E0 FSB0 PL0 mi m1 RT). intros z Hz.
           pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & _). pose proof TR as (_ & (Tlo & Thi & _) & _).
           pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & _). pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & _).
           destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH]; [apply AG1; clear -ZI LO LOC CR; lia|].
           unfold rt_high2 in RH. apply AG1; clear -RH LO LOC CR Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2; lia. }
  split; [unfold put_frame in PF |- *; rewrite HU in PF |- *; agw PF MU1 WM1; clear; repeat split; try exact I; lia|].
  split; [exact TC1|].
  split; [agw FRR MU1 WM1; clear; repeat split; try exact I; lia|].
  split; [unfold drl_fr_lo in FLO |- *; agw FLO MU1 WM1; clear; repeat split; try exact I; lia|].
  split; [unfold drl_fr_cb in FCB |- *; agw FCB MU1 WM1; clear; repeat split; try exact I; lia|].
  split; [unfold drl_fr_hi in FHI |- *; agw FHI MU1 WM1; clear; repeat split; try exact I; lia|].
  split; [exact BH1|]. split; [exact BWS1|].
  split. { eapply bcellsn_transport; [exact (proj2 BC)| exact MU1| exact WM1|]. apply Forall_forall. intros b' Hb'.
           pose proof (proj1 (Forall_forall _ _) BOK b' (or_intror Hb')) as (_ & B2 & _). cbn. clear -B2 LO. repeat split; try exact I; lia. }
  split. { eapply bitemsl_transport; [exact (proj2 BIT)| exact MU1| exact WM1|]. apply Forall_forall. intros b' Hb'.
           pose proof (proj1 (Forall_forall _ _) BOK b' (or_intror Hb')) as (_ & B2 & _). cbn. clear -B2 LO. repeat split; try exact I; lia. }
  split; [exact BOK|]. split; [exact BAP|].
  split; [pose proof (proj1 (Forall_forall _ _) BOK b (or_introl eq_refl)) as (_ & _ & _ & B4 & _); unfold qbytes in QBYT |- *; cbn [fold_right] in QBYT; clear -QBYT B4; lia|].
  exists (W ++ [(U - 160, U - 160 + 32)]). split; [| split; apply Forall_app; split; [exact AWOK| | exact AVOID|]].
  - eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU1]]; intros z Hz;
      apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin.
  - apply Forall_cons; [| apply Forall_nil]. unfold aw_ok. cbn [fst snd]. left. clear -LO. lia.
  - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros blo bsz LIVEb NEb. right; right.
    destruct (BF_casT.live_block_where E0 a blo bsz (proj1 (proj2 AIV)) LIVEb) as (Lw0 & Lw1 & _). clear -Lw1 LOC LO. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma batch_loop : forall l ai mi moi j8 (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
  l <> [] -> LINV l ai mi moi -> stk bsegs mi lo (U - 160 + -112) ->
  drl_fr_lo (U - 160) mi j8 -> drl_fr_cb (U - 160) (wz (T + 208)) (wz B) mi -> drl_fr_hi (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 mi ->
  realizes_cfg acfg bsegs (mkCfg (drl_head gp tp s10 s11 F fc (U - 160) (U - 160) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 (blen l) mi) moi) K.
Proof.
  induction l as [|b rest IH]; intros until xt6; intros NE LI SK FLO FCB FHI; [exfalso; exact (NE eq_refl)|].
  pose proof LI as (WF & _ & AK & _ & _ & _ & _ & _ & _ & _ & TOK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _ & TC & _ & BC & BIT & BOK & BAP & QBYT & _).
  pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  destruct (glue_pols (b :: rest) ai moi WF AK TOK) as (KIP0 & PSTK & PCP & PDAT & PB). set (P0 := PP (sA ai s) moi) in *.
  destruct (bitems_words mi b (proj1 BIT)) as (ws & BWS & LWS & WSI).
  pose proof (proj1 (Forall_forall _ _) BOK b (or_introl eq_refl)) as (B1 & B2 & B3 & B4 & B5).
  pose proof (qbytes_ge_len (b :: rest) BOK) as QL. pose proof (qbytes_ge_len rest ltac:(inversion BOK; assumption)) as QLr.
  assert (QR : 0 <= qbytes rest /\ qbytes (b :: rest) = b_size b + qbytes rest) by (unfold qbytes; cbn [fold_right]; clear -QLr; unfold qbytes in QLr; split; [lia| reflexivity]).
  set (Q1 := fun ms : machine_state => exists m1,
          mem_inv bsegs m1 /\ stk bsegs m1 lo (U - 160 + -112) /\ munch [(U - 160, U - 160 + 32)] mi m1 /\ wmono bsegs mi m1 /\ tmpc (U - 160) m1 rest
       /\ rw_cells bsegs m1 (b_addr b) [C8 (wz (bhd rest)); C8 (wz (b_size b)); C8 (wz (bcnt b))] /\ u64arr bsegs m1 (b_addr b + 24) ws
       /\ ((b_items b = [] /\ ms = drl_bd gp tp s10 s11 F fc (U - 160) (U - 160) xra xt0 xt1 xt2 (wz (b_size b)) (wz (qbytes rest)) xa2 xa3 xa4 xa5 xa6 xa7 (wz 0) xs7 xs8 xs9 xt3 xt4 xt5 xt6 (b_addr b) m1)
           \/ (exists it0, nth_error ws 0 = Some it0 /\ 0 < bcnt b /\ ms = drl_call gp tp s10 s11 F fc (U - 160) (U - 160) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (b_addr b) (bcnt b) 0 it0 m1))).
  eapply (rzA_seg_cfg bsegs (aSc (sA ai s)) (aNc (sA ai s)) (aEBc (sA ai s)) P0 Q1).
  { eapply (drl_deq P0 gp tp s10 s11 F fc Q1 (U - 160) lo (U - 160) SB LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) (hsb_of [] (b :: rest) ai WF) PCP mi (b :: rest) b rest ws);
      [reflexivity| | | exact (proj1 QR)| clear -B4; lia| clear -QBYT QR; lia| exact B5| exact B1| exact B2| exact MI| exact SK| exact TC| exact (proj1 BC)| exact BWS| exact LWS
      | exact (PB b ltac:(apply in_app_iff; right; left; reflexivity))| |].
    - destruct rest as [|b2 rest']; [left; reflexivity| right]. pose proof (proj1 (Forall_forall _ _) BOK b2 ltac:(right; left; reflexivity)) as (C1 & C2 & _).
      cbn [bhd_or]. clear -C1 C2 SPH LO LOC CR. lia.
    - unfold blen. clear -QL QBYT. cbn [length] in *. lia.
    - intros m1 NOI MI1 SK1 MU1 WM1 TC1 BH1 BWS1. apply evtA_done. exists m1. repeat (split; [assumption|]). left. split; [exact NOI| reflexivity].
    - intros m1 it0 NTH0 POS MI1 SK1 MU1 WM1 TC1 BH1 BWS1. apply evtA_done. exists m1. repeat (split; [assumption|]). right. exists it0. split; [exact NTH0|]. split; [exact POS| reflexivity]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1. destruct KIP1 as [KIA1 _].
  destruct HQ1 as (m1 & MI1 & SK1 & MU1 & WM1 & TC1 & BH1 & BWS1 & ARMS).
  pose proof (LINV_magree _ _ _ _ mo1 LI AG1 KIA1) as LI1.
  pose proof (iinv_start b rest ws j8 ai mi m1 mo1 LI1 FLO FCB FHI WSI MU1 WM1 MI1 TC1 BH1 BWS1) as II0.
  (* [comment removed for export] *)
  assert (BLOCKK : forall aj mj moj (zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs6 zs7 zs8 zs9 zt3 zt4 zt5 zt6 : word),
      IINV b rest ws j8 (bcnt b) aj mj moj -> stk bsegs mj lo (U - 160 + -112) ->
      realizes_cfg acfg bsegs (mkCfg (drl_bd gp tp s10 s11 F fc (U - 160) (U - 160) zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs6 zs7 zs8 zs9 zt3 zt4 zt5 zt6 (b_addr b) mj) moj) K).
  { intros until zt6. intros IIb SKb. eapply block_step; [exact IIb| exact SKb|].
    intros ak mk mok t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LIk SKk FLOk FCBk FHIk.
    pose proof LIk as (WFk & _ & AKk & _ & _ & _ & _ & _ & _ & _ & TOKk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIk & _ & _ & TCk & _ & _ & _ & BOKk & _ & QBYTk & _).
    destruct (glue_pols rest ak mok WFk AKk TOKk) as (KIPk & PSTKk & PCPk & _). set (Pk := PP (sA ak s) mok) in *.
    pose proof (qbytes_ge_len rest BOKk) as QLk.
    set (Qk := fun ms : machine_state =>
            (rest <> [] /\ ms = drl_head gp tp s10 s11 F fc (U - 160) (U - 160) (wz 0x34c28) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' (wz (b_addr b)) zs6 zs7 zs8 zs9 t3' t4' t5' t6' (blen rest) mk)
         \/ (rest = [] /\ stk bsegs mk lo (U - 160) /\ ms = drl_ret gp tp s10 s11 F fc (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mk)).
    eapply (rzA_seg_cfg bsegs (aSc (sA ak s)) (aNc (sA ak s)) (aEBc (sA ak s)) Pk Qk).
    { eapply (drl_latch_step Pk gp tp s10 s11 F fc Qk (U - 160) lo (U - 160) SB (wz (T + 208)) (wz B) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9
                LOC ltac:(clear -LO; lia) PSTKk PCPk mk rest);
        [unfold blen in *; clear -QLk QBYTk; lia| exact MIk| exact SKk| exact TCk| exact FLOk| exact FCBk| exact FHIk| |].
      - intros NEr. apply evtA_done. left. split; [exact NEr| reflexivity].
      - intros Er SKr. apply evtA_done. right. split; [exact Er|]. split; [exact SKr| reflexivity]. }
    { exact KIPk. }
    intros ms2 mo2 HQ2 AG2 KIP2. destruct KIP2 as [KIA2 _]. pose proof (LINV_magree _ _ _ _ mo2 LIk AG2 KIA2) as LI2.
    destruct HQ2 as [(NEr & ->)|(Er & SKr & ->)].
    - eapply IH; [exact NEr| exact LI2| exact SKk| exact FLOk| exact FCBk| exact FHIk].
    - subst rest. eapply loop_exit; [exact LI2| exact SKr]. }
  destruct ARMS as [(NOI & ->)|(it0 & NTH0 & POS & ->)].
  - (* [comment removed for export] *)
    assert (BC0 : bcnt b = 0) by (rewrite NOI; reflexivity).
    eapply BLOCKK; [| exact SK1]. rewrite BC0. exact II0.
  - eapply (items_loop (Z.to_nat (bcnt b)) b rest ws j8 0 ai m1 mo1 it0); [clear; lia| exact LWS| exact WSI| clear -POS; lia| exact NTH0| exact II0| exact SK1|].
    intros. eapply BLOCKK; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma LINV_prologue : forall l ai mi m' moi,
  LINV l ai mi moi -> munch [(U - 160 + -112, U - 160)] mi m' -> wmono bsegs mi m' -> mem_inv bsegs m' -> LINV l ai m' moi.
Proof.
  intros l ai mi m' moi LI MU1 WM1 MI1.
  destruct LI as (WF & REP & AK & RES & DI & SS & CS & HBI & TQ & GQ & TOK & Ffs & Ffds & Ftid & Enp & Eres & Endi & Enb & Esb & SECi & PLIVE & ILIVE & RUNK
                  & MI & RT & PF & TC & FRR & BC & BIT & BOK & BAP & QBYT & (W & MU & AWOK & AVOID)).
  pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 (sA ai s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  assert (AG1 : forall z, (z < U - 160 + -112 \/ U - 160 <= z) -> 0 <= z < 2^64 -> m' (wa z) = mi (wa z)).
  { intros z Hz Rz. apply MU1. rewrite wa_unsigned by exact Rz. cbn [outside]. clear -Hz. repeat split; try exact I; lia. }
  unfold LINV.
  split; [exact WF|]. split; [apply (ARep_high_agree E0 [] l ai mi m' lo REP WF (renv_of E0 PL0 ENV0 PL0OK _ ai moi WF AK EI1 EI2) LOC WM1); intros z Hz Hlo; apply AG1; [left; clear -Hlo LO; lia| exact Hz]|].
  split; [exact AK|]. split; [exact RES|]. split; [exact DI|]. split; [exact SS|]. split; [exact CS|]. split; [exact HBI|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact TOK|].
  split; [exact Ffs|]. split; [exact Ffds|]. split; [exact Ftid|]. split; [exact Enp|]. split; [exact Eres|]. split; [exact Endi|]. split; [exact Enb|]. split; [exact Esb|]. split; [exact SECi|]. split; [exact PLIVE|].
  split; [exact ILIVE|]. split; [exact RUNK|]. split; [exact MI1|].
  split. { apply (rt_misc5_agree E0 FSB0 PL0 mi m' RT). intros z Hz.
           pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & _). pose proof TR as (_ & (Tlo & Thi & _) & _).
           pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & _). pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & _).
           destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH]; [apply AG1; clear -ZI LO LOC CR; lia|].
           unfold rt_high2 in RH. apply AG1; clear -RH LO LOC CR Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2; lia. }
  split; [unfold put_frame in PF |- *; rewrite HU in PF |- *; agw PF MU1 WM1; clear; repeat split; try exact I; lia|].
  split; [unfold tmpc in TC |- *; agw TC MU1 WM1; clear; repeat split; try exact I; lia|].
  split; [agw FRR MU1 WM1; clear; repeat split; try exact I; lia|].
  split. { eapply bcellsn_transport; [exact BC| exact MU1| exact WM1|]. apply Forall_forall. intros b' Hb'.
           pose proof (proj1 (Forall_forall _ _) BOK b' Hb') as (_ & B2 & _). cbn. clear -B2 LO. repeat split; try exact I; lia. }
  split. { eapply bitemsl_transport; [exact BIT| exact MU1| exact WM1|]. apply Forall_forall. intros b' Hb'.
           pose proof (proj1 (Forall_forall _ _) BOK b' Hb') as (_ & B2 & _). cbn. clear -B2 LO. repeat split; try exact I; lia. }
  split; [exact BOK|]. split; [exact BAP|]. split; [exact QBYT|].
  exists (W ++ [(U - 160 + -112, U - 160)]). split; [| split; apply Forall_app; split; [exact AWOK| | exact AVOID|]].
  - eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU1]]; intros z Hz;
      apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin.
  - apply Forall_cons; [| apply Forall_nil]. unfold aw_ok. cbn [fst snd]. left. clear -LO. lia.
  - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros blo bsz LIVEb NEb. right; right.
    destruct (BF_casT.live_block_where E0 a blo bsz (proj1 (proj2 AIV)) LIVEb) as (Lw0 & Lw1 & _). clear -Lw1 LOC LO. lia.
Qed.

(* [comment removed for export] *)
Lemma loop_entry : forall l ai mi moi (xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  LINV l ai mi moi -> stk bsegs mi lo (U - 160) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR (wz 0x34934) (wz (U - 160)) gp tp xt0 xt1 xt2 x8 x9 (wz (INST + 728)) (wz (U - 160)) (wz (T + 208)) (wz B) xa4 xa5 xa6 xa7
                    x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (wz 0x34b2c) fc None mi (seg_rom bsegs)) moi) K.
Proof.
  intros until xt6. intros LI SK.
  pose proof LI as (WF & _ & AK & _ & _ & _ & _ & _ & _ & _ & TOK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _ & TC & _ & _ & _ & BOK & _ & QBYT & _).
  pose proof alloc_ceiling_range as CR. unfold K_FREE in LO.
  destruct (glue_pols l ai moi WF AK TOK) as (KIP0 & PSTK & PCP & PDAT & PB). set (P0 := PP (sA ai s) moi) in *.
  pose proof (qbytes_ge_len l BOK) as QL.
  set (Q1 := fun ms : machine_state => exists m1,
          mem_inv bsegs m1 /\ munch [(U - 160 + -112, U - 160)] mi m1 /\ wmono bsegs mi m1
       /\ ((l = [] /\ stk bsegs m1 lo (U - 160) /\ ms = drl_ret gp tp s10 s11 F fc (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 xt0 xt1 xt2 (wz (U - 160)) (wz (T + 208)) (wz B) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m1)
           \/ (exists j8, l <> [] /\ stk bsegs m1 lo (U - 160 + -112) /\ drl_fr_lo (U - 160) m1 j8 /\ drl_fr_cb (U - 160) (wz (T + 208)) (wz B) m1
               /\ drl_fr_hi (U - 160) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 m1
               /\ ms = drl_head gp tp s10 s11 F fc (U - 160) (U - 160) (wz 0x34934) xt0 xt1 xt2 (wz 0xaab70) (wz (T + 208)) (wz B) xa4 xa5 xa6 xa7 x20 (wz 0x100000) s7 s8 s9 xt3 xt4 xt5 xt6 (blen l) m1))).
  eapply (rzA_seg_cfg bsegs (aSc (sA ai s)) (aNc (sA ai s)) (aEBc (sA ai s)) P0 Q1).
  { eapply (drl_entry P0 gp tp s10 s11 F fc Q1 (U - 160) lo (U - 160) SB (wz (T + 208)) (wz B) (wz 0x34934) x8 x9 x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9
              LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) PSTK PCP mi l); [exact MI| exact SK| exact TC| unfold blen in *; clear -QL QBYT; lia| |].
    - intros m1 E MI1 SK1 MU1 WM1 TC1. apply evtA_done. exists m1. split; [exact MI1|]. split; [exact MU1|]. split; [exact WM1|]. left. split; [exact E|]. split; [exact SK1| reflexivity].
    - intros m1 j8 NE MI1 SK1 MU1 WM1 TC1 FLO FCB FHI. apply evtA_done. exists m1. split; [exact MI1|]. split; [exact MU1|]. split; [exact WM1|]. right. exists j8.
      split; [exact NE|]. split; [exact SK1|]. split; [exact FLO|]. split; [exact FCB|]. split; [exact FHI| reflexivity]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1. destruct KIP1 as [KIA1 _].
  destruct HQ1 as (m1 & MI1 & MU1 & WM1 & ARMS).
  pose proof (LINV_prologue l ai mi m1 mo1 (LINV_magree _ _ _ _ mo1 LI AG1 KIA1) MU1 WM1 MI1) as LI1.
  destruct ARMS as [(E & SK1 & ->)|(j8 & NE & SK1 & FLO & FCB & FHI & ->)].
  - subst l. eapply loop_exit; [exact LI1| exact SK1].
  - eapply batch_loop; [exact NE| exact LI1| exact SK1| exact FLO| exact FCB| exact FHI].
Qed.

End LOOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma BI_to_detach : forall (sx a2 a4 : astate) cb cm aid key fid fd orcd evsd orcd' fe orce evse orce' gq1 emp popped kept,
  let a5 := xfer_st a4 in
  AsanBudget2.binv sx -> AQbound sx -> as_chunks sx !! cb = Some cm ->
  arun fd (depot_put E0 key (upd_ts (ts_on_free (cm_n cm)) sx)) orcd = Some (a2, ONorm fid, evsd, orcd') ->
  arun fe (enqueue E0 cb (cm_n cm) (AsanRepFlipB.s3 a2 cb cm aid fid)) orce = Some (a4, ONorm tt, evse, orce') ->
  AWf E0 [] [] a5 ->
  BF_deallocT4.rmerge (as_gq a5) = (gq1, emp) -> pop_prefix gq1 (qbytes gq1) kQuarantineMin = (popped, kept) ->
  BI (zlen (emp ++ popped)) fzero (upd_gq (fun _ => kept) a5).
Proof.
  intros until kept. cbv zeta. intros HBI QB Hcm RUNd RUNe WF5 MG PP.
  pose proof HBI as (B1 & B6 & B7 & B8 & B9 & ND). destruct (B6 _ _ Hcm) as [Hn _].
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (depot_put_view E0 (upd_ts (ts_on_free (cm_n cm)) sx) key) eq_refl RUNd) as V2. cbv beta in V2.
  assert (BI2 : BI 0 fzero a2) by (eapply BI_view; [exact V2| eapply BI_view; [| exact HBI]; reflexivity]).
  pose proof V2 as V2'. unfold bview_of in V2'. injection V2' as Vr Vc Vk Vt Vg Vs Vn Ve.
  assert (Hcm2 : as_chunks a2 !! cb = Some cm) by (rewrite Vk; exact Hcm).
  assert (BI3 : BI 0 fzero (AsanRepFlipB.s3 a2 cb cm aid fid)) by (unfold AsanRepFlipB.s3; apply (BI_chunk_flip 0 fzero a2 _ cm _ BI2 Hcm2); reflexivity).
  assert (QB3 : AQbound (AsanRepFlipB.s3 a2 cb cm aid fid)) by (apply (AQbound_tg sx); [cbn; exact Vt| cbn; exact Vg| exact QB]).
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (enqueue_cnt E0 _ cb (cm_n cm) BI3 ltac:(clear -Hn; lia) (nbatch_bound _ BI3 QB3)) eq_refl RUNe) as BI4. cbv beta in BI4.
  pose proof BI4 as (C1 & C6 & C7 & C8 & C9 & _).
  assert (BI5 : BI 0 fzero (xfer_st a4)).
  { unfold xfer_st. apply (BI_requeue 0 0 fzero fzero a4); [exact BI4| clear; lia| |].
    - intros c Hc. pose proof (proj1 (BI_c 0 fzero a4 c Hc BI4)) as X. unfold BIc_raw in X. unfold nbatch. cbn [as_tq]. rewrite zlen_app, (@zlen_nil batch). split; [clear; nia| unfold fzero; clear; lia].
    - cbn [as_tq app]. intros b Hb. apply C7. apply in_app_iff in Hb. apply in_app_iff. clear -Hb. tauto. }
  pose proof BI5 as (D1 & D6 & D7 & D8 & D9 & _).
  assert (MF : zlen gq1 + zlen emp = zlen (as_gq (xfer_st a4)) /\ forall b, In b gq1 -> kBatchSize <= b_size b).
  { unfold BF_deallocT4.rmerge in MG. match type of MG with (if ?b then _ else _) = _ => destruct b end.
    - destruct (merge_cnt _ _ _ MG) as [M1 M2]. split; [exact M1|]. apply M2. intros b Hb. apply D7. apply in_app_iff. right; exact Hb.
    - injection MG as E1 E2. rewrite <- E1, <- E2. rewrite (@zlen_nil batch). split; [rewrite Z.add_0_r; reflexivity|]. intros b Hb. apply D7. apply in_app_iff. right; exact Hb. }
  destruct MF as [MF1 MF2].
  pose proof (pop_prefix_app gq1 (qbytes gq1) kQuarantineMin) as PA. rewrite PP in PA. cbn [fst snd] in PA.
  eapply (BI_view _ _ (upd_tq (fun _ => as_tq (xfer_st a4)) (upd_gq (fun _ => kept) (xfer_st a4)))); [reflexivity|].
  apply (BI_requeue 0 _ fzero fzero (xfer_st a4)); [exact BI5| pose proof (zlen_nonneg (emp ++ popped)); lia| |].
  - intros c Hc. pose proof (proj1 (BI_c 0 fzero _ c Hc BI5)) as X. unfold BIc_raw in X. unfold nbatch.
    rewrite zlen_app. rewrite <- PA in MF1. rewrite zlen_app in MF1. unfold fzero. pose proof (b24_range c). split; [clear -MF1 H; nia| clear; lia].
  - intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [apply D7; apply in_app_iff; left; exact Hb|]. apply MF2. rewrite <- PA. apply in_app_iff. right; exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem recycle_srz : BF_deallocT5.recycle_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof.
  unfold BF_deallocT5.recycle_srz_stmt.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s p n lo B A len C C' ws K. cbv zeta.
  intros KN TOK HC1 HCS AIV FB LIVE SK LOC LO SPA TP HB HBA HAW KONT.
  unfold BF_deallocT3.QR_post. intros t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 m6 mo6 a2 a4 cm aid fid. cbv zeta.
  intros Hcm ST UB RUNd FID DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4 RES4 GQ4 TQ4 DI4 SS4 CS4 Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW PF6 QC6 GT m7 mo7 t0' t1' a4x a5x a6x a7x GTQ MI7 SK7 WM7 MU7 AG7 KIA7 QM7 GQ7 QC7 GLB7.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB.
  pose proof AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  set (a := aps_alloc s) in *. set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range _ sp) as USPR. change (bv_modulus 64) with (2^64) in USPR. fold usp in USPR.
  assert (SPH : usp < 2^47) by (clear -HB HBA HAW; unfold zlen in HAW; lia).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  destruct (freed_chunk_facts E0 s mo m p n Hrep Hwf Hkern EI1 EI2 LIVE) as (cm' & aid' & b1x & Hcm' & UB' & Hn' & _ & _ & N40 & _ & _ & _ & _ & CB0 & CBC & CBB & P16 & CBT & _).
  assert (Ecm : cm' = cm) by (rewrite Hcm in Hcm'; injection Hcm'; auto). subst cm'. subst n.
  pose proof (rounded_ge (cm_n cm)) as (RG1 & RG2 & RG3).
  assert (HL8b : 8 * ((cm_n cm + 7) / 8) < cm_n cm + 8 /\ cm_n cm <= rounded (cm_n cm)) by (clear -N40 RG1; Z.div_mod_to_equations; lia).
  assert (HCB : 0x603000 <= p - 16 /\ p - 16 + 16 + 8 * BF_free1d.l8 (cm_n cm) <= alloc_ceiling /\ (p - 16) mod 16 = 0).
  { unfold BF_free1d.l8. split; [exact CB0|]. split; [clear -CBC HL8b RG3; Z.div_mod_to_equations; lia| clear -P16; Z.div_mod_to_equations; lia]. }
  assert (HNHI : 0 <= cm_n cm / 2^32 < 256) by (clear -N40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (HNLO : 0 <= cm_n cm mod 2^32 < 2^32) by (clear; apply Z.mod_pos_bound; lia).
  pose proof DS2 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22).
  cbn [as_regions as_cache_inited as_cache as_cache_stale as_cache_allocated as_cache_mapped as_ptr_committed as_sec as_sec_stale as_sec_stats
       as_glob_allocated as_glob_mapped as_oom as_chunks as_dead as_tq as_gq as_ia_inited as_residue as_nprim_ever as_everc as_ts upd_ts]
    in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22.
  pose proof FLD as (E4c & E4s & E4p & E4g & E4np & E4res & E4nd & E4nb & E4sb & E4sst).
  (* [comment removed for export] *)
  eapply (recycle_head_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s lo B C C' (bst_key len ws) K
            t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 m6 mo6 a2 a4 cm aid fid (p - 16) m7 mo7 t0' t1' a4x a5x a6x a7x KN TOK HC1 HCS AIV FB);
    fold usp; [replace (p - 16 + 16) with p by (clear; lia); exact LIVE| exact LOC| exact LO| exact SPA| exact SPH| exact TP
    | exact Hcm| exact ST| rewrite UB'; clear; lia| exact RUNd| exact FID| exact DS2| exact ND2| exact RUNe| exact FLD| exact WF4| exact REP4| exact AK4| exact TOK4| exact KIA4
    | exact RES4| exact GQ4| exact TQ4| exact DI4| exact SS4| exact CS4| exact Ffs6| exact Ffds6| exact Ftid6| exact MI6| exact SK6| exact WM6| exact RT6
    | exact MUW| exact PF6| exact QC6| exact GT| exact GTQ| exact MI7| exact SK7| exact WM7| exact MU7| exact AG7| exact KIA7| exact QM7| exact GQ7| exact QC7| exact GLB7|].
  (* [comment removed for export] *)
  unfold BF_deallocT4.QDR_post. clear t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 m6 mo6 a2 a4 aid fid Hcm ST RUNd FID DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4 RES4 GQ4 TQ4 DI4 SS4 CS4
    Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW PF6 QC6 GT m7 mo7 t0' t1' a4x a5x a6x a7x GTQ MI7 SK7 WM7 MU7 AG7 KIA7 QM7 GQ7 QC7 GLB7
    E4c E4s E4p E4g E4np E4res E4nd E4nb E4sb E4sst D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14 D15 D16 D17 D18 D19 D20 D21 D22.
  intros t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 m6 mo6 a2 a4 cmz aid fid. cbv zeta.
  intros Hcmz ST UBz RUNd FID DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4 RES4 GQ4 TQ4 DI4 SS4 CS4 Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW PF6 QC6 GT m7 mo7 t0' t1' a4x a5x a6x a7x GTQ MI7 SK7 WM7 MU7 AG7 KIA7 QM7 GQ7 QC7 GLB7.
  intros m8 mo8 gq1 emp popped kept t0x t1x t2x a4y a5y a6y a7y t3x t4x t5x x8 x9 x18 x19 x20. cbv zeta. intros MRG POP MI8 SK8 MU8 WM8 AG8 KIA8 QM8 GQ8 BCk BIk FR8 BCd BId QK OK8 AP8 SUB8.
  assert (Ecm : cmz = cm) by (rewrite Hcm' in Hcmz; injection Hcmz; auto). subst cmz. clear UBz.
  pose proof FLD as (E4c & E4s & E4p & E4g & E4np & E4res & E4nd & E4nb & E4sb & E4sst).
  pose proof DS2 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22).
  cbn [as_regions as_cache_inited as_cache as_cache_stale as_cache_allocated as_cache_mapped as_ptr_committed as_sec as_sec_stale as_sec_stats
       as_glob_allocated as_glob_mapped as_oom as_chunks as_dead as_tq as_gq as_ia_inited as_residue as_nprim_ever as_everc as_ts upd_ts]
    in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22.
  set (gq5 := as_gq a4 ++ as_tq a4) in *. set (ax5 := xfer_st a4) in *. set (D := emp ++ popped) in *. set (ax6 := upd_gq (fun _ => kept) ax5).
  pose proof (magree_frame _ _ AG7) as (Ffds7 & Fvm7 & Flz7 & Ffs7 & Fh7 & Ftid7 & _). pose proof (magree_frame _ _ AG8) as (Ffds8 & Fvm8 & Flz8 & Ffs8 & Fh8 & Ftid8 & _).
  (* [comment removed for export] *)
  assert (Egq5 : as_gq ax5 = gq5) by (subst ax5 gq5; reflexivity).
  assert (WF5 : AWf E0 [] [] ax5) by (subst ax5; unfold xfer_st; exact (AWf_transfer E0 [] [] a4 WF4)).
  assert (TQNE : as_tq a4 <> []) by (intros E; unfold tq_bytes, kThreadQuarantineMax in GT; rewrite E in GT; cbn in GT; clear -GT; lia).
  assert (WF6 : AWf E0 [] D ax6 /\ (forall b, In b D -> items_live ax6 (b_items b))).
  { assert (MG : let '(l1, o) := BF_deallocT4.rmerge gq5 in AWf E0 [] (o ++ []) (upd_gq (fun _ => l1) ax5) /\ (forall b, In b o -> b_items b = [])).
    { unfold BF_deallocT4.rmerge. match goal with |- let '(_, _) := (if ?b then _ else _) in _ => destruct b end.
      - rewrite <- Egq5. apply (merge_ok E0 [] [] ax5 WF5).
      - split; [| intros b []]. cbn. subst ax5 gq5. unfold xfer_st. destruct a4; exact WF5. }
    rewrite MRG in MG. destruct MG as [WFm EMP]. rewrite app_nil_r in WFm.
    pose proof (pop_prefix_app gq1 (qbytes gq1) kQuarantineMin) as SPLIT. rewrite POP in SPLIT. cbn [fst snd] in SPLIT.
    destruct (AWf_detach E0 [] emp (upd_gq (fun _ => gq1) ax5) popped kept WFm ltac:(symmetry; exact SPLIT)) as [WFd LIVEd].
    rewrite upd_gq_gq in WFd. split.
    - subst D ax6. eapply AWf_perm_D; [apply Permutation_app_comm| exact WFd].
    - intros b Hb. subst D. apply in_app_iff in Hb as [Hb|Hb]; [rewrite (EMP b Hb); intros x []|]. intros x Hx. destruct (LIVEd b Hb x Hx) as (cmx & ix & jx & H & STx). exists cmx, ix, jx. split; [exact H| exact STx]. }
  destruct WF6 as [WF6 LIVE6].
  assert (RENV4 : AsanRepEnqB.renv_ok E0 a4) by exact (renv_of E0 PL0 ENV0 PL0OK [] a4 mo6 WF4 AK4 EI1 EI2).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRr & CT & DT & CD & CIA).
  pose proof TRr as (_ & (Tlo & Thi & Timg & Tband) & _). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof CR0 as (CIn & _ & _ & CRS & _). pose proof DR0 as (DIn & _ & _ & DRS & _). change kResvLen with 137439023104 in CRS, DRS.
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
  pose proof (ak_resv_geom _ _ _ AK4) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  pose proof (proj1 WF4) as WE4. pose proof (wf_env_iarena _ WE4) as (_ & _ & _ & WI4 & _). unfold kIArenaLen in WI4, CIA.
  assert (AK5 : AKern E0 ax5 mo6) by (subst ax5; unfold xfer_st; apply (AKern_ext E0 a4); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK4]).
  assert (GB : forall b, In b gq5 -> bok lo T b /\ ae_resv_beg E0 <= b_addr b /\ b_addr b + 8192 + 4096 <= ae_resv_beg E0 + 137439023104).
  { intros b Hb. assert (Hb5 : In b (as_tq ax5 ++ as_gq ax5)) by (rewrite Egq5; apply in_app_iff; right; exact Hb).
    split; [exact (wf_bok E0 [] ax5 mo6 lo WF5 AK5 LOC b Hb5)|].
    pose proof WF5 as (_ & WR5 & _ & _ & WQ5 & _). assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
    destruct (batch_block E0 [] ax5 b WQ5 ltac:(unfold all_batches; rewrite app_assoc, app_nil_r; exact Hb5)) as (CV & _).
    pose proof (carved_in_space E0 ax5 kBatchClass _ HB24 WR5 CV) as [I1 I2]. change (class_size kBatchClass) with 8192 in I2. unfold kRegionSize in I1. unfold kSpaceSize in I2.
    replace (ae_space_beg E0) with SB in I1, I2 by reflexivity. clear -I1 I2 G1 G3. lia. }
  (* [comment removed for export] *)
  set (BIGW := [(usp - 80 + -96, usp - 80); (0xab2c8, 0xab2cc); (0xab2d0, 0xab2f0); (T + 80, T + 112)] ++ map (fun x => (x + 0, x + 0 + 8192)) (map b_addr gq5)).
  assert (MU68 : munch BIGW m6 m8).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU7]| eapply munch_weaken; [| exact MU8]]; intros z Hz; apply (proj2 (outside_forall _ _)); intros lo' hi' Hin;
      pose proof (proj1 (outside_forall _ _) Hz) as OZ.
    - unfold drainWu in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      + cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
          [ pose proof (OZ (usp - 80 + -96) (usp - 80) ltac:(left; reflexivity)) | pose proof (OZ 0xab2c8 0xab2cc ltac:(right; left; reflexivity))
          | pose proof (OZ 0xab2d0 0xab2f0 ltac:(do 2 right; left; reflexivity)) | pose proof (OZ (T + 80) (T + 112) ltac:(do 3 right; left; reflexivity)) ]; clear -H; lia.
      + destruct (BF_deallocT2.snoc_case (as_gq a4)) as [Eg|(lq & bq & Eg)]; rewrite Eg in Hin; [destruct Hin|].
        assert (INbq : In bq gq5) by (subst gq5; rewrite Eg; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
        rewrite BF_deallocT2.list_last_snoc in Hin.
        pose proof (OZ (b_addr bq + 0) (b_addr bq + 0 + 8192) ltac:(apply in_app_iff; right; apply in_map_iff; exists (b_addr bq); split; [reflexivity| apply in_map; exact INbq])) as X.
        destruct lq; cbn [app] in Hin; (destruct Hin as [E|[]]; injection E as <- <-; clear -X; lia).
    - unfold rheadW in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      + cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-;
          [ pose proof (OZ (usp - 80 + -96) (usp - 80) ltac:(left; reflexivity)) | pose proof (OZ 0xab2c8 0xab2cc ltac:(right; left; reflexivity))
          | pose proof (OZ 0xab2d0 0xab2f0 ltac:(do 2 right; left; reflexivity)) ]; clear -H; lia.
      + exact (OZ lo' hi' ltac:(apply in_app_iff; right; exact Hin)). }
  assert (AGO : forall z, 0 <= z < 2^64 -> (z < usp - 176 \/ usp - 80 <= z) -> (z < 0xab2c8 \/ 0xab2cc <= z) -> (z < 0xab2d0 \/ 0xab2f0 <= z) -> (z < T + 80 \/ T + 112 <= z) ->
                 (forall b, In b gq5 -> z < b_addr b \/ b_addr b + 8192 <= z) -> m8 (wa z) = m6 (wa z)).
  { intros z Hz Z1 Z2 Z3 Z4 Z5. apply MU68. rewrite wa_unsigned by exact Hz. apply (proj2 (outside_forall _ _)). intros lo' hi' Hin.
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    - cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; clear -Z1 Z2 Z3 Z4; lia.
    - apply in_map_iff in Hin. destruct Hin as (x & E & Hin). injection E as <- <-. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). pose proof (Z5 b Hb). clear -H. lia. }
  assert (AG68 : forall z, 0 <= z < 2^64 -> ~ BF_deallocT4.FPW4 E0 gq5 lo z -> m8 (wa z) = m6 (wa z)).
  { intros z Hz NF. unfold BF_deallocT4.FPW4, ae_instance in NF. rewrite IC0_T7 in NF. cbn [aic_instance both_ic] in NF. unfold kInsQMutex, kInsQGlobal, kThrQCache in NF.
    apply AGO; [exact Hz| clear -NF LO; unfold K_FREE in LO; lia| clear -NF; lia| clear -NF; lia| clear -NF; lia|].
    intros b Hb. destruct (Z_lt_le_dec z (b_addr b)) as [X|X]; [left; exact X|]. destruct (Z_lt_le_dec z (b_addr b + 8192)) as [Y|Y]; [| right; exact Y].
    exfalso. apply NF. do 4 right. exists b. split; [exact Hb| clear -X Y; lia]. }
  assert (REP6 : ARep bsegs E0 (DepotR bsegs E0) ax6 m8).
  { subst ax6 ax5. apply (R4 a4 m6 m8 lo gq1 emp popped kept TQNE REP4 WF4 RENV4 (wmono_trans _ _ _ _ WM7 WM8) AG68 LOC MRG POP);
      unfold ae_instance; rewrite ?IC0_T7; cbn [aic_instance both_ic]; unfold kInsQMutex, kInsQGlobal, kThrQCache; [exact QM8| exact GQ8| | exact BCk| exact BIk].
    eapply (rw_cells_agree bsegs m7 m8); [| exact QC7]. cbn. intros z Hz. apply MU8. rewrite wa_unsigned by (clear -Hz Tlo Thi CR; lia).
    unfold rheadW. apply (proj2 (outside_forall _ _)). intros lo' hi' Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear -Hz LO LOC Timg Thi; unfold K_FREE in LO; lia.
    + apply in_map_iff in Hin. destruct Hin as (x & E & Hin). injection E as <- <-. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb).
      destruct (GB b Hb) as ((_ & _ & B3 & _) & _). clear -Hz B3. lia. }
  (* [comment removed for export] *)
  assert (LIVE4 : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (p - 16 + 16, cm_n cm) -> In (blo, bsz) (live_blocks a4)).
  { intros blo bsz LIVEb NEb. destruct (BF_deallocT2.live_block_other E0 [] [] a (p - 16) cm blo bsz Hwf Hcm' LIVEb ltac:(rewrite UB'; replace (p - 16 + 16) with p in NEb by (clear; lia); exact NEb)) as (cb' & cmc & ic & H' & NE' & <- & <- & ST').
    apply (BF_deallocT2.chunk_live_in a4 cb' cmc ic); [| exact ST']. rewrite E4c. unfold AsanRepFlipB.s3. cbn [as_chunks upd_chunks]. rewrite lookup_insert_ne by (clear -NE'; congruence). rewrite D14. exact H'. }
  assert (PLIVE : Permutation (live_blocks a) ((p - 16 + 16, cm_n cm) :: live_blocks ax6)).
  { replace (live_blocks ax6) with (live_blocks a4) by (subst ax6 ax5; reflexivity).
    unfold live_blocks, chunk_list. rewrite E4c. unfold AsanRepFlipB.s3. cbn [as_chunks upd_chunks]. rewrite D14. replace (p - 16 + 16) with p by (clear; lia).
    pose proof (BF_deallocT3.live_blocks_flip a (p - 16) cm aid fid Hcm' ST) as PM. unfold live_blocks, chunk_list in PM. cbn [as_chunks upd_chunks] in PM. rewrite UB' in PM. exact PM. }
  destruct RUNd as (fd & orcd & evsd & orcd' & RUNd). destruct RUNe as (fe & orce & evse & orce' & RUNe).
  assert (GE5 : kBatchSize * zlen (as_gq ax5) <= gq_bytes ax5).
  { unfold gq_bytes. apply (qbytes_ge E0 [] [] ax5 (as_gq ax5) WF5). intros b Hb. apply in_app_iff. right. exact Hb. }
  pose proof (BF_kit3.rwc_split bsegs m8 _ [C8 (wz (blen D)); C8 (wz (bhd D)); C8 (wz (blast D)); C8 (wz (qbytes D))] _ FR8) as [TC8 FRR8].
  cbn [cells_size csize Z.add Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRR8. replace (usp - 160 + 32) with (usp - 128) in FRR8 by (clear; lia).
  pose proof (proj1 (Forall_app _ _ _) OK8) as [OKk OKd].
  assert (QBD : qbytes D <= 2^30).
  { pose proof (rmerge_bytes gq5 gq1 emp MRG) as MB. pose proof (pop_prefix_app gq1 (qbytes gq1) kQuarantineMin) as SPLIT. rewrite POP in SPLIT. cbn [fst snd] in SPLIT.
    rewrite <- SPLIT, BF_qkit.qbytes_app in MB. pose proof (BF_qkit.qbytes_nonneg lo T kept OKk) as QK0.
    assert (Q5 : qbytes gq5 = gq_bytes a4 + tq_bytes a4) by (subst gq5; unfold gq_bytes, tq_bytes; apply BF_qkit.qbytes_app).
    subst D. rewrite BF_qkit.qbytes_app. unfold kQuarantineMax in GQ4. unfold kThreadQuarantineMax in TQ4. clear -MB QK0 Q5 GQ4 TQ4. lia. }
  (* [comment removed for export] *)
  assert (KONT' : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     dealloc_post_state E0 FSB0 HR0 L0 RES0 EB0 PL0 a a' m m' mo mo' s C C' (p - 16 + 16) (cm_n cm) lo usp (bst_key len ws) ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K).
  { intros until a'. replace (p - 16 + 16) with p by (clear; lia). apply KONT. }
  eapply (loop_entry s mo m lo usp C C' (p - 16) B (bst_key len ws) K cm a4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x8 x9 x18 x19 x20 F fc
            KN eq_refl AIV FB LOC LO SPA SPH TP E4s HCB HNHI HNLO KONT' D ax6 m8 mo8); [| exact SK8].
  unfold LINV. cbn [aps_alloc].
  split; [exact WF6|]. split; [exact REP6|].
  split; [subst ax6 ax5; unfold xfer_st; apply (AKern_ext E0 a4); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact (AKern_frame _ _ _ _ Fvm8 Flz8 (AKern_frame _ _ _ _ Fvm7 Flz7 AK4))]|].
  split; [apply (res_ok_frame a4); [subst ax6 ax5; cbn; intros sc H; exact H| subst ax6 ax5; cbn; apply incl_refl| exact RES4]|].
  split; [revert DI4; subst ax6 ax5; clear; unfold depot_inv, depot_n_ids, dphi; exact (fun H => H)|].
  split; [revert SS4; subst ax6 ax5; clear; unfold sstats_ok, sec_bytes; exact (fun H => H)|].
  split; [intros k cmk Hk; exact (CS4 k cmk Hk)|].
  split; [exact (BI_to_detach a a2 a4 (p - 16) cm aid (bst_key len ws) fid fd orcd evsd orcd' fe orce evse orce' gq1 emp popped kept Hbinv Hqb Hcm' RUNd RUNe WF5 ltac:(rewrite Egq5; exact MRG) POP)|].
  split; [subst ax6; reflexivity|].
  split; [subst ax6 ax5; unfold gq_bytes, xfer_st; cbn [as_gq upd_gq upd_tq]; unfold kQuarantineMin in QK; unfold kQuarantineMax; clear -QK; lia|].
  split. { apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 (C - 1) (C' - DSLACK) s a4 ax6 mo8).
           - exact (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK4 AG7 KIA7) AG8 KIA8).
           - subst ax6 ax5. unfold same_fp. repeat split; reflexivity.
           - subst ax6 ax5; reflexivity. - subst ax6 ax5; reflexivity. }
  split; [rewrite Ffs8, Ffs7; exact Ffs6|]. split; [rewrite Ffds8, Ffds7; exact Ffds6|]. split; [rewrite Ftid8, Ftid7; exact Ftid6|].
  split; [subst ax6 ax5; cbn; exact E4np|]. split; [subst ax6 ax5; cbn; exact E4res|]. split; [subst ax6 ax5; cbn; rewrite E4nd; exact ND2|].
  split; [subst ax6 ax5; reflexivity|]. split; [subst ax6 ax5; reflexivity|]. split; [subst ax6 ax5; cbn; rewrite E4s; intros sc H; exact H|].
  split; [exact PLIVE|]. split; [exact LIVE6|].
  split. { intros a' fr orcr evsr orcr' RUN. subst ax6.
           exact (arun_afree_core_recycle E0 a a2 a4 (p - 16) cm aid (bst_key len ws) fid fd orcd evsd orcd' fe orce evse orce' gq1 emp popped kept fr orcr a' evsr orcr'
                    Hcm' ST ltac:(rewrite UB'; clear; lia) RUNd RUNe GT GTQ GE5 ltac:(rewrite Egq5; exact MRG) POP RUN). }
  split; [exact MI8|].
  split. { apply (rt_misc5_agree E0 FSB0 PL0 m6 m8 RT6). intros z Hz.
           destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
           - apply AGO; [clear -ZI; lia| clear -ZI LO LOC CR; unfold K_FREE in LO; lia| | | clear -ZI Timg Tlo; lia|].
             + destruct (Z_lt_le_dec z 0xab2c8) as [X|X]; [left; exact X|]. destruct (Z_lt_le_dec z 0xab2cc) as [Y|Y]; [| right; exact Y].
               exfalso. apply NM. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear -X Y; lia].
             + destruct (Z_lt_le_dec z 0xab2d0) as [X|X]; [left; exact X|]. destruct (Z_lt_le_dec z 0xab2f0) as [Y|Y]; [| right; exact Y].
               exfalso. apply NM. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear -X Y; lia].
             + intros b Hb. destruct (GB b Hb) as ((B1 & _) & _). left. clear -ZI B1. lia.
           - unfold rt_high2 in RH. apply AGO; [clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia| clear -RH LO LOC Thi CQ2 CC2 DQ2 DD2; unfold K_FREE in LO; lia| | | clear -RH CT DT; lia|].
             + clear -RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
             + clear -RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
             + intros b Hb. destruct (GB b Hb) as ((B1 & B2 & B3 & _) & R1 & R2). clear -RH B1 B2 B3 R1 R2 CRS DRS CC1 CC2 DD1 DD2 CIA WI4. lia. }
  split. { unfold put_frame in PF6 |- *. fold usp in PF6 |- *. eapply (rw_cells_agree bsegs m6 m8); [| exact PF6]. cbn. intros z Hz.
           apply AGO; [clear -Hz USPR LO LOC CR; unfold K_FREE in LO; lia| clear -Hz; lia| clear -Hz LO LOC CR; unfold K_FREE in LO; lia| clear -Hz LO LOC CR; unfold K_FREE in LO; lia| clear -Hz LO LOC Thi; unfold K_FREE in LO; lia|].
           intros b Hb. destruct (GB b Hb) as ((_ & B2 & _) & _). right. clear -Hz B2 LO. unfold K_FREE in LO. lia. }
  split; [exact TC8|]. split; [exact FRR8|]. split; [exact BCd|]. split; [exact BId|]. split; [exact OKd|].
  split; [unfold bapart in AP8 |- *; rewrite map_app in AP8; exact (apl_app_r _ _ AP8)|]. split; [exact QBD|].
  destruct MUW as (W & MU & AWOK & AVOID). exists (W ++ BIGW). split; [| split; apply Forall_app; split; [exact AWOK| | exact AVOID|]].
  - eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU68]]; intros z Hz;
      apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin.
  - subst BIGW. apply Forall_app. split.
    + repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
      * left. clear -LO. unfold K_FREE in LO. lia.
      * right; left. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear; lia].
      * right; left. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear; lia].
      * right; right; left. exists (T + kThrQCache, 32). split; [unfold arep_thr_ranges; do 2 right; left; reflexivity| cbn [fst snd]; unfold kThrQCache; clear; lia].
    + apply Forall_forall. intros iv Hin. apply in_map_iff in Hin. destruct Hin as (x & <- & Hin). apply in_map_iff in Hin. destruct Hin as (b & <- & Hb).
      destruct (GB b Hb) as (_ & R1 & R2). unfold aw_ok. cbn [fst snd]. do 3 right; left. change kResvLen with 137439023104. clear -R1 R2. lia.
  - subst BIGW. apply Forall_app. split.
    + repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
        destruct (BF_casT.live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (BF_caT.live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT]|]); [.. | apply Forall_nil].
      * right; right. clear -Lw1 LOC LO. unfold K_FREE in LO. lia.
      * right. pose proof WE4 as (_ & WEhi & WErs & _). rewrite KHB in WEhi. destruct Lw3 as [[S1 _]|(sc & Hsc & S1 & S2)]; [clear -S1 WEhi WErs Lw0 G1; lia|].
        pose proof Hwf as (_ & _ & _ & _ & _ & (_ & _ & WS3a & _) & _). destruct (WS3a sc Hsc) as (_ & _ & _ & _ & _ & _ & SR).
        pose proof (SR _ (proj1 (wf_env_img _ (proj1 Hwf)))) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -X1 S1 S2 Lw0 EI2. lia.
      * right. pose proof WE4 as (_ & WEhi & WErs & _). rewrite KHB in WEhi. destruct Lw3 as [[S1 _]|(sc & Hsc & S1 & S2)]; [clear -S1 WEhi WErs Lw0 G1; lia|].
        pose proof Hwf as (_ & _ & _ & _ & _ & (_ & _ & WS3a & _) & _). destruct (WS3a sc Hsc) as (_ & _ & _ & _ & _ & _ & SR).
        pose proof (SR _ (proj1 (wf_env_img _ (proj1 Hwf)))) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -X1 S1 S2 Lw0 EI2. lia.
      * right. clear -BT. lia.
    + apply Forall_forall. intros iv Hin. apply in_map_iff in Hin. destruct Hin as (x & <- & Hin). apply in_map_iff in Hin. destruct Hin as (b & <- & Hb).
      cbn [fst snd]. intros blo bsz LIVEb NEb.
      assert (INb4 : In b (as_tq a4 ++ as_gq a4)) by (subst gq5; apply in_app_iff in Hb; apply in_app_iff; clear -Hb; tauto).
      pose proof (BF_deallocT2.batch_vs_live E0 [] a4 b blo bsz WF4 INb4 (LIVE4 blo bsz LIVEb NEb)) as BV. right. clear -BV. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem dealloc_srz_closed : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> dealloc_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof. intros ENV_depot. exact (BF_deallocT5.dealloc_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok EB0_ok ENV_depot ENV0 PL0OK L0OK R3 recycle_srz). Qed.
End DeallocT7.
End RC__1.
