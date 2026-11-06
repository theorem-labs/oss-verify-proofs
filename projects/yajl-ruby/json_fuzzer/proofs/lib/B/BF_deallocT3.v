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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf9 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHitB AsanRepCaB AsanRepX AsanFrame AsanRepFlipB AsanRealloc AsanRefillMB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_poison BF_free_kit BF_qkit BF_free1 BF_free1b BF_free1e BF_free1c BF_free1d BF_free3 BF_free4 B_policy5 B_slack5 B_budget5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 B_bframe BF_alloc_iface BF_dput_iface BF_free_iface BF_refill_iface BF_tkit BF_ainv_kit BX_unreg BX_Exit BF_statics BF_caT BF_casT BF_refill_room BF_deallocT1 BF_deallocT2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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

(* [comment removed for export] *)
Lemma live_blocks_flip : forall (sx : astate) cb cm aid fid,
  as_chunks sx !! cb = Some cm -> cm_state cm = CAllocated aid ->
  Permutation (live_blocks sx) ((cm_user_beg cm, cm_n cm) :: live_blocks (upd_chunks (fun mm => <[cb := flipped cm aid fid]> mm) sx)).
Proof.
  intros sx cb cm aid fid Hcm ST. unfold live_blocks, chunk_list. cbn [as_chunks upd_chunks].
  set (f := fun p : Z * chunkmeta => match cm_state (snd p) with CAllocated _ => true | CQuarantined _ _ => false end).
  set (g := fun p : Z * chunkmeta => (cm_user_beg (snd p), cm_n (snd p))).
  pose proof (map_to_list_delete (as_chunks sx) cb cm Hcm) as P1.
  assert (P2 : map_to_list (<[cb := flipped cm aid fid]> (as_chunks sx)) ≡ₚ (cb, flipped cm aid fid) :: map_to_list (delete cb (as_chunks sx))).
  { rewrite <- (insert_delete_eq (as_chunks sx) cb (flipped cm aid fid)). apply map_to_list_insert. apply lookup_delete_eq. }
  etransitivity.
  { apply Permutation_map. apply Permutation_filterb. symmetry. exact P1. }
  cbn [List.filter map]. subst f. cbn [snd]. rewrite ST. cbn [map]. apply perm_skip.
  symmetry. etransitivity.
  { apply Permutation_map. apply Permutation_filterb. exact P2. }
  cbn [List.filter map snd flipped cm_state]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arun_afree_core_ret : forall E (sx a2 a4 : astate) cb cm aid key fid fd orcd evsd orcd' fe orce evse orce',
  as_chunks sx !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  arun fd (depot_put E key (upd_ts (ts_on_free (cm_n cm)) sx)) orcd = Some (a2, ONorm fid, evsd, orcd') ->
  arun fe (enqueue E cb (cm_n cm) (AsanRepFlipB.s3 a2 cb cm aid fid)) orce = Some (a4, ONorm tt, evse, orce') ->
  tq_bytes a4 <= kThreadQuarantineMax ->
  exists fuel orc evs orc', arun fuel (afree_core E key (cb + 16) sx) orc = Some (a4, ONorm tt, evs, orc').
Proof.
  intros E sx a2 a4 cb cm aid key fid fd orcd evsd orcd' fe orce evse orce' Hcm ST UB RUNd RUNe TQ.
  destruct (arun_orc_app2 _ _ _ _ _ _ _ RUNd) as (ud & _ & Rd). destruct (arun_orc_app2 _ _ _ _ _ _ _ RUNe) as (ue & _ & Re).
  exists (fd + (fe + 0))%nat, (ud ++ ue), (evsd ++ (evse ++ [])), [].
  unfold afree_core. eapply arun_bind_pl; [apply arun_aget|]. cbv beta zeta.
  unfold kChunkHeaderSize. replace (cb + 16 - 16) with cb by lia. rewrite Hcm, ST, UB, Z.eqb_refl. cbn [negb].
  eapply arun_bind_pl; [apply arun_aupd|].
  eapply arun_abind; [apply (Rd ue)|].
  eapply arun_bind_pl; [apply arun_aupd|].
  eapply arun_abind; [pose proof (Re []) as X; rewrite app_nil_r in X; exact X|].
  unfold drain_if_needed. eapply arun_bind_pl; [apply arun_aget|]. cbv beta.
  replace (kThreadQuarantineMax <? tq_bytes a4) with false by (symmetry; apply Z.ltb_ge; exact TQ). apply arun_aret.
Qed.

(* [comment removed for export] *)
Section DeallocT3.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation INST := 0xaaf58.
#[local] Notation PP := (BF_deallocT1.PP E0 FSB0 HR0).

(* [comment removed for export] *)
Definition QD_post (s : aps) (mo : Model) (m : mem) (usp lo cb B C C' : Z) (key : list Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (K : TSet) : Prop :=
    forall (t0 t1 t2 a4' a5 a6 a7 t3 t4 t5 t6 : word) (m6 : mem) (mo6 : Model) (a2 a4 : astate) (cm : chunkmeta) (aid fid : Z),
  let a := aps_alloc s in let n := cm_n cm in let a3 := AsanRepFlipB.s3 a2 cb cm aid fid in
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  (* [comment removed for export] *)
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> dsame (upd_ts (ts_on_free n) a) a2 -> as_ndepot_ins a2 = as_ndepot_ins a + 1 ->
  (exists fuel orc evs orc', arun fuel (enqueue E0 cb n a3) orc = Some (a4, ONorm tt, evs, orc')) ->
  as_chunks a4 = as_chunks a3 /\ as_sec a4 = as_sec a /\ as_ptr_committed a4 = as_ptr_committed a /\ as_gq a4 = as_gq a
  /\ as_nprim_ever a4 = as_nprim_ever a /\ as_residue a4 = as_residue a /\ as_ndepot_ins a4 = as_ndepot_ins a2
  /\ as_node_blocks a4 = as_node_blocks a2 /\ as_store_blocks a4 = as_store_blocks a2 /\ as_sec_stats a4 = as_sec_stats a ->
  AWf E0 [] [] a4 -> ARep bsegs E0 (DepotR bsegs E0) a4 m6 -> AKern E0 a4 mo6 ->
  RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo6 ->
  res_ok a4 -> gq_bytes a4 <= kQuarantineMax -> 0 <= tq_bytes a4 <= kThreadQuarantineMax + 2^28 -> depot_inv E0 a4 -> sstats_ok a4 -> csmall a4 ->
  m_fs mo6 = m_fs mo -> m_fds mo6 = m_fds mo -> m_tid mo6 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv bsegs m6 -> stk bsegs m6 lo (usp - 80) -> wmono bsegs m m6 -> rt_misc5 FSB0 PL0 E0 m6 ->
  (exists W, munch W m m6 /\ Forall (aw_ok E0 a a4 lo usp) W
             /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W) ->
  rw_cells bsegs m6 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m6 (T + 80) [C8 (wz (qcount (as_tq a4))); C8 (wz (list_first (as_tq a4))); C8 (wz (list_last (as_tq a4))); C8 (wz (tq_bytes a4))] ->
  kThreadQuarantineMax < tq_bytes a4 ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR (wz 0x36df4) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) (wz (INST + 728)) (wz (T + 80)) (wz (T + 208)) (wz B) a4' a5 a6 a7
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x34620) fc None m6 (seg_rom bsegs)) mo6) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xfer_st (a : astate) : astate := upd_tq (fun _ => []) (upd_gq (fun g => g ++ as_tq a) a).
(* [comment removed for export] *)
Definition FPWx (a : astate) (lo : Z) (z : Z) : Prop :=
     lo <= z \/ (ae_instance E0 + kInsQMutex <= z < ae_instance E0 + kInsQMutex + 4)
  \/ (ae_instance E0 + kInsQGlobal <= z < ae_instance E0 + kInsQGlobal + 32)
  \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (as_gq a <> [] /\ list_last (as_gq a) <= z < list_last (as_gq a) + 8).
Definition R3_stmt : Prop :=
  forall (a : astate) (m m' : mem) (lo : Z),
  let tq := as_tq a in let gq := as_gq a in
  tq <> [] -> ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] [] a -> renv_ok E0 a ->
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPWx a lo z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (ae_instance E0 + kInsQMutex) [C4 (wz 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsQGlobal)
    [C8 (wz (qcount gq + qcount tq)); C8 (wz (match gq with [] => list_first tq | _ => list_first gq end)); C8 (wz (list_last tq)); C8 (wz (gq_bytes a + tq_bytes a))] ->
  rw_cells bsegs m' (T + kThrQCache) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  (forall l0 b0, gq = l0 ++ [b0] -> rw_cells bsegs m' (b_addr b0) [C8 (wz (list_first tq))]) ->
  ARep bsegs E0 (DepotR bsegs E0) (xfer_st a) m'.
Hypothesis R3 : R3_stmt.

(* [comment removed for export] *)
Lemma drain_cells : forall (ax : astate) (m : mem) (P : list Z),
  ARep bsegs E0 (DepotR bsegs E0) ax m -> AWf E0 P [] ax -> ae_ic E0 = both_ic ->
  let gq := as_gq ax in
     rw_cells bsegs m 0xab2c8 [C4 (wz 0)]
  /\ rw_cells bsegs m 0xab2d0 [C8 (wz (qcount gq)); C8 (wz (list_first gq)); C8 (wz (list_last gq)); C8 (wz (gq_bytes ax))]
  /\ rw_cells bsegs m 0xab270 [C8 (wz kQuarantineMax); C8 (wz kQuarantineMin); C8 (wz kThreadQuarantineMax)]
  /\ (forall l b, gq = l ++ [b] ->
        list_last gq = b_addr b /\ 1 <= qcount gq
        /\ rw_cells bsegs m (b_addr b) [C8 (wz 0); C8 (wz (b_size b)); C8 (wz (zlen (b_items b)))]
        /\ wf_batch E0 [] ax b /\ 1 <= zlen (b_items b)).
Proof.
  intros ax m P REP WF IC0. cbv zeta.
  pose proof REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rins as (_ & _ & _ & _ & _ & _ & _ & I8 & I9 & I10 & _).
  unfold ae_instance in I8, I9, I10. rewrite IC0 in I8, I9, I10. cbn [aic_instance both_ic kInsQuarantine kInsQMutex kInsQGlobal Z.add] in I8, I9, I10.
  split; [exact I9|]. split; [exact I10|]. split; [exact I8|].
  intros l b Hgq.
  assert (INb : In b (as_tq ax ++ as_gq ax)) by (rewrite Hgq; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
  pose proof WF as (_ & _ & _ & _ & (Q1 & _) & _). destruct (Q1 b INb) as [WB B1].
  split; [rewrite Hgq; apply list_last_snoc|]. split; [unfold qcount; rewrite Hgq, length_app; cbn [length]; clear; lia|].
  destruct Rbat as [_ RBg]. rewrite Hgq in RBg. pose proof (arep_batch_list_snoc ax l b m RBg) as [HB _].
  split; [exact HB|]. split; [exact WB| exact B1].
Qed.

(* [comment removed for export] *)
Lemma gq_weights : forall E P D sx, AWf E P D sx -> kBatchSize * qcount (as_gq sx) <= gq_bytes sx /\ kBatchSize * qcount (as_tq sx) <= tq_bytes sx.
Proof.
  intros E P D sx WF. unfold gq_bytes, tq_bytes, qcount. unfold zlen.
  split; [apply (qbytes_ge E P D sx (as_gq sx) WF); intros x Hx; apply in_app_iff; right; exact Hx
        | apply (qbytes_ge E P D sx (as_tq sx) WF); intros x Hx; apply in_app_iff; left; exact Hx].
Qed.

(* [comment removed for export] *)
Lemma arun_afree_core_xfer : forall E (sx a2 a4 : astate) cb cm aid key fid fd orcd evsd orcd' fe orce evse orce',
  as_chunks sx !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  arun fd (depot_put E key (upd_ts (ts_on_free (cm_n cm)) sx)) orcd = Some (a2, ONorm fid, evsd, orcd') ->
  arun fe (enqueue E cb (cm_n cm) (AsanRepFlipB.s3 a2 cb cm aid fid)) orce = Some (a4, ONorm tt, evse, orce') ->
  kThreadQuarantineMax < tq_bytes a4 -> gq_bytes a4 + tq_bytes a4 <= kQuarantineMax ->
  exists fuel orc evs orc', arun fuel (afree_core E key (cb + 16) sx) orc = Some (xfer_st a4, ONorm tt, evs, orc').
Proof.
  intros E sx a2 a4 cb cm aid key fid fd orcd evsd orcd' fe orce evse orce' Hcm ST UB RUNd RUNe TQ GQ.
  destruct (arun_orc_app2 _ _ _ _ _ _ _ RUNd) as (ud & _ & Rd). destruct (arun_orc_app2 _ _ _ _ _ _ _ RUNe) as (ue & _ & Re).
  exists (fd + (fe + 0))%nat, (ud ++ ue), (evsd ++ (evse ++ [])), [].
  unfold afree_core. eapply arun_bind_pl; [apply arun_aget|]. cbv beta zeta.
  unfold kChunkHeaderSize. replace (cb + 16 - 16) with cb by lia. rewrite Hcm, ST, UB, Z.eqb_refl. cbn [negb].
  eapply arun_bind_pl; [apply arun_aupd|].
  eapply arun_abind; [apply (Rd ue)|].
  eapply arun_bind_pl; [apply arun_aupd|].
  eapply arun_abind; [pose proof (Re []) as X; rewrite app_nil_r in X; exact X|].
  unfold drain_if_needed. eapply arun_bind_pl; [apply arun_aget|]. cbv beta.
  replace (kThreadQuarantineMax <? tq_bytes a4) with true by (symmetry; apply Z.ltb_lt; exact TQ).
  eapply arun_bind_pl; [apply arun_aupd|]. eapply arun_bind_pl; [apply arun_aget|]. cbv beta.
  replace (kQuarantineMax <? gq_bytes (upd_tq (fun _ => []) (upd_gq (fun g => g ++ as_tq a4) a4))) with false.
  2:{ symmetry. apply Z.ltb_ge. unfold gq_bytes in GQ |- *. unfold tq_bytes in GQ. cbn [as_gq upd_tq upd_gq]. rewrite qbytes_app. exact GQ. }
  apply arun_aret.
Qed.

(* [comment removed for export] *)
Lemma putback_srz :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (lo B C C' : Z) (key : list Z) (K : TSet)
         (t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 : word) (m6 : mem) (mo6 : Model) (a2 a4 : astate) (cm : chunkmeta) (aid fid cb : Z),
  let a := aps_alloc s in let usp := bv_unsigned sp in let n := cm_n cm in let a3 := AsanRepFlipB.s3 a2 cb cm aid fid in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> 1 <= C -> FSLACK <= C' -> AINVc a m mo -> fbudget_pre a -> In (cb + 16, n) (live_blocks a) ->
  alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 -> usp < 2^47 -> tp = wz 0x5e1550 ->
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  (* [comment removed for export] *)
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> dsame (upd_ts (ts_on_free n) a) a2 -> as_ndepot_ins a2 = as_ndepot_ins a + 1 ->
  (exists fuel orc evs orc', arun fuel (enqueue E0 cb n a3) orc = Some (a4, ONorm tt, evs, orc')) ->
  as_chunks a4 = as_chunks a3 /\ as_sec a4 = as_sec a /\ as_ptr_committed a4 = as_ptr_committed a /\ as_gq a4 = as_gq a
  /\ as_nprim_ever a4 = as_nprim_ever a /\ as_residue a4 = as_residue a /\ as_ndepot_ins a4 = as_ndepot_ins a2
  /\ as_node_blocks a4 = as_node_blocks a2 /\ as_store_blocks a4 = as_store_blocks a2 /\ as_sec_stats a4 = as_sec_stats a ->
  AWf E0 [] [] a4 -> ARep bsegs E0 (DepotR bsegs E0) a4 m6 -> AKern E0 a4 mo6 ->
  RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo6 ->
  res_ok a4 -> gq_bytes a4 <= kQuarantineMax -> 0 <= tq_bytes a4 <= kThreadQuarantineMax + 2^28 -> depot_inv E0 a4 -> sstats_ok a4 -> csmall a4 ->
  m_fs mo6 = m_fs mo -> m_fds mo6 = m_fds mo -> m_tid mo6 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv bsegs m6 -> stk bsegs m6 lo (usp - 80) -> wmono bsegs m m6 -> rt_misc5 FSB0 PL0 E0 m6 ->
  (exists W, munch W m m6 /\ Forall (aw_ok E0 a a4 lo usp) W
             /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W) ->
  rw_cells bsegs m6 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m6 (T + 80) [C8 (wz (qcount (as_tq a4))); C8 (wz (list_first (as_tq a4))); C8 (wz (list_last (as_tq a4))); C8 (wz (tq_bytes a4))] ->
  
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a0x a1x a2x a3x a4x a5x a6x a7x t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     dealloc_post_state E0 FSB0 HR0 L0 RES0 EB0 PL0 a a' m m' mo mo' s C C' (cb + 16) n lo usp key ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0x a1x a2x a3x a4x a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  QD_post s mo m usp lo cb B C C' key ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc K ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR (wz 0x36ebc) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) a0' a1' a2' a3' a4' a5 a6 a7
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x36ebc) fc None m6 (seg_rom bsegs)) mo6) K.
Proof.
  intros until cb. cbv zeta. intros KN TOK HC1 HCS AIV FB LIVE LOC LO SPA SPH TP.
  intros Hcm ST UB RUNd FID DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4 RES4 GQ4 TQ4 DI4 SS4 CS4 Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW PF6 QC6 KONT QDPOST.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof AIV as AIV0. destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  set (a := aps_alloc s) in *. set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range _ sp) as USPR. change (bv_modulus 64) with (2^64) in USPR. fold usp in USPR.
  unfold K_FREE in LO.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRr & CT & DT & CD & CIA).
  pose proof TRr as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  destruct (freed_chunk_facts E0 s mo m (cb + 16) (cm_n cm) Hrep Hwf Hkern EI1 EI2 LIVE)
    as (cm' & aid' & b1x & Hcm' & _ & _ & _ & _ & N40 & _ & _ & _ & _ & CB0 & CBC & CBB & P16 & CBT & _).
  replace (cb + 16 - 16) with cb in * by (clear; lia). clear Hcm' cm' aid' b1x.
  pose proof (rounded_ge (cm_n cm)) as (RG1 & RG2 & RG3).
  pose proof FLD as (E4c & E4s & E4p & E4g & E4np & E4res & E4nd & E4nb & E4sb & E4sst).
  pose proof DS2 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22).
  cbn [as_regions as_cache_inited as_cache as_cache_stale as_cache_allocated as_cache_mapped as_ptr_committed as_sec as_sec_stale as_sec_stats
       as_glob_allocated as_glob_mapped as_oom as_chunks as_dead as_tq as_gq as_ia_inited as_residue as_nprim_ever as_everc as_ts upd_ts]
    in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22.
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK4) as (R4 & R4' & ATK4 & _).
  assert (ENV4 : ENVOK E0 FSB0 (sA a4 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK4).
  pose proof (proj1 WF4) as WE4.
  set (P4 := PP (sA a4 s) mo6).
  pose proof (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a4 s) mo6 R4 R4' ATK4) as KIP4.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P4 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P4. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 (sA a4 s) mo6 AK4 WE4 ENV0); clear -H1 H2 LOC USPR CR; lia. }
  assert (PT : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P4 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P4. rewrite <- EPOL. apply (pol_thread' E0 FSB0 HR0 (sA a4 s) mo6 AK4 WE4); clear -H1 H2; lia. }
  assert (HTp : placed_s T 4096) by (unfold placed_s, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG; clear -Tlo Thi Timg Tband; repeat split; lia).
  assert (HL8b : 8 * ((cm_n cm + 7) / 8) < cm_n cm + 8 /\ cm_n cm <= rounded (cm_n cm)) by (clear -N40 RG1; Z.div_mod_to_equations; lia).
  assert (HCB : 0x603000 <= cb /\ cb + 16 + 8 * BF_free1d.l8 (cm_n cm) <= alloc_ceiling /\ cb mod 16 = 0).
  { unfold BF_free1d.l8. split; [exact CB0|]. split; [clear -CBC HL8b RG3; Z.div_mod_to_equations; lia| clear -P16; Z.div_mod_to_equations; lia]. }
  assert (HNHI : 0 <= cm_n cm / 2^32 < 256) by (clear -N40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (HNLO : 0 <= cm_n cm mod 2^32 < 2^32) by (clear; apply Z.mod_pos_bound; lia).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; clear -USPR LO LOC CR; lia).
  assert (RENV4 : renv_ok E0 a4).
  { split; [exact (blocks_sep_of E0 a4 mo6 ENV0 WF4 AK4)|]. split; [clear -Tlo Thi Timg; repeat split; lia|].
    split; [intros r Hr; pose proof (IMGR r Hr) as X; rewrite EI1; clear -X EI2; lia|]. split; [rewrite EI1; clear; lia|]. split; [exact IMGR|].
    split; [exact (img_depsep_asan E0 IC0)|]. split; [exists mo6; exact AK4|]. split; [exact TDN| exact DNP]. }
  destruct (Z_lt_le_dec kThreadQuarantineMax (tq_bytes a4)) as [GT|LE].
  - (* [comment removed for export] *)
    eapply (rzA_seg_cfg bsegs (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) P4).
    { replace (wz (usp - 80)) with (wz (bv_unsigned sp - 80) : word) by reflexivity.
      eapply (put_back_drain P4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m6 lo T B cb (cm_n cm / 2^32) (cm_n cm mod 2^32) (cm_n cm) LOC
                ltac:(fold usp; clear -SPH; lia) HTp HCB HNHI HNLO PSTK PT (tq_bytes a4) (qcount (as_tq a4)) (list_first (as_tq a4)) (list_last (as_tq a4)));
        rewrite ?Hsp; fold usp; [exact SK6| clear -LO; lia| exact MI6| unfold put_frame; fold usp; rewrite ?Hsp; exact PF6| exact QC6| unfold kThreadQuarantineMax in GT, TQ4; clear -GT TQ4; lia]. }
    { exact KIP4. }
    intros ms7 mo7 HQ7 AG7 KIP7. unfold put_drain_post in HQ7. rewrite ?Hsp in HQ7. fold usp in HQ7. subst ms7.
    pose proof (magree_frame _ _ AG7) as (Ffds7 & Fvm7 & Flz7 & Ffs7 & Fh7 & Ftid7 & _). destruct KIP7 as [KIA7 _].
    pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK4 AG7 KIA7) as TOK7. pose proof (AKern_frame _ _ _ _ Fvm7 Flz7 AK4) as AK7.
    unfold QD_post in QDPOST.
    eapply (QDPOST t0 t1 t2 a4' a5 a6 a7 t3 t4 t5 t6 m6 mo7 a2 a4 cm aid fid);
      [ exact Hcm | exact ST | exact UB | exact RUNd | exact FID | exact DS2 | exact ND2 | exact RUNe | exact FLD | exact WF4 | exact REP4 | exact AK7 | exact TOK7 | exact KIA7
      | exact RES4 | exact GQ4 | exact TQ4 | exact DI4 | exact SS4 | exact CS4
      | rewrite Ffs7; exact Ffs6 | rewrite Ffds7; exact Ffds6 | rewrite Ftid7; exact Ftid6
      | exact MI6 | exact SK6 | exact WM6 | exact RT6 | exact MUW | exact PF6 | exact QC6 | exact GT ].
  - (* [comment removed for export] *)
    eapply (rzA_seg_cfg bsegs (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) P4).
    { replace (wz (usp - 80)) with (wz (bv_unsigned sp - 80) : word) by reflexivity.
      eapply (put_back_ret P4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m6 lo T B cb (cm_n cm / 2^32) (cm_n cm mod 2^32) (cm_n cm) LOC
                ltac:(fold usp; clear -SPH; lia) HTp HCB HNHI HNLO PSTK PT (tq_bytes a4) (qcount (as_tq a4)) (list_first (as_tq a4)) (list_last (as_tq a4)));
        rewrite ?Hsp; fold usp; [exact SK6| clear -LO; lia| exact MI6| unfold put_frame; fold usp; rewrite ?Hsp; exact PF6| exact QC6| unfold kThreadQuarantineMax in LE; clear -LE TQ4; lia]. }
    { exact KIP4. }
    intros ms7 mo7 HQ7 AG7 KIP7. unfold put_ret_post in HQ7. fold usp in HQ7.
    destruct HQ7 as (m7 & -> & MU7 & WM7 & MI7 & SK7).
    pose proof (magree_frame _ _ AG7) as (Ffds7 & Fvm7 & Flz7 & Ffs7 & Fh7 & Ftid7 & _). destruct KIP7 as [KIA7 _].
    pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK4 AG7 KIA7) as TOK7. pose proof (AKern_frame _ _ _ _ Fvm7 Flz7 AK4) as AK7.
    assert (AG67 : forall z, m7 (wa z) = m6 (wa z)) by (intros z; apply MU7; exact I).
    pose proof RUNd as (fd & orcd & evsd & orcd' & RUNd1). pose proof RUNe as (fe & orce & evse & orce' & RUNe1).
    destruct (arun_afree_core_ret E0 a a2 a4 cb cm aid key fid fd orcd evsd orcd' fe orce evse orce' Hcm ST UB RUNd1 RUNe1 LE) as (fa & orca & evsa & orca' & RUNA).
    eapply KONT. unfold dealloc_post_state. fold a usp.
    split; [exact SK7|].
    split. { destruct MUW as (W & MU & FA & FL). exists W. split; [| split; [exact FA| exact FL]].
             eapply munch_trans; [exact MU|]. intros x Hx. apply MU7. exact I. }
    split; [exists fa, orca, evsa, orca'; exact RUNA|].
    split. { (* [comment removed for export] *)
      split. { apply (ARep_high_agree E0 [] [] a4 m6 m7 lo REP4 WF4 RENV4 LOC WM7). intros z _ _. apply AG67. }
      split; [exact WF4|]. split; [exact AK7|]. split; [exact RES4|]. split; [split; [exact LE| exact GQ4]|]. split; [exact DI4|].
      split. { unfold AsanBudget2.binv. exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (afree_core_cnt E0 a key (cb + 16) Hbinv Hqb) eq_refl RUNA). }
      split; [exact MI7|]. split; [apply (rt_misc5_agree E0 FSB0 PL0 m6 m7 RT6); intros z _; apply AG67|]. split; [exact SS4| exact CS4]. }
    split; [unfold FSLACK; unfold DSLACK in TOK7; exact TOK7|].
    split; [rewrite Ffs7; exact Ffs6|]. split; [rewrite Ffds7; exact Ffds6|]. split; [rewrite Ftid7; exact Ftid6|].
    split. { unfold facct. rewrite E4np, E4res, E4nd, ND2. clear. repeat split; lia. }
    unfold live_blocks, chunk_list. rewrite E4c. unfold AsanRepFlipB.s3. cbn [as_chunks upd_chunks]. rewrite D14. rewrite <- UB.
    pose proof (live_blocks_flip a cb cm aid fid Hcm ST) as PM. unfold live_blocks, chunk_list in PM. cbn [as_chunks upd_chunks] in PM. exact PM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition drainWu (usp : Z) (gq : list batch) : list (Z * Z) :=
  [(usp - 128, usp - 80); (0xab2c8, 0xab2cc); (0xab2d0, 0xab2f0); (T + 80, T + 112)] ++ (match gq with [] => [] | _ => [(list_last gq, list_last gq + 8)] end).

(* [comment removed for export] *)
Definition QR_post (s : aps) (mo : Model) (m : mem) (usp lo cb B C C' : Z) (key : list Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (K : TSet) : Prop :=
  forall (t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 : word) (m6 : mem) (mo6 : Model) (a2 a4 : astate) (cm : chunkmeta) (aid fid : Z),
  let a := aps_alloc s in let n := cm_n cm in let a3 := AsanRepFlipB.s3 a2 cb cm aid fid in
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  (* [comment removed for export] *)
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> dsame (upd_ts (ts_on_free n) a) a2 -> as_ndepot_ins a2 = as_ndepot_ins a + 1 ->
  (exists fuel orc evs orc', arun fuel (enqueue E0 cb n a3) orc = Some (a4, ONorm tt, evs, orc')) ->
  as_chunks a4 = as_chunks a3 /\ as_sec a4 = as_sec a /\ as_ptr_committed a4 = as_ptr_committed a /\ as_gq a4 = as_gq a
  /\ as_nprim_ever a4 = as_nprim_ever a /\ as_residue a4 = as_residue a /\ as_ndepot_ins a4 = as_ndepot_ins a2
  /\ as_node_blocks a4 = as_node_blocks a2 /\ as_store_blocks a4 = as_store_blocks a2 /\ as_sec_stats a4 = as_sec_stats a ->
  AWf E0 [] [] a4 -> ARep bsegs E0 (DepotR bsegs E0) a4 m6 -> AKern E0 a4 mo6 ->
  RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo6 ->
  res_ok a4 -> gq_bytes a4 <= kQuarantineMax -> 0 <= tq_bytes a4 <= kThreadQuarantineMax + 2^28 -> depot_inv E0 a4 -> sstats_ok a4 -> csmall a4 ->
  m_fs mo6 = m_fs mo -> m_fds mo6 = m_fds mo -> m_tid mo6 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv bsegs m6 -> stk bsegs m6 lo (usp - 80) -> wmono bsegs m m6 -> rt_misc5 FSB0 PL0 E0 m6 ->
  (exists W, munch W m m6 /\ Forall (aw_ok E0 a a4 lo usp) W
             /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W) ->
  rw_cells bsegs m6 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m6 (T + 80) [C8 (wz (qcount (as_tq a4))); C8 (wz (list_first (as_tq a4))); C8 (wz (list_last (as_tq a4))); C8 (wz (tq_bytes a4))] ->
  kThreadQuarantineMax < tq_bytes a4 ->
  forall (m7 : mem) (mo7 : Model) (t0' t1' a4x a5x a6x a7x : word),
  kQuarantineMax < gq_bytes a4 + tq_bytes a4 ->
  mem_inv bsegs m7 -> stk bsegs m7 lo (usp - 80) -> wmono bsegs m6 m7 -> munch (drainWu usp (as_gq a4)) m6 m7 ->
  magree mo6 mo7 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo7 ->
  rw_cells bsegs m7 0xab2c8 [C4 (wz 256)] ->
  rw_cells bsegs m7 0xab2d0 [C8 (wz (qcount (as_gq a4) + qcount (as_tq a4))); C8 (wz (match as_gq a4 with [] => list_first (as_tq a4) | _ => list_first (as_gq a4) end));
                          C8 (wz (list_last (as_tq a4))); C8 (wz (gq_bytes a4 + tq_bytes a4))] ->
  rw_cells bsegs m7 (T + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  (forall l0 b0, as_gq a4 = l0 ++ [b0] -> rw_cells bsegs m7 (b_addr b0) [C8 (wz (list_first (as_tq a4)))]) ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR (wz 0x36df4) (wz (usp - 80)) gp tp t0' t1' t2 (wz (INST + 728)) (wz (T + 80)) (wz (INST + 728)) (wz kQuarantineMin) (wz (T + 208)) (wz B) a4x a5x a6x a7x
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x347c4) fc None m7 (seg_rom bsegs)) mo7) K.

Lemma drain_srz :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (lo B C C' : Z) (key : list Z) (K : TSet)
         (t0 t1 t2 a4' a5 a6 a7 t3 t4 t5 t6 : word) (m6 : mem) (mo6 : Model) (a2 a4 : astate) (cm : chunkmeta) (aid fid cb : Z),
  let a := aps_alloc s in let usp := bv_unsigned sp in let n := cm_n cm in let a3 := AsanRepFlipB.s3 a2 cb cm aid fid in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> 1 <= C -> FSLACK <= C' -> AINVc a m mo -> fbudget_pre a -> In (cb + 16, n) (live_blocks a) ->
  alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 -> usp < 2^47 -> tp = wz 0x5e1550 ->
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  (* [comment removed for export] *)
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> dsame (upd_ts (ts_on_free n) a) a2 -> as_ndepot_ins a2 = as_ndepot_ins a + 1 ->
  (exists fuel orc evs orc', arun fuel (enqueue E0 cb n a3) orc = Some (a4, ONorm tt, evs, orc')) ->
  as_chunks a4 = as_chunks a3 /\ as_sec a4 = as_sec a /\ as_ptr_committed a4 = as_ptr_committed a /\ as_gq a4 = as_gq a
  /\ as_nprim_ever a4 = as_nprim_ever a /\ as_residue a4 = as_residue a /\ as_ndepot_ins a4 = as_ndepot_ins a2
  /\ as_node_blocks a4 = as_node_blocks a2 /\ as_store_blocks a4 = as_store_blocks a2 /\ as_sec_stats a4 = as_sec_stats a ->
  AWf E0 [] [] a4 -> ARep bsegs E0 (DepotR bsegs E0) a4 m6 -> AKern E0 a4 mo6 ->
  RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo6 ->
  res_ok a4 -> gq_bytes a4 <= kQuarantineMax -> 0 <= tq_bytes a4 <= kThreadQuarantineMax + 2^28 -> depot_inv E0 a4 -> sstats_ok a4 -> csmall a4 ->
  m_fs mo6 = m_fs mo -> m_fds mo6 = m_fds mo -> m_tid mo6 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv bsegs m6 -> stk bsegs m6 lo (usp - 80) -> wmono bsegs m m6 -> rt_misc5 FSB0 PL0 E0 m6 ->
  (exists W, munch W m m6 /\ Forall (aw_ok E0 a a4 lo usp) W
             /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W) ->
  rw_cells bsegs m6 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m6 (T + 80) [C8 (wz (qcount (as_tq a4))); C8 (wz (list_first (as_tq a4))); C8 (wz (list_last (as_tq a4))); C8 (wz (tq_bytes a4))] ->
  
  kThreadQuarantineMax < tq_bytes a4 ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a0x a1x a2x a3x a4x a5x a6x a7x t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     dealloc_post_state E0 FSB0 HR0 L0 RES0 EB0 PL0 a a' m m' mo mo' s C C' (cb + 16) n lo usp key ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0x a1x a2x a3x a4x a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  QR_post s mo m usp lo cb B C C' key ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc K ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR (wz 0x36df4) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) (wz (INST + 728)) (wz (T + 80)) (wz (T + 208)) (wz B) a4' a5 a6 a7
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x34620) fc None m6 (seg_rom bsegs)) mo6) K.
Proof.
  intros until cb. cbv zeta. intros KN TOK HC1 HCS AIV FB LIVE LOC LO SPA SPH TP.
  intros Hcm ST UB RUNd FID DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4 RES4 GQ4 TQ4 DI4 SS4 CS4 Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW PF6 QC6 GT KONT QRPOST.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof AIV as AIV0. destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  set (a := aps_alloc s) in *. set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range _ sp) as USPR. change (bv_modulus 64) with (2^64) in USPR. fold usp in USPR.
  unfold K_FREE in LO.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRr & CT & DT & CD & CIA).
  pose proof TRr as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  destruct (freed_chunk_facts E0 s mo m (cb + 16) (cm_n cm) Hrep Hwf Hkern EI1 EI2 LIVE)
    as (cm' & aid' & b1x & Hcm' & _ & _ & _ & _ & N40 & _ & _ & _ & _ & CB0 & CBC & CBB & P16 & CBT & _).
  replace (cb + 16 - 16) with cb in * by (clear; lia). clear Hcm' cm' aid' b1x.
  pose proof (rounded_ge (cm_n cm)) as (RG1 & RG2 & RG3).
  pose proof FLD as (E4c & E4s & E4p & E4g & E4np & E4res & E4nd & E4nb & E4sb & E4sst).
  pose proof DS2 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22).
  cbn [as_regions as_cache_inited as_cache as_cache_stale as_cache_allocated as_cache_mapped as_ptr_committed as_sec as_sec_stale as_sec_stats
       as_glob_allocated as_glob_mapped as_oom as_chunks as_dead as_tq as_gq as_ia_inited as_residue as_nprim_ever as_everc as_ts upd_ts]
    in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22.
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK4) as (R4 & R4' & ATK4 & _).
  assert (ENV4 : ENVOK E0 FSB0 (sA a4 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK4).
  pose proof (proj1 WF4) as WE4. pose proof WF4 as (_ & WR4 & _ & _ & _ & WS4 & _). destruct WS4 as (_ & _ & WS3 & _).
  set (P4 := PP (sA a4 s) mo6).
  pose proof (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a4 s) mo6 R4 R4' ATK4) as KIP4.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P4 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P4. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 (sA a4 s) mo6 AK4 WE4 ENV0); clear -H1 H2 LOC USPR CR; lia. }
  assert (PSTK80 : forall y k, lo <= y -> y + Z.of_nat k <= usp - 80 -> P4 (Z_to_bv 64 y, k)) by (intros y k H1 H2; apply PSTK; [exact H1| clear -H2; lia]).
  assert (PT : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P4 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P4. rewrite <- EPOL. apply (pol_thread' E0 FSB0 HR0 (sA a4 s) mo6 AK4 WE4); clear -H1 H2; lia. }
  assert (PDAT : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P4 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P4. rewrite <- EPOL. apply (pol_img' E0 FSB0 HR0 (sA a4 s) mo6 AK4 WE4 ENV4 ENV0); clear -H1 H2; lia. }
  assert (PUSR : forall y k, region_beg SB kBatchClass <= y -> y + Z.of_nat k <= region_beg SB kBatchClass + rg_mapped_user (get_region a4 kBatchClass) -> P4 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. destruct k as [|k']; [apply PP_zero|]. unfold P4. rewrite <- EPOL.
    apply (pol_user E0 FSB0 HR0 (sA a4 s) mo6 [] [] AK4 WF4 kBatchClass); [unfold kBatchClass, kLargestClassID; clear; lia| exact H1| exact H2| clear; lia]. }
  assert (Hsp : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; clear -USPR LO LOC CR; lia).
  (* [comment removed for export] *)
  pose proof (ak_resv_geom _ _ _ AK4) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (proj2 WR4 kBatchClass ltac:(unfold kBatchClass, kLargestClassID; clear; lia)) as (RG1' & RG2' & RG3' & _).
  cbv zeta in RG1', RG2', RG3'. unfold region_of in RG1', RG2', RG3'. change kFreeArrayOffset with 3758096384 in RG3'.
  assert (BLK : forall bb, carved E0 a4 kBatchClass bb ->
            region_beg SB kBatchClass <= bb /\ bb + 8192 <= region_beg SB kBatchClass + rg_mapped_user (get_region a4 kBatchClass)
            /\ kHighMemBeg <= bb /\ bb + 8192 <= alloc_ceiling /\ (bb + 8192 <= T \/ T + 4096 <= bb)
            /\ ae_resv_beg E0 <= bb /\ bb + 8192 + 4096 <= ae_resv_beg E0 + 137439023104).
  { intros bb (k & K0 & KE & KB). unfold region_of in KB. change (class_size kBatchClass) with 8192 in KE, KB.
    unfold region_beg, kBatchClass in *. change kRegionSize with 4294967296 in *. rewrite KHB.
    pose proof WE4 as (_ & WEhi & _ & _ & WEce & _). rewrite KHB in WEhi. pose proof (wf_env_thread _ WE4) as (_ & _ & _ & WT4 & _).
    clear -K0 KE KB RG1' RG3' G1 G2 G3 WT4 WEhi WEce CR. repeat split; lia. }
  (* [comment removed for export] *)
  destruct (drain_cells a4 m6 [] REP4 WF4 IC0) as (QMTX & GQc & QMAX & GLASTF).
  pose proof (gq_weights E0 [] [] a4 WF4) as [WG WT]. unfold kBatchSize in WG, WT. unfold kThreadQuarantineMax in GT, TQ4. unfold kQuarantineMax in GQ4.
  set (cnt := qcount (as_tq a4)) in *. set (gcnt := qcount (as_gq a4)) in *.
  assert (GCN : 0 <= gcnt) by (subst gcnt; unfold qcount; clear; lia).
  assert (LASTG : gcnt <> 0 -> exists lq bq, as_gq a4 = lq ++ [bq] /\ list_last (as_gq a4) = b_addr bq
            /\ rw_cells bsegs m6 (b_addr bq) [C8 (wz 0); C8 (wz (b_size bq)); C8 (wz (zlen (b_items bq)))]
            /\ (region_beg SB kBatchClass <= b_addr bq /\ b_addr bq + 8192 <= region_beg SB kBatchClass + rg_mapped_user (get_region a4 kBatchClass)
                /\ kHighMemBeg <= b_addr bq /\ b_addr bq + 8192 <= alloc_ceiling /\ (b_addr bq + 8192 <= T \/ T + 4096 <= b_addr bq)
                /\ ae_resv_beg E0 <= b_addr bq /\ b_addr bq + 8192 + 4096 <= ae_resv_beg E0 + 137439023104)
            /\ In bq (as_tq a4 ++ as_gq a4)).
  { intros NZ. destruct (snoc_case (as_gq a4)) as [E|(lq & bq & E)]; [exfalso; apply NZ; subst gcnt; rewrite E; reflexivity|].
    destruct (GLASTF lq bq E) as (EL & _ & LB & WB & _). pose proof WB as (CVb & _).
    exists lq, bq. split; [exact E|]. split; [exact EL|]. split; [exact LB|]. split; [exact (BLK _ CVb)|].
    rewrite E. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
  set (gfirst' := if gcnt =? 0 then list_first (as_tq a4) else list_first (as_gq a4)).
  assert (CNT1 : 0 < cnt).
  { destruct (snoc_case (as_tq a4)) as [E|(lq & bq & E)]; [exfalso; unfold tq_bytes in GT; rewrite E in GT; cbn in GT; clear -GT; lia|].
    subst cnt. rewrite E. unfold qcount. rewrite length_app. cbn [length]. clear. lia. }
  set (DQd := fun ms7 =>
       (exists (t0' t1' t2' a1x a2x a3x a4x a5x a6x a7x t3' t4' t5' t6' : word) (m8 : mem),
          ms7 = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (INST + 728)) a1x a2x a3x a4x a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m8 (seg_rom bsegs)
          /\ mem_inv bsegs m8 /\ stk bsegs m8 lo usp /\ wmono bsegs m6 m8 /\ munch (drainWu usp (as_gq a4)) m6 m8
          /\ rw_cells bsegs m8 0xab2c8 [C4 (wz 0)]
          /\ rw_cells bsegs m8 0xab2d0 [C8 (wz (gcnt + cnt)); C8 (wz gfirst'); C8 (wz (list_last (as_tq a4))); C8 (wz (gq_bytes a4 + tq_bytes a4))]
          /\ rw_cells bsegs m8 (T + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
          /\ (gcnt <> 0 -> rw_cells bsegs m8 (list_last (as_gq a4)) [C8 (wz (list_first (as_tq a4)))])
          /\ gq_bytes a4 + tq_bytes a4 <= 0x10000000)
    \/ (exists (t0' t1' a4x a5x a6x a7x : word) (m7 : mem),
          ms7 = MS (mkR (wz 0x36df4) (wz (usp - 80)) gp tp t0' t1' t2 (wz (INST + 728)) (wz (T + 80)) (wz (INST + 728)) (wz kQuarantineMin) (wz (T + 208)) (wz B) a4x a5x a6x a7x
                        (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x347c4) fc None m7 (seg_rom bsegs)
          /\ mem_inv bsegs m7 /\ stk bsegs m7 lo (usp - 80) /\ wmono bsegs m6 m7 /\ munch (drainWu usp (as_gq a4)) m6 m7
          /\ rw_cells bsegs m7 0xab2c8 [C4 (wz 256)]
          /\ rw_cells bsegs m7 0xab2d0 [C8 (wz (gcnt + cnt)); C8 (wz gfirst'); C8 (wz (list_last (as_tq a4))); C8 (wz (gq_bytes a4 + tq_bytes a4))]
          /\ rw_cells bsegs m7 (T + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
          /\ (gcnt <> 0 -> rw_cells bsegs m7 (list_last (as_gq a4)) [C8 (wz (list_first (as_tq a4)))])
          /\ 0x10000000 < gq_bytes a4 + tq_bytes a4)).
  assert (HNHI : 0 <= cm_n cm / 2^32 < 256) by (clear -N40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (HNLO : 0 <= cm_n cm mod 2^32 < 2^32) by (clear; apply Z.mod_pos_bound; lia).
  assert (HL8b : 8 * ((cm_n cm + 7) / 8) < cm_n cm + 8 /\ cm_n cm <= rounded (cm_n cm)) by (clear -N40 RG1; Z.div_mod_to_equations; lia).
  assert (HCB : 0x603000 <= cb /\ cb + 16 + 8 * BF_free1d.l8 (cm_n cm) <= alloc_ceiling /\ cb mod 16 = 0).
  { unfold BF_free1d.l8. split; [exact CB0|]. split; [clear -CBC HL8b RG3; Z.div_mod_to_equations; lia| clear -P16; Z.div_mod_to_equations; lia]. }
  assert (MUDW : forall mx, munch (BF_free3.drainW (wz (usp - 80)) T gcnt (list_last (as_gq a4))) m6 mx -> munch (drainWu usp (as_gq a4)) m6 mx).
  { intros mx MU. eapply munch_weaken; [| exact MU]. intros z Hz. unfold BF_free3.drainW. unfold drainWu in Hz. rewrite ?Hsp.
    replace (usp - 80 - 48) with (usp - 128) by (clear; lia).
    destruct (snoc_case (as_gq a4)) as [E|(lq & bq & E)].
    - assert (Gz : gcnt = 0) by (subst gcnt; rewrite E; reflexivity). rewrite (proj2 (Z.eqb_eq gcnt 0) Gz). rewrite E in Hz. exact Hz.
    - assert (Gnz : gcnt <> 0) by (subst gcnt; rewrite E; unfold qcount; rewrite length_app; cbn [length]; clear; lia). rewrite (proj2 (Z.eqb_neq gcnt 0) Gnz).
      rewrite E in Hz |- *. destruct lq; exact Hz. }
  eapply (rzA_seg_cfg bsegs (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) P4 DQd).
  { eapply (drain_walk P4 (wz 0x36df4) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) (wz (T + 208)) (wz B) a4' a5 a6 a7 (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000)
              s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc DQd m6 lo T cnt (list_first (as_tq a4)) (list_last (as_tq a4)) (tq_bytes a4) gcnt (list_first (as_gq a4)) (list_last (as_gq a4)) (gq_bytes a4) kQuarantineMin);
      rewrite ?Hsp;
      [ exact SK6 | exact LOC | clear -LO; lia | clear -SPH LO LOC CR; lia | exact MI6 | clear -Tlo Thi Timg; repeat split; lia
      | exact QMTX | exact GQc | exact QMAX | exact QC6
      | clear -CNT1 WT WG GCN GQ4 TQ4; lia | clear -CNT1 WT WG GCN GQ4 TQ4; lia
      | intros NZ; destruct (LASTG NZ) as (lq & bq & E & EL & _ & (_ & _ & L3 & L4 & L5 & _) & _); rewrite EL; clear -L3 L4 L5; repeat split; lia
      | intros NZ; destruct (LASTG NZ) as (lq & bq & E & EL & LB & _); rewrite EL; destruct (rwc_split bsegs m6 (b_addr bq) [C8 (wz 0)] [C8 (wz (b_size bq)); C8 (wz (zlen (b_items bq)))] LB) as [X _]; exact X
      | exact PSTK80 | exact PDAT | exact PT
      | intros NZ y k Y1 Y2; destruct (LASTG NZ) as (lq & bq & E & EL & _ & (L1 & L2 & _) & _); rewrite EL in Y1, Y2; apply PUSR; [clear -Y1 L1; lia| clear -Y2 L2; lia]
      | | ].
    - intros m8 a1x a4x a5x a6x a7x t0' t1' MI8 SK8 WM8 MU8 QM8 GQ8 QC8 GLB8 LEQ. rewrite ?Hsp in SK8. unfold BF_free3.gfirst' in GQ8. fold gfirst' in GQ8.
      replace (ret_pc (wz 0x36df4)) with (wz 0x36df4 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PF8 : rw_cells bsegs m8 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply BF_unwind.rw_cells_agree; [| exact PF6]. cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]. intros z Hz. apply (MUDW m8 MU8). rewrite wa_unsigned by (clear -Hz USPR LO LOC CR; lia).
        unfold drainWu. destruct (snoc_case (as_gq a4)) as [E|(lq & bq & E)]; rewrite E.
        - cbn [outside app]. clear -Hz Thi LO LOC CR. repeat split; try exact I; lia.
        - destruct (GLASTF lq bq E) as (_ & _ & _ & WB & _). pose proof (BLK _ (proj1 WB)) as (_ & _ & _ & L4 & _).
          rewrite list_last_snoc. destruct lq; cbn [outside app]; clear -Hz Thi LO LOC CR L4; repeat split; try exact I; lia. }
      replace (wz (usp - 80)) with (wz (bv_unsigned sp - 80) : word) by reflexivity.
      eapply evtA_cut; [eapply (put_epi P4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m8 lo T B cb (cm_n cm / 2^32) (cm_n cm mod 2^32) (cm_n cm) LOC
                                 ltac:(fold usp; clear -SPH; lia) HCB HNHI HNLO PSTK t0' t1' t2 a1x (wz (T + 208)) (wz B) a4x a5x a6x a7x t3 t4 t5 t6 (INST + 728));
                         rewrite ?Hsp; fold usp; [exact SK8| clear -LO; lia| exact MI8| unfold put_frame; fold usp; rewrite ?Hsp; exact PF8] |].
      intros ms8 HP. unfold put_ret_post in HP. fold usp in HP. destruct HP as (m9 & -> & MU9 & WM9 & MI9 & SK9).
      apply evtA_done. unfold DQd. left. exists t0', t1', t2, a1x, (wz (T + 208) : word), (wz B : word), a4x, a5x, a6x, a7x, t3, t4, t5, t6, m9.
      assert (AG89 : forall z, m9 (wa z) = m8 (wa z)) by (intros z; apply MU9; exact I).
      split; [reflexivity|]. split; [exact MI9|]. split; [exact SK9|]. split; [exact (wmono_trans _ _ _ _ WM8 WM9)|].
      split; [eapply munch_trans; [exact (MUDW m8 MU8)| intros x _; apply MU9; exact I]|].
      split; [eapply BF_unwind.rw_cells_agree; [intros z _; apply AG89| exact QM8]|]. split; [eapply BF_unwind.rw_cells_agree; [intros z _; apply AG89| exact GQ8]|].
      split; [eapply BF_unwind.rw_cells_agree; [intros z _; apply AG89| exact QC8]|].
      split; [intros NZ; eapply BF_unwind.rw_cells_agree; [intros z _; apply AG89| exact (GLB8 NZ)]| exact LEQ].
    - intros m7 a4x a5x a6x a7x t0' t1' MI7 SK7 WM7 MU7 QM7 GQ7 QC7 GLB7 GTQ. rewrite ?Hsp in SK7. unfold BF_free3.gfirst' in GQ7. fold gfirst' in GQ7.
      apply evtA_done. unfold DQd. right. exists t0', t1', a4x, a5x, a6x, a7x, m7.
      split; [reflexivity|]. split; [exact MI7|]. split; [exact SK7|]. split; [exact WM7|]. split; [exact (MUDW m7 MU7)|].
      split; [exact QM7|]. split; [exact GQ7|]. split; [exact QC7|]. split; [exact GLB7| exact GTQ]. }
  { exact KIP4. }
  intros ms7 mo7 HQ7 AG7 KIP7. unfold DQd in HQ7.
  pose proof (magree_frame _ _ AG7) as (Ffds7 & Fvm7 & Flz7 & Ffs7 & Fh7 & Ftid7 & _). destruct KIP7 as [KIA7 _].
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK4 AG7 KIA7) as TOK7. pose proof (AKern_frame _ _ _ _ Fvm7 Flz7 AK4) as AK7.
  assert (RENV4 : renv_ok E0 a4).
  { split; [exact (blocks_sep_of E0 a4 mo6 ENV0 WF4 AK4)|]. split; [clear -Tlo Thi Timg; repeat split; lia|].
    split; [intros r Hr; pose proof (IMGR r Hr) as X; rewrite EI1; clear -X EI2; lia|]. split; [rewrite EI1; clear; lia|]. split; [exact IMGR|].
    split; [exact (img_depsep_asan E0 IC0)|]. split; [exists mo6; exact AK4|]. split; [exact TDN| exact DNP]. }
  destruct HQ7 as [(t0' & t1' & t2' & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3' & t4' & t5' & t6' & m8 & -> & MI8 & SK8 & WM8 & MU8 & QM8 & GQ8 & QC8 & GLB8 & LEQ)
                  |(t0' & t1' & a4x & a5x & a6x & a7x & m7 & -> & MI7 & SK7 & WM7 & MU7 & QM7 & GQ7 & QC7 & GLB7 & GTQ)].
  - (* [comment removed for export] *)
    set (ax5 := xfer_st a4).
    assert (WF5 : AWf E0 [] [] ax5) by exact (AWf_transfer E0 [] [] a4 WF4).
    assert (AK5 : AKern E0 ax5 mo7) by (apply (AKern_ext E0 a4); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK7]).
    assert (SFP45 : same_fp a4 ax5) by (repeat split; reflexivity).
    assert (TOK5 : RTOKc (C - 1) (C' - DSLACK) (sA ax5 s) mo7) by (eapply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0); [exact TOK7| exact SFP45| reflexivity| reflexivity]).
    assert (AG68 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 128 \/ usp - 80 <= z) -> (z + 1 <= 0xab2c8 \/ 0xab2cc <= z) -> (z + 1 <= 0xab2d0 \/ 0xab2f0 <= z)
                  -> (z + 1 <= T + 80 \/ T + 112 <= z) -> (as_gq a4 <> [] -> z + 1 <= list_last (as_gq a4) \/ list_last (as_gq a4) + 8 <= z) -> m8 (wa z) = m6 (wa z)).
    { intros z Z0 Z1 Z2 Z3 Z4 Z5. apply MU8. rewrite wa_unsigned by (clear -Z0; lia). unfold drainWu.
      destruct (snoc_case (as_gq a4)) as [E|(lq & bq & E)]; rewrite E; [cbn [outside app]; clear -Z1 Z2 Z3 Z4; repeat split; try exact I; lia|].
      specialize (Z5 ltac:(rewrite E; destruct lq; discriminate)). rewrite E, list_last_snoc in Z5. rewrite list_last_snoc. destruct lq; cbn [outside app]; clear -Z1 Z2 Z3 Z4 Z5; repeat split; try exact I; lia. }
    assert (REP5 : ARep bsegs E0 (DepotR bsegs E0) ax5 m8).
    { apply (R3 a4 m6 m8 lo ltac:(intros E; unfold tq_bytes in GT; rewrite E in GT; cbn in GT; clear -GT; lia) REP4 WF4 RENV4 WM8).
      - intros z Z0 NF. unfold FPWx, ae_instance in NF. rewrite IC0 in NF. cbn [aic_instance both_ic] in NF. unfold kInsQMutex, kInsQGlobal, kThrQCache in NF.
        apply AG68; [exact Z0| clear -NF LO; lia| clear -NF; lia| clear -NF; lia| clear -NF; lia|].
        intros NE. assert (X : ~ (list_last (as_gq a4) <= z < list_last (as_gq a4) + 8)) by (intros H; apply NF; do 4 right; split; [exact NE| exact H]). clear -X. lia.
      - exact LOC.
      - unfold ae_instance. rewrite IC0. cbn [aic_instance both_ic]. unfold kInsQMutex. exact QM8.
      - unfold ae_instance. rewrite IC0. cbn [aic_instance both_ic]. unfold kInsQGlobal.
        replace (match as_gq a4 with [] => list_first (as_tq a4) | _ :: _ => list_first (as_gq a4) end) with gfirst'; [exact GQ8|].
        subst gfirst' gcnt. destruct (as_gq a4); reflexivity.
      - unfold kThrQCache. exact QC8.
      - intros l0 b0 E. rewrite <- (list_last_snoc l0 b0), <- E. apply GLB8. subst gcnt. rewrite E. unfold qcount. rewrite length_app. cbn [length]. clear. lia. }
    pose proof RUNd as (fd & orcd & evsd & orcd' & RUNd1). pose proof RUNe as (fe & orce & evse & orce' & RUNe1).
    destruct (arun_afree_core_xfer E0 a a2 a4 cb cm aid key fid fd orcd evsd orcd' fe orce evse orce' Hcm ST UB RUNd1 RUNe1
                ltac:(unfold kThreadQuarantineMax; exact GT) ltac:(unfold kQuarantineMax; clear -LEQ; lia)) as (fa & orca & evsa & orca' & RUNA).
    assert (LIVE4 : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> In (blo, bsz) (live_blocks a4)).
    { intros blo bsz LIVEb NEb. destruct (live_block_other E0 [] [] a cb cm blo bsz Hwf Hcm LIVEb ltac:(rewrite UB; exact NEb)) as (cb' & cm' & i & H' & NE' & <- & <- & ST').
      apply (chunk_live_in a4 cb' cm' i); [| exact ST']. rewrite E4c. unfold AsanRepFlipB.s3. cbn [as_chunks upd_chunks]. rewrite lookup_insert_ne by (clear -NE'; congruence). rewrite D14. exact H'. }
    eapply KONT. unfold dealloc_post_state. fold a usp.
    split; [exact SK8|].
    split. { destruct MUW as (W & MU & FA & FL). exists (W ++ drainWu usp (as_gq a4)).
             split; [| split; apply Forall_app; split; [eapply Forall_impl; [| exact FA]; intros iv Hiv; apply (aw_ok_mono E0 a a ax5 a4 lo usp usp iv); [intros sc Hsc; exact Hsc| | | clear; lia| exact Hiv]; intros x0 Hx; exact Hx | | exact FL | ]].
             - eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU8]]; intros z Hz;
                 apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin.
             - unfold drainWu. apply Forall_app. split.
               + repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
                 * left. clear -LO; lia.
                 * right; left. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear; lia].
                 * right; left. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear; lia].
                 * right; right; left. exists (T + kThrQCache, 32). split; [unfold arep_thr_ranges; do 2 right; left; reflexivity| cbn [fst snd]; unfold kThrQCache; clear; lia].
               + destruct (snoc_case (as_gq a4)) as [E|(lq & bq & E)]; rewrite E; [apply Forall_nil|]. destruct (GLASTF lq bq E) as (EL & _ & _ & WB & _). pose proof (BLK _ (proj1 WB)) as (_ & _ & _ & _ & _ & L5 & L6).
                 rewrite list_last_snoc. destruct lq; (apply Forall_cons; [unfold aw_ok; cbn [fst snd]; do 3 right; left; change kResvLen with 137439023104; clear -L5 L6; lia| apply Forall_nil]).
             - unfold drainWu. apply Forall_app. split.
               + repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
                   destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT]|]); [.. | apply Forall_nil].
                 * right; right. clear -Lw1 LOC LO. lia.
                 * right. pose proof (proj1 WF4) as (_ & WEhi & WErs & _). rewrite KHB in WEhi. destruct Lw3 as [[S1 _]|(sc & Hsc & S1 & S2)]; [clear -S1 WEhi WErs Lw0; lia|].
                   pose proof Hwf as (_ & _ & _ & _ & _ & (_ & _ & WS3a & _) & _). destruct (WS3a sc Hsc) as (_ & _ & _ & _ & _ & _ & SR).
                   pose proof (SR _ (proj1 (wf_env_img _ (proj1 Hwf)))) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -X1 S1 S2 Lw0 EI2. lia.
                 * right. pose proof (proj1 WF4) as (_ & WEhi & WErs & _). rewrite KHB in WEhi. destruct Lw3 as [[S1 _]|(sc & Hsc & S1 & S2)]; [clear -S1 WEhi WErs Lw0; lia|].
                   pose proof Hwf as (_ & _ & _ & _ & _ & (_ & _ & WS3a & _) & _). destruct (WS3a sc Hsc) as (_ & _ & _ & _ & _ & _ & SR).
                   pose proof (SR _ (proj1 (wf_env_img _ (proj1 Hwf)))) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -X1 S1 S2 Lw0 EI2. lia.
                 * right. clear -BT. lia.
               + destruct (snoc_case (as_gq a4)) as [E|(lq & bq & E)]; rewrite E; [apply Forall_nil|]. destruct (GLASTF lq bq E) as (EL & _ & _ & WB & _).
                 assert (INbq : In bq (as_tq a4 ++ as_gq a4)) by (rewrite E; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
                 rewrite list_last_snoc. destruct lq; (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
                   pose proof (batch_vs_live E0 [] a4 bq blo bsz WF4 INbq (LIVE4 blo bsz LIVEb NEb)) as BV; right; clear -BV; lia| apply Forall_nil]). }
    split; [exists fa, orca, evsa, orca'; exact RUNA|].
    split. { (* [comment removed for export] *)
      split; [exact REP5|]. split; [exact WF5|]. split; [exact AK5|].
      split; [apply (res_ok_frame a4); [cbn; intros sc H; exact H| cbn; apply incl_refl| exact RES4]|].
      split. { split; [unfold tq_bytes; cbn; unfold kThreadQuarantineMax; clear; lia|]. unfold gq_bytes, kQuarantineMax. subst ax5. unfold xfer_st. cbn [as_gq upd_tq upd_gq]. rewrite qbytes_app.
               unfold gq_bytes, tq_bytes in LEQ. clear -LEQ. lia. }
      split; [revert DI4; clear; unfold depot_inv, depot_n_ids, dphi; exact (fun H => H)|].
      split. { unfold AsanBudget2.binv. exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (afree_core_cnt E0 a key (cb + 16) Hbinv Hqb) eq_refl RUNA). }
      split; [exact MI8|].
      split. { apply (rt_misc5_agree E0 FSB0 PL0 m6 m8 RT6). intros z Hz.
               pose proof CR0 as (CIn & _ & _ & CRS & _). pose proof DR0 as (DIn & _ & _ & DRS & _). change kResvLen with 137439023104 in CRS, DRS.
               pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
               pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
               destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
               - apply AG68; [clear -ZI; lia| clear -ZI LO LOC CR; lia| | | clear -ZI Timg Tlo; lia|].
                 + destruct (Z_lt_le_dec z 0xab2c8) as [X|X]; [left; clear -X; lia|]. destruct (Z_lt_le_dec z 0xab2cc) as [Y|Y]; [| right; exact Y].
                   exfalso. apply NM. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear -X Y; lia].
                 + destruct (Z_lt_le_dec z 0xab2d0) as [X|X]; [left; clear -X; lia|]. destruct (Z_lt_le_dec z 0xab2f0) as [Y|Y]; [| right; exact Y].
                   exfalso. apply NM. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; clear -X Y; lia].
                 + intros NE. destruct (LASTG ltac:(subst gcnt; destruct (as_gq a4); [exfalso; exact (NE eq_refl)| unfold qcount; cbn [length]; clear; lia])) as (lq & bq & E & EL & _ & (_ & _ & L3 & _) & _).
                   rewrite EL. clear -ZI L3 KHB. lia.
               - unfold rt_high2 in RH. apply AG68; [clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia| clear -RH LO LOC Thi CQ2 CC2 DQ2 DD2; lia| | | clear -RH CT DT; lia|].
                 + clear -RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
                 + clear -RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
                 + intros NE. destruct (LASTG ltac:(subst gcnt; destruct (as_gq a4); [exfalso; exact (NE eq_refl)| unfold qcount; cbn [length]; clear; lia])) as (lq & bq & E & EL & _ & (_ & _ & _ & _ & L5 & L6 & L7) & _).
                   rewrite EL. unfold kIArenaLen in CIA. pose proof (wf_env_iarena _ WE4) as (_ & _ & _ & WI4 & _). unfold kIArenaLen in WI4.
                   clear -RH L5 L6 L7 CRS DRS CC1 CC2 DD1 DD2 CIA WI4. lia. }
      split; [revert SS4; clear; unfold sstats_ok, sec_bytes; exact (fun H => H)|].
      intros cbx cmx Hx. apply (CS4 cbx cmx). exact Hx. }
    split; [unfold FSLACK; unfold DSLACK in TOK5; exact TOK5|].
    split; [rewrite Ffs7; exact Ffs6|]. split; [rewrite Ffds7; exact Ffds6|]. split; [rewrite Ftid7; exact Ftid6|].
    split. { unfold facct. subst ax5. unfold xfer_st. cbn [as_nprim_ever as_residue as_ndepot_ins upd_tq upd_gq]. rewrite E4np, E4res, E4nd, ND2. clear. repeat split; lia. }
    unfold live_blocks, chunk_list. subst ax5. unfold xfer_st. cbn [as_chunks upd_tq upd_gq]. rewrite E4c. unfold AsanRepFlipB.s3. cbn [as_chunks upd_chunks]. rewrite D14. rewrite <- UB.
    pose proof (live_blocks_flip a cb cm aid fid Hcm ST) as PM. unfold live_blocks, chunk_list in PM. cbn [as_chunks upd_chunks] in PM. exact PM.
  - (* [comment removed for export] *)
    unfold QR_post in QRPOST.
    eapply (QRPOST t0 t1 t2 a4' a4' a4' a4' a4' a5 a6 a7 t3 t4 t5 t6 m6 mo6 a2 a4 cm aid fid);
      [ exact Hcm | exact ST | exact UB | exact RUNd | exact FID | exact DS2 | exact ND2 | exact RUNe | exact FLD | exact WF4 | exact REP4 | exact AK4 | exact TOK4 | exact KIA4
      | exact RES4 | exact GQ4 | unfold kThreadQuarantineMax; exact TQ4 | exact DI4 | exact SS4 | exact CS4
      | exact Ffs6 | exact Ffds6 | exact Ftid6
      | exact MI6 | exact SK6 | exact WM6 | exact RT6 | exact MUW | exact PF6 | exact QC6 | unfold kThreadQuarantineMax; exact GT
      | unfold kQuarantineMax; clear -GTQ; lia
      | exact MI7 | exact SK7 | exact WM7 | exact MU7 | exact AG7 | exact KIA7 | exact QM7
      | subst gcnt cnt gfirst'; replace (match as_gq a4 with [] => list_first (as_tq a4) | _ :: _ => list_first (as_gq a4) end) with (if qcount (as_gq a4) =? 0 then list_first (as_tq a4) else list_first (as_gq a4)); [exact GQ7| destruct (as_gq a4); reflexivity]
      | exact QC7
      | intros l0 b0 E; rewrite <- (list_last_snoc l0 b0), <- E; apply GLB7; subst gcnt; rewrite E; unfold qcount; rewrite length_app; cbn [length]; clear; lia ].
Qed.

End DeallocT3.
End RC__1.
