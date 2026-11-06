(* CARRIED from commit af0289e23fe22dee392685c3fca02473a52c792c,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstEnqG.v, sha256 443f3508e1ddbfe0170b27b2b2e9a71429ed1559ef97f4a822d4b190cae91865 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the
   module paths only: OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib M -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable M, except lib.A for: DMspec DMiface DeallocG ImgBaseAG ImgBaseDG DGif0 DIfaceR YGcfInstErrno YGcfInstEnq EnqGbase AFl1. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (lane F1 of the generic cf instance layer; integrator ReallocPrimary).
   The cf instance's MODEL fields of lane B2's frame-generic Enqueue interface (EnqGbase.v at commit
   d371f1553a2, taken by path, byte-identical: EnqIfaceRoom :153, EnqIfaceHit :193), at
     segs := im_segs, A_ENQ := dg_enqueue, ARX := any relation giving ARcf at Hp (YGcfInstBase.ARX_cf B IOK Hp),
     AOX := aowned B, EPRE := YGcfInstEnq.enq_pre_cf, RMAXD := kFreeArrayOffset, and B2's own STRICT block-size
     parameter := [ENQ_NMAX_STRICT] (= kQuarantineMax + 1).  The layer's NMAXD is the INCLUSIVE quarantine-entry bound
     `ck_n k <= kQuarantineMax` (CF-LAYER-LANES.md, 'NMAXD, ONE MEANING'), which enq_pre_cf carries;
     [nmax_strict_of_guard] turns it into B2's strict form.
   rule 24: no function proved (kind: interface-instance discharge, model fields only).
   - [enq_nmax_cf]: ir_nmax / ih_nmax (enq_pre_cf's guard conjunct, and 0 <= ck_req from chunk_ok_cf);
   - [rmaxd_ok_cf]: ih_rmaxd_ok at RMAXD := kFreeArrayOffset;
   - [enq_rmax_cf]: ih_rmax (from enq_pre_cf's batch_room_cf, YG00cf.v:361-362);
   - [Shit_cf], [enq_inited_cf], [enq_hit_eq_cf], [ih_shape_cf]: the hit arm's end state (YFf2.S''s text) and its
     step equation (YFg5.enqueue_hit_eq's script), the cache's initialization from Wf_cf (wrc_cache);
   - Main's instance checks: [enq_nmax_strict_ok] (ENQ_NMAX_STRICT <= 2 ^ 30, B2's window) and the
     event-free replacement of YG0m.batches_len_fuel (which reads wf_regime, an event ceiling that Wf_cf drops):
     [qthread_len_cf] (|qc_list thread| <= 2 ^ 16) and [batches_len_cf] (|all_batches| <= 2 ^ 16 + 2 ^ 17), from
     qloose's byte bounds, wq_bytes_t and every batch's kBatchBytes header (b_bytes, YG00.v:147).
   The walk fields (ir_walk / ih_walk, ir_frame / ih_frame) are the unit's relocated walk at its image; the transport
   fields (ir_post / ih_post, ir_owned / ih_owned, ir_safe / ih_safe) are the cf AR transport (YGcfEnqTr*.v, lane F1,
   next).  No image constant; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h YG0l YG0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG ImgBaseDG DGif0 DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG08cf YG03cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstErrno YGcfInstEnq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require EnqGbase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YFfp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFl1.
(* stdpp, through the LPS modules, shadows several list names; In / NoDup here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {IM : AImg} {AG : AGImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Main's instance checks that read no relation.                                                                 *)

(* RMAXD's window at the cf instance (EnqGbase.v:201 ih_rmaxd_ok at RMAXD := kFreeArrayOffset). *)
Lemma rmaxd_ok_cf : 2 ^ 31 <= kFreeArrayOffset <= kFreeArrayOffset.
Proof. unfold kFreeArrayOffset. lia. Qed.

(* B2's strict block-size parameter at the cf instance, and its link to the layer's inclusive guard. *)
Definition ENQ_NMAX_STRICT : Z := kQuarantineMax + 1.
Lemma nmax_strict_of_guard : forall k, ck_n k <= kQuarantineMax -> ck_n k < ENQ_NMAX_STRICT.
Proof. intros k H. unfold ENQ_NMAX_STRICT. lia. Qed.
Lemma enq_nmax_strict_ok : ENQ_NMAX_STRICT <= 2 ^ 30.
Proof. unfold ENQ_NMAX_STRICT, kQuarantineMax. lia. Qed.

(* Every batch's bytes are its kBatchBytes header plus its items' sizes (YG00.v:147). *)
Lemma items_sum_nonneg_cf : forall l : list chunk, Forall (fun k => 0 <= ck_n k) l ->
0 <= fold_right (fun k acc => ck_n k + acc) 0 l.
Proof. induction l as [|k t IH]; intros H; cbn; [lia|]. inversion H; subst. pose proof (IH H3). lia. Qed.

Lemma sum_bytes_ge_cf : forall l : list batch, Forall (fun b => Forall (fun k => 0 <= ck_n k) (b_items b)) l ->
kBatchBytes * Z.of_nat (length l) <= sum_bytes l.
Proof.
induction l as [|b t IH]; intros H.
- unfold sum_bytes. cbn. lia.
- inversion H; subst. pose proof (IH H3) as IHt. pose proof (items_sum_nonneg_cf _ H2) as P.
  assert (Bb : kBatchBytes <= b_bytes b) by (unfold b_bytes; lia).
  unfold sum_bytes in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
  unfold kBatchBytes in IHt, Bb |- *. lia.
Qed.

(* Every queued chunk has a non-negative size: it is a chunk of the state (wq_items) and chunk_ok_cf bounds it. *)
Lemma queued_n_nonneg_cf : forall U X, Wf_cf U X ->
Forall (fun b => Forall (fun k => 0 <= ck_n k) (b_items b)) (all_batches X).
Proof.
intros U X W. apply Forall_forall. intros b Hb. apply Forall_forall. intros k Hk.
pose proof (wfc_quarantine _ _ _ _ _ W) as Q.
assert (Hq : In k (q_items X)) by (unfold q_items; apply in_flat_map; exists b; split; assumption).
destruct (proj1 (Forall_forall _ _) (wq_items _ Q) k Hq) as [Hc _].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hc) as [Hr _].
unfold ck_n, req_size. destruct (ck_req k =? 0); lia.
Qed.

(* The event-free replacement of YG0m.batches_len_fuel's thread part: from qloose's byte bound alone. *)
Lemma qthread_len_cf : forall U X, Wf_cf U X -> qloose X -> Z.of_nat (length (qc_list (st_qthread X))) <= 2 ^ 16.
Proof.
intros U X W (Q1 & _ & _).
pose proof (wq_bytes_t _ (wfc_quarantine _ _ _ _ _ W)) as E.
assert (F : Forall (fun b => Forall (fun k => 0 <= ck_n k) (b_items b)) (qc_list (st_qthread X))).
{ apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) (queued_n_nonneg_cf U X W)).
  unfold all_batches. apply in_or_app. left. exact Hb. }
pose proof (sum_bytes_ge_cf _ F) as G. rewrite <- E in G. unfold kBatchBytes in G. lia.
Qed.

(* ... and over every batch, thread and global (YG0m.batches_len_qloose's bound, at Wf_cf). *)
Lemma batches_len_cf : forall U X, Wf_cf U X -> qloose X -> Z.of_nat (length (all_batches X)) <= 2 ^ 16 + 2 ^ 17.
Proof.
intros U X W QL. pose proof (qthread_len_cf U X W QL) as T. destruct QL as (_ & Q2 & _).
pose proof (wq_bytes_g _ (wfc_quarantine _ _ _ _ _ W)) as E.
assert (F : Forall (fun b => Forall (fun k => 0 <= ck_n k) (b_items b)) (qc_list (st_qglobal X))).
{ apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) (queued_n_nonneg_cf U X W)).
  unfold all_batches. apply in_or_app. right. exact Hb. }
pose proof (sum_bytes_ge_cf _ F) as G. rewrite <- E in G. unfold kBatchBytes in G.
unfold all_batches. rewrite length_app, Nat2Z.inj_add. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The hit arm's end state and step equation (model only).                                                       *)

(* YFf2.S' (YFf2.v:59-64): the class-24 cache's last chunk becomes the new batch holding [k]. *)
Definition Shit_cf (X : astate) (k : chunk) (l : list Z) : astate :=
set_qthread (qc_push (st_qthread X) k (Some (region_off kBatchClass + last l 0)))
  (upd_pc kBatchClass (mkPC (pc_max (cache X kBatchClass)) (YG00.removelast l)) X).

(* YFg5.enqueue_hit_eq (YFg5.v:411-418), its script. *)
Lemma enq_hit_eq_cf : forall X k l, st_cache_inited X = true -> need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] -> enqueue k X = IRet (tt, Shit_cf X k l).
Proof.
intros X k l CI HNB Hl Hlne.
unfold enqueue, cache_alloc, init_cache_if_needed, refill_if_empty, get_pc, set_pc, get, put, modify, ret, bind. cbn [ibind].
rewrite HNB. cbn [ibind]. rewrite CI. cbn [ibind].
change (znth pclass0 kBatchClass (st_cache X)) with (cache X kBatchClass). rewrite Hl.
destruct l as [|x t]; [congruence|]. cbn [ibind]. fold (cache X kBatchClass). rewrite Hl. cbn [ibind]. reflexivity.
Qed.

(* A non-empty class-24 cache means the caches are initialized (Wf_cf's wrc_cache). *)
Lemma enq_inited_cf : forall U X l, Wf_cf U X -> pc_chunks (cache X kBatchClass) = l -> l <> [] ->
st_cache_inited X = true.
Proof.
intros U X l W Hl Hlne.
pose proof (wfc_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as C. unfold wf_class_cf in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as Hc.
destruct (st_cache_inited X) eqn:E; [reflexivity|].
exfalso. apply Hlne. rewrite <- Hl, Hc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Wf_cf at an Enqueue arm's end state, from Wf_cf at its pre-state and the two lower bounds of the tick          *)
(*    (YGcfInstEnq.enq_pre_tick_cf): the bounds lend one map credit and one batch credit (enq_reslack_cf), the       *)
(*    model's step spends them (YG03cf.enqueue_okx_cf), and the class totals are kept (Compl0).  The tick bounds are   *)
(*    consumed only as credits: here to re-establish wfc_prim_ev / wfc_batches_ev at the post, and in section 4 as    *)
(*    WfR_cf U 1 0 1 for the miss arm's refill (refill_batch_apostg_cf); never as room.                              *)
Lemma enq_reslack_cf : forall U X, Wf_cf U X ->
prim_user_mapped X + kUserMapSize <= kUserMapSize * st_nev X ->
Z.of_nat (length (all_batches X)) + 1 <= st_nev X -> WfR_cf U 1 0 1 X.
Proof.
intros U X W H1 H2. destruct W.
constructor; try assumption; unfold kUserMapSize in *; lia.
Qed.

Lemma enq_wf_post_cf : forall U X k S', Wf_cf U X ->
prim_user_mapped X + kUserMapSize <= kUserMapSize * st_nev X ->
Z.of_nat (length (all_batches X)) + 1 <= st_nev X ->
In k (st_chunks X) -> ck_state k = CQuarantined -> ck_n k <= kQuarantineMax -> ~ In (ck_beg k) (map ck_beg (q_items X)) ->
batch_room_cf X -> enqueue k X = IRet (tt, S') -> Wf_cf U S'.
Proof.
intros U X k S' W H1 H2 Hk Hst HQM Hnq BR EQ.
pose proof (enqueue_okx_cf U 1 0 1 X k true (enq_reslack_cf U X W H1 H2) ltac:(lia) ltac:(lia) Hk Hst HQM Hnq BR) as P.
rewrite EQ in P. cbn [atok] in P. destruct P as ((W' & _) & CD). cbn [snd] in W', CD.
change (1 - 1) with 0 in W'.
apply WfP_of_WfR_cf; [exact W'|].
intros c Hc. rewrite (CD c Hc). exact (wfc_compl0 _ _ _ _ _ W c Hc).
Qed.

(* Wf_cf after the HIT step at a state whose class-24 cache is not empty (the miss arm's refilled state): the step
   pops the cache and pushes one batch, it maps nothing, so it spends only the batch credit and needs no room premise
   (YG03cf.pop_ok_cf, WfR_qpush_cf; the class totals are kept, as in YG03cf.enqueue_okx_cf's hit branch). *)
Lemma hit_wf_post_cf : forall U X k l, Wf_cf U X ->
Z.of_nat (length (all_batches X)) + 1 <= st_nev X ->
In k (st_chunks X) -> ck_state k = CQuarantined -> ck_n k <= kQuarantineMax -> ~ In (ck_beg k) (map ck_beg (q_items X)) ->
st_cache_inited X = true -> need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] -> Wf_cf U (Shit_cf X k l).
Proof.
intros U X k l W H2 Hk Hst HQM Hnq Hci HNB Hl Hlne.
assert (W0 : WfR_cf U 0 0 1 X) by (destruct W; constructor; try assumption; lia).
assert (HLc : (Z.to_nat kBatchClass < length (st_cache X))%nat) by (eapply WfR_len_cache_cf; [exact W0 | unfold kBatchClass; lia]).
destruct (pop_ok_cf U 0 0 1 X kBatchClass l W0 ltac:(unfold kBatchClass; lia) Hci Hl Hlne) as (W3 & P1 & P2 & P3).
pose proof (WfR_qpush_cf U 0 0 1 _ k (Some (region_off kBatchClass + last l 0)) W3 ltac:(lia) Hk Hst HQM Hnq
  (ex_intro _ (last l 0) (conj eq_refl (conj P1 (conj P2 P3)))) Hci (fun _ => HNB)) as W4.
change (1 - 1) with 0 in W4.
unfold Shit_cf. apply WfP_of_WfR_cf; [exact W4|].
intros c Hc. etransitivity; [|exact (wfc_compl0 _ _ _ _ _ W c Hc)]. apply cdef_ext; [reflexivity|].
set (p := mkPC (pc_max (cache X kBatchClass)) (YG00.removelast l)).
assert (EQc : cache (set_qthread (qc_push (st_qthread X) k (Some (region_off kBatchClass + last l 0))) (upd_pc kBatchClass p X)) c =
  cache (upd_pc kBatchClass p X) c) by reflexivity.
assert (EQr : reg (set_qthread (qc_push (st_qthread X) k (Some (region_off kBatchClass + last l 0))) (upd_pc kBatchClass p X)) c = reg X c)
  by reflexivity.
assert (EQo : chunk_offs (set_qthread (qc_push (st_qthread X) k (Some (region_off kBatchClass + last l 0))) (upd_pc kBatchClass p X)) c =
  chunk_offs X c) by reflexivity.
unfold class_elems. rewrite !length_app, EQc, EQr, EQo.
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qthread].
destruct (Z.eqb_spec c kBatchClass) as [->|Hne].
- rewrite cache_upd_pc by (first [unfold kBatchClass; lia | exact HLc]). subst p. cbn [pc_chunks].
  try rewrite Z.eqb_refl. rewrite removelast_length by exact Hlne. rewrite Hl.
  cbn [qc_push qc_list]. rewrite !length_map, !length_app. cbn [length].
  destruct l as [|o t]; [congruence|]. cbn [length]. change (st_qglobal (upd_pc kBatchClass _ X)) with (st_qglobal X). lia.
- unfold upd_pc. rewrite cache_upd_other by (unfold kBatchClass in *; lia). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The miss arm's refill on its granted paths (EnqGmiss's im_apostg at the cf instance).  cgif proves it at its   *)
(*    event-bounded WfP (YFg6.refill_tree_apostg, which reads preg); the cf proof reads the cache-alloc model fact   *)
(*    YG03cf.cache_alloc_okx_cf at WfR_cf U 1 0 1 X (the tick's two credits) and batch_room_cf: a granted path of     *)
(*    the refill tree extends, by the pure pop, to a granted path of cache_alloc, whose post forces the pop to fire.  *)
(*    Stated over cgif's YFl1.refill_tree, which EnqGmiss's im_apostg names; at kBatchClass it is the cf model's tree  *)
(*    term for term (YGcfInstRefill.refill_tree_cf_batch, by reflexivity).                                            *)
Lemma apath_ibind_comp {A B0 : Type} : forall (t : itree astate A) (k : A -> itree astate B0) tr1 a tr2 b,
apath t tr1 a -> apath (k a) tr2 b -> apath (ibind t k) (tr1 ++ tr2) b.
Proof.
induction t as [a0 | q snap c IH | pc | f]; intros k tr1 a tr2 b H1 H2.
- destruct tr1 as [|x tr1]; cbn [apath] in H1; [subst a0; exact H2 | destruct H1].
- destruct tr1 as [|[q' z] tr1]; cbn [apath] in H1; [destruct H1|]. destruct H1 as (-> & Hz & Hp).
  cbn [ibind app apath]. split; [reflexivity|]. split; [exact Hz|]. exact (IH z k tr1 a tr2 b Hp H2).
- destruct tr1; cbn [apath] in H1; destruct H1.
- destruct tr1; cbn [apath] in H1; destruct H1.
Qed.

Lemma apath_ibind_inv {A B0 : Type} : forall (t : itree astate A) (k : A -> itree astate B0) tr b,
apath (ibind t k) tr b -> exists tr1 tr2 a, tr = tr1 ++ tr2 /\ apath t tr1 a /\ apath (k a) tr2 b.
Proof.
induction t as [a0 | q snap c IH | pc | f]; intros k tr b H.
- exists [], tr, a0. cbn [ibind] in H. split; [reflexivity|]. split; [reflexivity | exact H].
- destruct tr as [|[q' z] tr]; cbn [ibind apath] in H; [destruct H|]. destruct H as (-> & Hz & Hp).
  destruct (IH z k tr b Hp) as (tr1 & tr2 & a & -> & P1 & P2).
  exists ((q, z) :: tr1), tr2, a. split; [reflexivity|]. split; [cbn [apath]; split; [reflexivity | split; [exact Hz | exact P1]] | exact P2].
- destruct tr; cbn [ibind apath] in H; destruct H.
- destruct tr; cbn [ibind apath] in H; destruct H.
Qed.

Lemma apath_bind_comp {A B0 : Type} : forall (m : M A) (k : A -> M B0) s tr1 a s1 tr2 b,
apath (m s) tr1 (a, s1) -> apath (k a s1) tr2 b -> apath (bind m k s) (tr1 ++ tr2) b.
Proof. intros m k s tr1 a s1 tr2 b H1 H2. unfold bind. exact (apath_ibind_comp _ _ tr1 (a, s1) tr2 b H1 H2). Qed.

Lemma apath_bind_inv {A B0 : Type} : forall (m : M A) (k : A -> M B0) s tr b,
apath (bind m k s) tr b -> exists tr1 tr2 a s1, tr = tr1 ++ tr2 /\ apath (m s) tr1 (a, s1) /\ apath (k a s1) tr2 b.
Proof.
intros m k s tr b H. unfold bind in H. destruct (apath_ibind_inv _ _ _ _ H) as (tr1 & tr2 & [a s1] & E & P1 & P2).
exists tr1, tr2, a, s1. split; [exact E|]. split; [exact P1 | exact P2].
Qed.

Lemma refill_batch_apostg_cf : forall U X, WfR_cf U 1 0 1 X -> batch_room_cf X ->
forall tr r, apath (AFl1.refill_tree kBatchClass X) tr r -> gflag tr = true ->
regs_only X (snd r) /\ st_cache_inited (snd r) = true /\ pc_chunks (cache (snd r) kBatchClass) <> [].
Proof.
intros U X W BR tr [u2 s2] Hp Hg. cbn [snd].
unfold AFl1.refill_tree in Hp. destruct (apath_bind_inv _ _ _ _ _ Hp) as (tr1 & tr2 & u1 & s1 & -> & P1 & P2).
assert (ROOM : rg_mapped_user (reg X kBatchClass) + kUserMapSize <= kFreeArrayOffset) by (unfold batch_room_cf in BR; exact BR).
pose proof (cache_alloc_okx_cf U 1 0 1 X kBatchClass true W ltac:(unfold kBatchClass; lia) ltac:(lia) ROOM) as OK.
assert (LF : last_flag true ((tr1 ++ tr2) ++ []) = true) by (rewrite app_nil_r; exact (last_flag_true _ Hg)).
destruct (pc_chunks (cache s2 kBatchClass)) as [|o l0] eqn:E.
- assert (PC : apath (cache_alloc kBatchClass X) (tr1 ++ (tr2 ++ [])) (None, s2)).
  { unfold cache_alloc. apply (apath_bind_comp _ _ X tr1 u1 s1); [exact P1|].
    apply (apath_bind_comp _ _ s1 tr2 u2 s2); [exact P2|].
    unfold get_pc, get, ret, bind. cbn [ibind apath]. change (znth pclass0 kBatchClass (st_cache s2)) with (cache s2 kBatchClass).
    rewrite E. reflexivity. }
  rewrite app_assoc in PC. pose proof (atok_apath_flag _ true _ _ _ OK PC) as POST. rewrite LF in POST.
  destruct POST as ((_ & _ & _ & NS) & _). discriminate NS.
- set (s3 := set_cache (zupd kBatchClass (mkPC (pc_max (cache s2 kBatchClass)) (YG00.removelast (o :: l0))) (st_cache s2)) s2).
  assert (PC : apath (cache_alloc kBatchClass X) (tr1 ++ (tr2 ++ [])) (Some (region_off kBatchClass + last (o :: l0) 0), s3)).
  { unfold cache_alloc. apply (apath_bind_comp _ _ X tr1 u1 s1); [exact P1|].
    apply (apath_bind_comp _ _ s1 tr2 u2 s2); [exact P2|].
    unfold get_pc, set_pc, modify, get, put, ret, bind. cbn [ibind apath]. change (znth pclass0 kBatchClass (st_cache s2)) with (cache s2 kBatchClass).
    rewrite E. reflexivity. }
  rewrite app_assoc in PC. pose proof (atok_apath_flag _ true _ _ _ OK PC) as POST. rewrite LF in POST.
  destruct POST as ((_ & RO & CI & _) & _).
  split; [|split; [exact CI | discriminate]].
  unfold regs_only in *. subst s3. cbn in RO |- *. exact RO.
Qed.

Section b.
Variable B : asyms.
(* The caller's ghost set and the walk relation: any relation that gives ARcf at Hp (YGcfInstBase.ARX_cf B IOK Hp,
   with HAR := YGcfInstBase.ARX_cf_ARcf B IOK Hp). *)
Variable Hp : list Z.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Hypothesis HAR : forall inst ly S W mem md, ARX inst ly S W mem md -> ARcf im_segs B ly S Hp W mem md.

Local Notation EPRE := (enq_pre_cf B ARX).

Lemma enq_pre_wf_cf : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k -> Wf_cf (as_universe B) X.
Proof.
intros inst ly X W regs mem md k PRE. destruct PRE as (HA & _).
destruct (HAR inst ly X W mem md HA) as (M & _). exact (amc_wf _ _ _ _ _ M).
Qed.

(* ir_nmax / ih_nmax at B2's strict parameter ENQ_NMAX_STRICT, from enq_pre_cf's guard conjunct. *)
Lemma enq_nmax_cf : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k -> 1 <= ck_n k < ENQ_NMAX_STRICT.
Proof.
intros inst ly X W regs mem md k PRE. pose proof (enq_pre_wf_cf inst ly X W regs mem md k PRE) as W0.
destruct PRE as (_ & _ & _ & Hk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HN & _).
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W0) k Hk) as [Hr _].
split; [|exact (nmax_strict_of_guard k HN)]. unfold ck_n, req_size. destruct (Z.eqb_spec (ck_req k) 0); lia.
Qed.

(* ih_rmax at RMAXD := kFreeArrayOffset, from enq_pre_cf's batch_room_cf. *)
Lemma enq_rmax_cf : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k ->
rg_mapped_user (reg X kBatchClass) <= kFreeArrayOffset.
Proof.
intros inst ly X W regs mem md k PRE. destruct PRE as (_ & BR & _). unfold batch_room_cf in BR.
unfold kUserMapSize in BR. lia.
Qed.

(* ih_shape at Shit := Shit_cf. *)
Lemma ih_shape_cf : forall inst ly X W regs mem md k l, EPRE inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true -> pc_chunks (cache X kBatchClass) = l -> l <> [] ->
enqueue k X = IRet (tt, Shit_cf X k l).
Proof.
intros inst ly X W regs mem md k l PRE HNB Hl Hlne.
pose proof (enq_pre_wf_cf inst ly X W regs mem md k PRE) as W0.
exact (enq_hit_eq_cf X k l (enq_inited_cf _ X l W0 Hl Hlne) HNB Hl Hlne).
Qed.

(* Main's check (3) at the Enqueue call state: the batch counts the walk's q_facts read are bounded by bytes. *)
Lemma enq_batches_len_cf : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k ->
Z.of_nat (length (qc_list (st_qthread X))) <= 2 ^ 16 /\ Z.of_nat (length (all_batches X)) <= 2 ^ 16 + 2 ^ 17.
Proof.
intros inst ly X W regs mem md k PRE. pose proof (enq_pre_wf_cf inst ly X W regs mem md k PRE) as W0.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QL & _).
exact (conj (qthread_len_cf _ X W0 QL) (batches_len_cf _ X W0 QL)).
Qed.

(* Wf_cf at the room arm's end state (EnqGbase.Sroom, YFfp.enqueue_room_eq). *)
Lemma enq_room_wf_cf : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = false -> Wf_cf (as_universe B) (EnqGbase.Sroom X k).
Proof.
intros inst ly X W regs mem md k PRE HNB.
pose proof (enq_pre_wf_cf inst ly X W regs mem md k PRE) as W0.
destruct (enq_pre_tick_cf B ARX inst ly X W regs mem md k PRE) as [E1 E2].
destruct PRE as (_ & BR & _ & Hk & Hst & Hnq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQM & _).
exact (enq_wf_post_cf _ X k _ W0 E2 E1 Hk Hst HQM Hnq BR (YFfp.enqueue_room_eq k X HNB)).
Qed.

(* Wf_cf at the hit arm's end state (Shit_cf, enq_hit_eq_cf). *)
Lemma enq_hit_wf_cf : forall inst ly X W regs mem md k l, EPRE inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true -> pc_chunks (cache X kBatchClass) = l -> l <> [] ->
Wf_cf (as_universe B) (Shit_cf X k l).
Proof.
intros inst ly X W regs mem md k l PRE HNB Hl Hlne.
pose proof (enq_pre_wf_cf inst ly X W regs mem md k PRE) as W0.
pose proof (ih_shape_cf inst ly X W regs mem md k l PRE HNB Hl Hlne) as EQ.
destruct (enq_pre_tick_cf B ARX inst ly X W regs mem md k PRE) as [E1 E2].
destruct PRE as (_ & BR & _ & Hk & Hst & Hnq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQM & _).
exact (enq_wf_post_cf _ X k _ W0 E2 E1 Hk Hst HQM Hnq BR EQ).
Qed.
End b.
End a.
