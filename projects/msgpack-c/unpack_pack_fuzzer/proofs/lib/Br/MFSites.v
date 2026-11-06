(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KOwn PgArith.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_Contracts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue NodeSound TreeBridge TreeBridgeN KRel MPath Room Grant MMeas MF NoRefuse MFMust.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition T2_A_stmt (PHI : mstate -> Prop) : Prop :=
  forall L L1 cs1 c, MI_Contracts.SIMREL (ps_m s0) L -> cpath L (cmalloc (ps_m s0) BUF0) L1 (cs1, Some c) -> PHI cs1.
Definition T2_Bm_stmt (PHI PHIB : mstate -> Prop) : Prop :=
  forall cs L L' cs' c n, PHI cs -> MI_Contracts.SIMREL cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  cpath L (cmalloc cs n) L' (cs', Some c) -> PHIB cs'.
Definition T2_Bf_stmt (PHI PHIB : mstate -> Prop) : Prop :=
  forall cs L L' cs' c, PHIB cs -> MI_Contracts.SIMREL cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' -> PHI cs'.

Definition one_mmap (L : mled) (t : Malloc.M (mstate * option cptr)) (lenlo lenhi : Z) : Prop :=
  exists len kont, t = SVis (EMmap 0 len PROT_RW MAPF) kont /\ lenlo <= len <= lenhi
    /\ (forall z, is_errno_form z = true -> exists cs1, kont z = SRet (cs1, None))
    /\ (forall a, is_err a = false -> answer_ok L (EMmap 0 len PROT_RW MAPF) a = true -> exists cs2 c, kont a = SRet (cs2, Some c)).
Definition T2_C_stmt (PHI : mstate -> Prop) : Prop :=
  forall cs L n, PHI cs -> MI_Contracts.SIMREL cs L -> 0 < n < MMAP_THRESHOLD -> one_mmap L (cmalloc cs n) 1 (2 ^ 21).
Definition T2_Cbig_stmt (PHI : mstate -> Prop) : Prop :=
  forall cs L n, PHI cs -> MI_Contracts.SIMREL cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  one_mmap L (cmalloc cs n) (n + IB + UNIT) (n + IB + UNIT).

Section Sites.
Variables PHI PHIB : mstate -> Prop.
Hypothesis T2_A : T2_A_stmt PHI.
Hypothesis T2_Bm_sim : T2_Bm_stmt PHI PHIB.
Hypothesis T2_Bf_sim : T2_Bf_stmt PHI PHIB.
Hypothesis T2_C_sim : T2_C_stmt PHI.
Hypothesis T2_Cbig_sim : T2_Cbig_stmt PHI.

Lemma cpath_some_not_overflow : forall cs n L L' cs' c,
  cpath L (cmalloc cs n) L' (cs', Some c) -> size_overflows n = false.
Proof.
  intros cs n L L' cs' c H. destruct (size_overflows n) eqn:E; [| reflexivity].
  rewrite (cmalloc_overflow _ _ E) in H. inversion H.
Qed.

Lemma bufsz_ge : forall k, MMAP_THRESHOLD <= bufsz (S k).
Proof.
  intros k. unfold bufsz, BUF0, MMAP_THRESHOLD. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  assert (1 <= 2 ^ Z.of_nat k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). nia.
Qed.

Lemma hist_PHI : forall k s p, histR k s p -> PHI (ps_m s).
Proof.
  intros k s p H. induction H as [p s1 (L & L1 & Hc & Hp) | k s p p' s1 s2 Hh IH (L & L1 & Hc & Hp) (L2 & L3 & Hc2 & Hin & Hf)].
  - eapply T2_A; [exact Hc | exact Hp].
  - eapply T2_Bf_sim; [| exact Hc2 | exact Hin | exact Hf].
    eapply T2_Bm_sim; [exact IH | exact Hc | apply bufsz_ge | eapply cpath_some_not_overflow; exact Hp | exact Hp].
Qed.

Lemma KREL_creach : forall s LB mo, KREL s LB mo -> exists L, MI_Contracts.SIMREL (ps_m s) L /\ KL L (ps_brk s) mo.
Proof. intros s LB mo [(L & Hc & HK & _) _]. exists L. auto. Qed.

Lemma ctree_ok_root : forall L e (k : Z -> Malloc.M (mstate * option cptr)) Post,
  ctree_ok L (SVis e k) Post -> event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post.
Proof. intros L e k Post H. exact H. Qed.

Lemma one_mmap_succ : forall s mo n L lo hi j,
  MI_Contracts.SIMREL (ps_m s) L -> KL L (ps_brk s) mo -> 0 <= n ->
  one_mmap L (cmalloc (ps_m s) n) lo hi -> 0 < lo -> hi <= 2 ^ 27 - 4096 ->
  mo_ok mo -> room mo j -> 0 <= j <= 27 ->
  malloc_can_succeed s mo n.
Proof.
  intros s mo n L lo hi j Hc HK Hn (len & kont & E & Hlen & _ & Hsucc) Hlo Hhi Hmo Hroom Hj.
  set (e := EMmap 0 len PROT_RW MAPF) in *.

  pose proof (MI_Contracts.cmalloc_contract_sim _ _ _ Hc Hn) as CT. rewrite E in CT.
  destruct (ctree_ok_root _ _ _ _ CT) as [Hpre _].

  set (nZ := page_round_up_Z len).
  assert (HnZ : len <= nZ <= 2 ^ 27) by (unfold nZ, page_round_up_Z, page_size; lia).
  destruct (room_grant mo j nZ Hroom Hj Hmo (kl_ceil _ _ _ HK) ltac:(lia)) as [a Hg].
  destruct (ev_mmap_grant_path len PROT_RW s mo a ltac:(lia) ltac:(lia) (or_introl eq_refl) Hmo (kl_ceil _ _ _ HK) Hg) as (mo' & Hev & Hmo' & Hva & _ & _ & _).

  assert (Hok : answer_ok L e (bv_unsigned a) = true).
  { pose proof (ev_step_spec L e GT s frame_ok_GT Hpre s mo (conj eq_refl (conj HK I))) as W.
    exact (proj1 (twf_tpath _ _ _ _ _ _ W Hev)). }
  assert (Herr : is_err (bv_unsigned a) = false).
  { destruct Hg as (_ & _ & G3 & _). pose proof (kl_ceil _ _ _ HK) as CK. unfold ceil_ok in CK. pose_ceil.
    unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  destruct (Hsucc (bv_unsigned a) Herr Hok) as (cs2 & c & Hk).
  exists (c, fresh_off cs2 c n). eexists _, mo'.
  apply (mpath_raw_malloc n s mo [bv_unsigned a] cs2 (Some c) s mo').
  rewrite E. cbn [mreal]. exists s, mo'. split; [exact Hev|]. rewrite Hk. cbn. repeat split; reflexivity.
Qed.

Theorem MF_C_succ : MF_C_succ_stmt.
Proof.
  intros k s p A mo n j Hh HK Hmo Hk Hn Hroom Hj.
  destruct (KREL_creach _ _ _ HK) as (L & Hc & HKL).
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hsmall | Hbig].
  - eapply (one_mmap_succ s mo n L 1 (2 ^ 21) j); try assumption; try lia.
    apply T2_C_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia].
  - eapply (one_mmap_succ s mo n L (n + IB + UNIT) (n + IB + UNIT) j); try assumption; try lia.
    + apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia |]. unfold size_overflows. apply Z.leb_gt. lia.
    + unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
    + unfold IB, UNIT. lia.
Qed.

Lemma bufsz_le : forall k, (k <= 10)%nat -> bufsz k <= 2 ^ 26.
Proof.
  intros k Hk. unfold bufsz, BUF0. change (2 ^ 26) with (65536 * 2 ^ 10).
  apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Theorem MF_B_succ : MF_B_succ_stmt.
Proof.
  intros k s p A mo j Hh HK Hmo Hk Hroom Hj.
  destruct (KREL_creach _ _ _ HK) as (L & Hc & HKL).
  pose proof (bufsz_ge k) as G1. pose proof (bufsz_le (S k) ltac:(lia)) as G2.
  eapply (one_mmap_succ s mo (bufsz (S k)) L (bufsz (S k) + IB + UNIT) (bufsz (S k) + IB + UNIT) j); try assumption.
  - unfold MMAP_THRESHOLD in G1. lia.
  - apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | exact G1 |]. unfold size_overflows. apply Z.leb_gt. lia.
  - unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
  - unfold IB, UNIT. lia.
Qed.

Lemma answer_ok_mmap_cases : forall L len z, 0 < len ->
  answer_ok L (EMmap 0 len PROT_RW MAPF) z = true -> is_errno_form z = true \/ is_err z = false.
Proof.
  intros L len z Hlen H. cbn [answer_ok] in H. change (Z.land MAPF Malloc.MAP_FIXED =? 0) with true in H. cbn iota in H.
  unfold mmap_answer_ok in H. destruct (is_errno_form z) eqn:E; [left; reflexivity | right].
  cbn [orb] in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply Z.leb_le in H3.
  unfold is_err. apply Z.ltb_ge. pose proof alloc_ceiling_lt. unfold TWO64. pose proof (round_up_pg_ge len). lia.
Qed.

Lemma one_mmap_evs : forall L t lo hi zs, 0 < lo ->
  one_mmap L t lo hi -> okpath L t zs ->
  exists len, lo <= len <= hi /\ evs_of t zs = [EMmap 0 len PROT_RW MAPF].
Proof.
  intros L t lo hi zs Hlo (len & kont & -> & Hlen & Hfail & Hsucc) Hok.
  destruct zs as [| z zs]; cbn [okpath] in Hok; [destruct Hok|]. destruct Hok as [Hz Hok].
  exists len. split; [exact Hlen|]. cbn [evs_of]. f_equal.
  destruct (answer_ok_mmap_cases L len z ltac:(lia) Hz) as [Herr | Hok'].
  - destruct (Hfail z Herr) as [cs1 Hk]. rewrite Hk in Hok |- *. destruct zs; [reflexivity | destruct Hok].
  - destruct (Hsucc z Hok' Hz) as (cs2 & c & Hk). rewrite Hk in Hok |- *. destruct zs; [reflexivity | destruct Hok].
Qed.

Lemma esize_mmap_bound : forall a len p f B, 0 < len -> len + 4096 <= B -> esize (EMmap a len p f) <= B.
Proof.
  intros a len p f B Hl HB. cbn [esize]. unfold page_round_up_Z, page_size.
  pose proof (Z_div_mod_eq_full (len + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (len + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma one_mmap_room : forall s LB mo n r s' mo' j lo hi,
  KREL s LB mo -> mo_ok mo -> 0 <= n -> room mo j -> 0 <= j ->
  (forall L, MI_Contracts.SIMREL (ps_m s) L -> one_mmap L (cmalloc (ps_m s) n) lo hi) -> 0 < lo -> hi + 4096 <= (2 ^ 26 + 2 ^ 20) ->
  mpath (raw_malloc n) s mo r s' mo' -> room mo' (j + 1).
Proof.
  intros s LB mo n r s' mo' j lo hi HK Hmo Hn Hroom Hj Hone Hlo Hhi Hp.
  destruct (raw_malloc_measure n s LB mo r s' mo' 1 (2 ^ 26 + 2 ^ 20) HK Hmo Hn) as (k' & E' & Hk & HE & MS); [| exact Hp |].
  - intros L zs Hc Hok. destruct (one_mmap_evs L _ lo hi zs Hlo (Hone L Hc) Hok) as (len & Hlen & ->).
    cbn [length esum]. split; [lia|]. rewrite Z.add_0_r. apply esize_mmap_bound; lia.
  - eapply room_step; [exact Hroom | exact Hj | exact MS | lia | lia].
Qed.

Theorem MF3_C : MF3_C_stmt.
Proof.
  intros k s p A mo n j r s' mo' Hh HK Hmo Hk Hn Hroom Hj Hp.
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hsmall | Hbig].
  - eapply (one_mmap_room s _ mo n r s' mo' j 1 (2 ^ 21)); try eassumption; try lia.
    intros L Hc. apply T2_C_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia].
  - eapply (one_mmap_room s _ mo n r s' mo' j (n + IB + UNIT) (n + IB + UNIT)); try eassumption; try lia.
    + intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia |]. unfold size_overflows. apply Z.leb_gt. lia.
    + unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
    + unfold IB, UNIT. lia.
Qed.

Theorem MF3_B : MF3_B_stmt.
Proof.
  intros k s p A mo j r s' mo' Hh HK Hmo Hk Hroom Hj Hp.
  pose proof (bufsz_ge k) as G1. pose proof (bufsz_le (S k) ltac:(lia)) as G2.
  eapply (one_mmap_room s _ mo (bufsz (S k)) r s' mo' j (bufsz (S k) + IB + UNIT) (bufsz (S k) + IB + UNIT)); try eassumption.
  - unfold MMAP_THRESHOLD in G1. lia.
  - intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | exact G1 |]. unfold size_overflows. apply Z.leb_gt. lia.
  - unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
  - unfold IB, UNIT. lia.
Qed.

Lemma one_mmap_must : forall s LB mo n j lo hi,
  KREL s LB mo -> mo_ok mo -> 0 <= n -> room mo j -> 0 <= j < 28 ->
  (forall L, MI_Contracts.SIMREL (ps_m s) L -> one_mmap L (cmalloc (ps_m s) n) lo hi) -> 0 < lo -> hi + 4096 <= (2 ^ 26 + 2 ^ 20) ->
  malloc_must_succeed s mo n.
Proof.
  intros s LB mo n j lo hi HK Hmo Hn R Hj Hone Hlo Hhi r s' mo' Hp.
  assert (HB : forall L zs, MI_Contracts.SIMREL (ps_m s) L -> okpath L (cmalloc (ps_m s) n) zs ->
     (length (evs_of (cmalloc (ps_m s) n) zs) <= 64)%nat /\ esum (evs_of (cmalloc (ps_m s) n) zs) <= (2 ^ 26 + 2 ^ 20)).
  { intros L zs Hc Hok. destruct (one_mmap_evs L _ lo hi zs Hlo (Hone L Hc) Hok) as (len & Hlen & ->).
    cbn [length esum]. split; [lia|]. rewrite Z.add_0_r. apply esize_mmap_bound; lia. }
  destruct (raw_malloc_noref n s LB mo r s' mo' j HK Hmo Hn R Hj HB Hp) as (L & zs & st' & p & Hc & Hf & Hok & Hnr & ->).
  destruct (Hone L Hc) as (len & kont & E & Hlen & _ & Hsucc).
  rewrite E in Hf, Hok, Hnr.
  destruct zs as [| z zs]; [cbn [okpath] in Hok; destruct Hok|].
  cbn [okpath] in Hok. destruct Hok as [Hz _]. cbn [noref] in Hnr. destruct Hnr as [Hnz _].
  specialize (Hnz eq_refl).
  destruct (Hsucc z Hnz Hz) as (cs2 & c & Hk). cbn [follow] in Hf. rewrite Hk in Hf. cbn [follow] in Hf.
  injection Hf as <- <-. discriminate.
Qed.

Theorem MF_C_must : MF_C_must_stmt.
Proof.
  intros k s p A mo n j Hh HK Hmo Hk Hn Hroom Hj.
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hsmall | Hbig].
  - eapply (one_mmap_must s _ mo n j 1 (2 ^ 21)); try eassumption; try lia.
    intros L Hc. apply T2_C_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia].
  - eapply (one_mmap_must s _ mo n j (n + IB + UNIT) (n + IB + UNIT)); try eassumption; try lia.
    + intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia |]. unfold size_overflows. apply Z.leb_gt. lia.
    + unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
    + unfold IB, UNIT. lia.
Qed.

Theorem MF_B_must : MF_B_must_stmt.
Proof.
  intros k s p A mo j Hh HK Hmo Hk Hroom Hj.
  pose proof (bufsz_ge k) as G1. pose proof (bufsz_le (S k) ltac:(lia)) as G2.
  eapply (one_mmap_must s _ mo (bufsz (S k)) j (bufsz (S k) + IB + UNIT) (bufsz (S k) + IB + UNIT)); try eassumption.
  - unfold MMAP_THRESHOLD in G1. lia.
  - lia.
  - intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | exact G1 |]. unfold size_overflows. apply Z.leb_gt. lia.
  - unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
  - unfold IB, UNIT. lia.
Qed.

End Sites.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.DecodeM.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.PgArith.
Import F_syscalls.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NodeSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Grant OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MMeas OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NoRefuse OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MFMust.
Import MF.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition T2_A_stmt (PHI : mstate -> Prop) : Prop :=
  forall L L1 cs1 c, MI_Contracts.SIMREL (ps_m s0) L -> cpath L (cmalloc (ps_m s0) BUF0) L1 (cs1, Some c) -> PHI cs1.
Definition T2_Bm_stmt (PHI PHIB : mstate -> Prop) : Prop :=
  forall cs L L' cs' c n, PHI cs -> MI_Contracts.SIMREL cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  cpath L (cmalloc cs n) L' (cs', Some c) -> PHIB cs'.
Definition T2_Bf_stmt (PHI PHIB : mstate -> Prop) : Prop :=
  forall cs L L' cs' c, PHIB cs -> MI_Contracts.SIMREL cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' -> PHI cs'.

Definition one_mmap (L : mled) (t : Malloc.M (mstate * option cptr)) (lenlo lenhi : Z) : Prop :=
  exists len kont, t = SVis (EMmap 0 len PROT_RW MAPF) kont /\ lenlo <= len <= lenhi
    /\ (forall z, is_errno_form z = true -> exists cs1, kont z = SRet (cs1, None))
    /\ (forall a, is_err a = false -> answer_ok L (EMmap 0 len PROT_RW MAPF) a = true -> exists cs2 c, kont a = SRet (cs2, Some c)).
Definition T2_C_stmt (PHI : mstate -> Prop) : Prop :=
  forall cs L n, PHI cs -> MI_Contracts.SIMREL cs L -> 0 < n < MMAP_THRESHOLD -> one_mmap L (cmalloc cs n) 1 (2 ^ 21).
Definition T2_Cbig_stmt (PHI : mstate -> Prop) : Prop :=
  forall cs L n, PHI cs -> MI_Contracts.SIMREL cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  one_mmap L (cmalloc cs n) (n + IB + UNIT) (n + IB + UNIT).

Section Sites.
Variables PHI PHIB : mstate -> Prop.
Hypothesis T2_A : T2_A_stmt PHI.
Hypothesis T2_Bm_sim : T2_Bm_stmt PHI PHIB.
Hypothesis T2_Bf_sim : T2_Bf_stmt PHI PHIB.
Hypothesis T2_C_sim : T2_C_stmt PHI.
Hypothesis T2_Cbig_sim : T2_Cbig_stmt PHI.

Lemma cpath_some_not_overflow : forall cs n L L' cs' c,
  cpath L (cmalloc cs n) L' (cs', Some c) -> size_overflows n = false.
Proof.
  intros cs n L L' cs' c H. destruct (size_overflows n) eqn:E; [| reflexivity].
  rewrite (cmalloc_overflow _ _ E) in H. inversion H.
Qed.

Lemma bufsz_ge : forall k, MMAP_THRESHOLD <= bufsz (S k).
Proof.
  intros k. unfold bufsz, BUF0, MMAP_THRESHOLD. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  assert (1 <= 2 ^ Z.of_nat k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). nia.
Qed.

Lemma hist_PHI : forall k s p, histR k s p -> PHI (ps_m s).
Proof.
  intros k s p H. induction H as [p s1 (L & L1 & Hc & Hp) | k s p p' s1 s2 Hh IH (L & L1 & Hc & Hp) (L2 & L3 & Hc2 & Hin & Hf)].
  - eapply T2_A; [exact Hc | exact Hp].
  - eapply T2_Bf_sim; [| exact Hc2 | exact Hin | exact Hf].
    eapply T2_Bm_sim; [exact IH | exact Hc | apply bufsz_ge | eapply cpath_some_not_overflow; exact Hp | exact Hp].
Qed.

Lemma KREL_creach : forall s LB mo, KREL s LB mo -> exists L, MI_Contracts.SIMREL (ps_m s) L /\ KL L (ps_brk s) mo.
Proof. intros s LB mo [(L & Hc & HK & _) _]. exists L. auto. Qed.

Lemma ctree_ok_root : forall L e (k : Z -> Malloc.M (mstate * option cptr)) Post,
  ctree_ok L (SVis e k) Post -> event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post.
Proof. intros L e k Post H. exact H. Qed.

Lemma one_mmap_succ : forall s mo n L lo hi j,
  MI_Contracts.SIMREL (ps_m s) L -> KL L (ps_brk s) mo -> 0 <= n ->
  one_mmap L (cmalloc (ps_m s) n) lo hi -> 0 < lo -> hi <= 2 ^ 27 - 4096 ->
  mo_ok mo -> room mo j -> 0 <= j <= 27 ->
  malloc_can_succeed s mo n.
Proof.
  intros s mo n L lo hi j Hc HK Hn (len & kont & E & Hlen & _ & Hsucc) Hlo Hhi Hmo Hroom Hj.
  set (e := EMmap 0 len PROT_RW MAPF) in *.

  pose proof (MI_Contracts.cmalloc_contract_sim _ _ _ Hc Hn) as CT. rewrite E in CT.
  destruct (ctree_ok_root _ _ _ _ CT) as [Hpre _].

  set (nZ := page_round_up_Z len).
  assert (HnZ : len <= nZ <= 2 ^ 27) by (unfold nZ, page_round_up_Z, page_size; lia).
  destruct (room_grant mo j nZ Hroom Hj Hmo (kl_ceil _ _ _ HK) ltac:(lia)) as [a Hg].
  destruct (ev_mmap_grant_path len PROT_RW s mo a ltac:(lia) ltac:(lia) (or_introl eq_refl) Hmo (kl_ceil _ _ _ HK) Hg) as (mo' & Hev & Hmo' & Hva & _ & _ & _).

  assert (Hok : answer_ok L e (bv_unsigned a) = true).
  { pose proof (ev_step_spec L e GT s frame_ok_GT Hpre s mo (conj eq_refl (conj HK I))) as W.
    exact (proj1 (twf_tpath _ _ _ _ _ _ W Hev)). }
  assert (Herr : is_err (bv_unsigned a) = false).
  { destruct Hg as (_ & _ & G3 & _). pose proof (kl_ceil _ _ _ HK) as CK. unfold ceil_ok in CK. pose_ceil.
    unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  destruct (Hsucc (bv_unsigned a) Herr Hok) as (cs2 & c & Hk).
  exists (c, fresh_off cs2 c n). eexists _, mo'.
  apply (mpath_raw_malloc n s mo [bv_unsigned a] cs2 (Some c) s mo').
  rewrite E. cbn [mreal]. exists s, mo'. split; [exact Hev|]. rewrite Hk. cbn. repeat split; reflexivity.
Qed.

Theorem MF_C_succ : MF_C_succ_stmt.
Proof.
  intros k s p A mo n j Hh HK Hmo Hk Hn Hroom Hj.
  destruct (KREL_creach _ _ _ HK) as (L & Hc & HKL).
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hsmall | Hbig].
  - eapply (one_mmap_succ s mo n L 1 (2 ^ 21) j); try assumption; try lia.
    apply T2_C_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia].
  - eapply (one_mmap_succ s mo n L (n + IB + UNIT) (n + IB + UNIT) j); try assumption; try lia.
    + apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia |]. unfold size_overflows. apply Z.leb_gt. lia.
    + unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
    + unfold IB, UNIT. lia.
Qed.

Lemma bufsz_le : forall k, (k <= 10)%nat -> bufsz k <= 2 ^ 26.
Proof.
  intros k Hk. unfold bufsz, BUF0. change (2 ^ 26) with (65536 * 2 ^ 10).
  apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Theorem MF_B_succ : MF_B_succ_stmt.
Proof.
  intros k s p A mo j Hh HK Hmo Hk Hroom Hj.
  destruct (KREL_creach _ _ _ HK) as (L & Hc & HKL).
  pose proof (bufsz_ge k) as G1. pose proof (bufsz_le (S k) ltac:(lia)) as G2.
  eapply (one_mmap_succ s mo (bufsz (S k)) L (bufsz (S k) + IB + UNIT) (bufsz (S k) + IB + UNIT) j); try assumption.
  - unfold MMAP_THRESHOLD in G1. lia.
  - apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | exact G1 |]. unfold size_overflows. apply Z.leb_gt. lia.
  - unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
  - unfold IB, UNIT. lia.
Qed.

Lemma answer_ok_mmap_cases : forall L len z, 0 < len ->
  answer_ok L (EMmap 0 len PROT_RW MAPF) z = true -> is_errno_form z = true \/ is_err z = false.
Proof.
  intros L len z Hlen H. cbn [answer_ok] in H. change (Z.land MAPF Malloc.MAP_FIXED =? 0) with true in H. cbn iota in H.
  unfold mmap_answer_ok in H. destruct (is_errno_form z) eqn:E; [left; reflexivity | right].
  cbn [orb] in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply Z.leb_le in H3.
  unfold is_err. apply Z.ltb_ge. pose proof alloc_ceiling_lt. unfold TWO64. pose proof (round_up_pg_ge len). lia.
Qed.

Lemma one_mmap_evs : forall L t lo hi zs, 0 < lo ->
  one_mmap L t lo hi -> okpath L t zs ->
  exists len, lo <= len <= hi /\ evs_of t zs = [EMmap 0 len PROT_RW MAPF].
Proof.
  intros L t lo hi zs Hlo (len & kont & -> & Hlen & Hfail & Hsucc) Hok.
  destruct zs as [| z zs]; cbn [okpath] in Hok; [destruct Hok|]. destruct Hok as [Hz Hok].
  exists len. split; [exact Hlen|]. cbn [evs_of]. f_equal.
  destruct (answer_ok_mmap_cases L len z ltac:(lia) Hz) as [Herr | Hok'].
  - destruct (Hfail z Herr) as [cs1 Hk]. rewrite Hk in Hok |- *. destruct zs; [reflexivity | destruct Hok].
  - destruct (Hsucc z Hok' Hz) as (cs2 & c & Hk). rewrite Hk in Hok |- *. destruct zs; [reflexivity | destruct Hok].
Qed.

Lemma esize_mmap_bound : forall a len p f B, 0 < len -> len + 4096 <= B -> esize (EMmap a len p f) <= B.
Proof.
  intros a len p f B Hl HB. cbn [esize]. unfold page_round_up_Z, page_size.
  pose proof (Z_div_mod_eq_full (len + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (len + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma one_mmap_room : forall s LB mo n r s' mo' j lo hi,
  KREL s LB mo -> mo_ok mo -> 0 <= n -> room mo j -> 0 <= j ->
  (forall L, MI_Contracts.SIMREL (ps_m s) L -> one_mmap L (cmalloc (ps_m s) n) lo hi) -> 0 < lo -> hi + 4096 <= (2 ^ 26 + 2 ^ 20) ->
  mpath (raw_malloc n) s mo r s' mo' -> room mo' (j + 1).
Proof.
  intros s LB mo n r s' mo' j lo hi HK Hmo Hn Hroom Hj Hone Hlo Hhi Hp.
  destruct (raw_malloc_measure n s LB mo r s' mo' 1 (2 ^ 26 + 2 ^ 20) HK Hmo Hn) as (k' & E' & Hk & HE & MS); [| exact Hp |].
  - intros L zs Hc Hok. destruct (one_mmap_evs L _ lo hi zs Hlo (Hone L Hc) Hok) as (len & Hlen & ->).
    cbn [length esum]. split; [lia|]. rewrite Z.add_0_r. apply esize_mmap_bound; lia.
  - eapply room_step; [exact Hroom | exact Hj | exact MS | lia | lia].
Qed.

Theorem MF3_C : MF3_C_stmt.
Proof.
  intros k s p A mo n j r s' mo' Hh HK Hmo Hk Hn Hroom Hj Hp.
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hsmall | Hbig].
  - eapply (one_mmap_room s _ mo n r s' mo' j 1 (2 ^ 21)); try eassumption; try lia.
    intros L Hc. apply T2_C_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia].
  - eapply (one_mmap_room s _ mo n r s' mo' j (n + IB + UNIT) (n + IB + UNIT)); try eassumption; try lia.
    + intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia |]. unfold size_overflows. apply Z.leb_gt. lia.
    + unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
    + unfold IB, UNIT. lia.
Qed.

Theorem MF3_B : MF3_B_stmt.
Proof.
  intros k s p A mo j r s' mo' Hh HK Hmo Hk Hroom Hj Hp.
  pose proof (bufsz_ge k) as G1. pose proof (bufsz_le (S k) ltac:(lia)) as G2.
  eapply (one_mmap_room s _ mo (bufsz (S k)) r s' mo' j (bufsz (S k) + IB + UNIT) (bufsz (S k) + IB + UNIT)); try eassumption.
  - unfold MMAP_THRESHOLD in G1. lia.
  - intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | exact G1 |]. unfold size_overflows. apply Z.leb_gt. lia.
  - unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
  - unfold IB, UNIT. lia.
Qed.

Lemma one_mmap_must : forall s LB mo n j lo hi,
  KREL s LB mo -> mo_ok mo -> 0 <= n -> room mo j -> 0 <= j < 28 ->
  (forall L, MI_Contracts.SIMREL (ps_m s) L -> one_mmap L (cmalloc (ps_m s) n) lo hi) -> 0 < lo -> hi + 4096 <= (2 ^ 26 + 2 ^ 20) ->
  malloc_must_succeed s mo n.
Proof.
  intros s LB mo n j lo hi HK Hmo Hn R Hj Hone Hlo Hhi r s' mo' Hp.
  assert (HB : forall L zs, MI_Contracts.SIMREL (ps_m s) L -> okpath L (cmalloc (ps_m s) n) zs ->
     (length (evs_of (cmalloc (ps_m s) n) zs) <= 64)%nat /\ esum (evs_of (cmalloc (ps_m s) n) zs) <= (2 ^ 26 + 2 ^ 20)).
  { intros L zs Hc Hok. destruct (one_mmap_evs L _ lo hi zs Hlo (Hone L Hc) Hok) as (len & Hlen & ->).
    cbn [length esum]. split; [lia|]. rewrite Z.add_0_r. apply esize_mmap_bound; lia. }
  destruct (raw_malloc_noref n s LB mo r s' mo' j HK Hmo Hn R Hj HB Hp) as (L & zs & st' & p & Hc & Hf & Hok & Hnr & ->).
  destruct (Hone L Hc) as (len & kont & E & Hlen & _ & Hsucc).
  rewrite E in Hf, Hok, Hnr.
  destruct zs as [| z zs]; [cbn [okpath] in Hok; destruct Hok|].
  cbn [okpath] in Hok. destruct Hok as [Hz _]. cbn [noref] in Hnr. destruct Hnr as [Hnz _].
  specialize (Hnz eq_refl).
  destruct (Hsucc z Hnz Hz) as (cs2 & c & Hk). cbn [follow] in Hf. rewrite Hk in Hf. cbn [follow] in Hf.
  injection Hf as <- <-. discriminate.
Qed.

Theorem MF_C_must : MF_C_must_stmt.
Proof.
  intros k s p A mo n j Hh HK Hmo Hk Hn Hroom Hj.
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hsmall | Hbig].
  - eapply (one_mmap_must s _ mo n j 1 (2 ^ 21)); try eassumption; try lia.
    intros L Hc. apply T2_C_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia].
  - eapply (one_mmap_must s _ mo n j (n + IB + UNIT) (n + IB + UNIT)); try eassumption; try lia.
    + intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | lia |]. unfold size_overflows. apply Z.leb_gt. lia.
    + unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
    + unfold IB, UNIT. lia.
Qed.

Theorem MF_B_must : MF_B_must_stmt.
Proof.
  intros k s p A mo j Hh HK Hmo Hk Hroom Hj.
  pose proof (bufsz_ge k) as G1. pose proof (bufsz_le (S k) ltac:(lia)) as G2.
  eapply (one_mmap_must s _ mo (bufsz (S k)) j (bufsz (S k) + IB + UNIT) (bufsz (S k) + IB + UNIT)); try eassumption.
  - unfold MMAP_THRESHOLD in G1. lia.
  - lia.
  - intros L Hc. apply T2_Cbig_sim; [exact (hist_PHI _ _ _ Hh) | exact Hc | exact G1 |]. unfold size_overflows. apply Z.leb_gt. lia.
  - unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
  - unfold IB, UNIT. lia.
Qed.

End Sites.

End CEIL.
End TwinB.
