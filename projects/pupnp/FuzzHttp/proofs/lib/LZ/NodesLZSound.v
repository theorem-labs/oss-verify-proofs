(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree RelSpec RelSpecX Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require AsanAcct BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Restrict.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.

#[using="HH"] Lemma seg_rom_hidden : forall a, H a = true -> seg_rom segs a = None.
Proof. intros a Ha. unfold seg_rom. rewrite (AsanAcct.memory_read1_hidden segs H HH a Ha). reflexivity. Qed.

#[using="HH"] Lemma mrd_mrestrict : forall m a,
  mrd segs (AsanAcct.mrestrict H m) a = if H a then None else mrd segs m a.
Proof.
  intros m a. unfold mrd, AsanAcct.mrestrict. destruct (H a) eqn:Ha; [| reflexivity]. apply seg_rom_hidden. exact Ha.
Qed.

#[using="HH"] Lemma bytes_at_unrestrict : forall m a bs,
  bytes_at segs (AsanAcct.mrestrict H m) a bs -> bytes_at segs m a bs.
Proof.
  intros m a bs (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|].
  intros i Hi. specialize (HB i Hi). rewrite mrd_mrestrict in HB.
  destruct (H (wa (a + Z.of_nat i))); [| exact HB].
  symmetry in HB. apply nth_error_None in HB. lia.
Qed.

#[using="HH"] Lemma bytes_at_visible : forall m a bs,
  bytes_at segs (AsanAcct.mrestrict H m) a bs -> forall i, (i < length bs)%nat -> H (wa (a + Z.of_nat i)) = false.
Proof.
  intros m a bs (H0 & H1 & HB) i Hi. specialize (HB i Hi). rewrite mrd_mrestrict in HB.
  destruct (H (wa (a + Z.of_nat i))); [| reflexivity].
  symmetry in HB. apply nth_error_None in HB. lia.
Qed.

#[using="HH"] Lemma wr_at_unrestrict : forall m a n,
  wr_at segs (AsanAcct.mrestrict H m) a n -> wr_at segs m a n.
Proof.
  intros m a n (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. specialize (HW i Hi). rewrite (AsanAcct.wview_restrict segs H HH) in HW.
  destruct (H (wa (a + i))); [exfalso; apply HW; reflexivity| exact HW].
Qed.

#[using="HH"] Lemma wr_at_visible : forall m a n,
  wr_at segs (AsanAcct.mrestrict H m) a n -> forall i, 0 <= i < n -> H (wa (a + i)) = false.
Proof.
  intros m a n (H0 & H1 & HW) i Hi. specialize (HW i Hi). rewrite (AsanAcct.wview_restrict segs H HH) in HW.
  destruct (H (wa (a + i))); [exfalso; apply HW; reflexivity| reflexivity].
Qed.

#[using="HH"] Lemma at_node_unrestrict : forall n msF,
  at_node segs n (restrict H msF) -> at_node segs n msF.
Proof.
  intros n msF Hat. destruct n; cbn [at_node] in Hat |- *; unfold areg in *;
    rewrite ?AsanAcct.restrict_svc_pending, ?AsanAcct.restrict_regs, ?AsanAcct.restrict_rom, ?AsanAcct.restrict_mem in Hat;
    try exact Hat.
  -
    destruct Hat as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & iovs & B1 & B2 & B3).
    repeat (split; [assumption|]). exists iovs. split; [eapply bytes_at_unrestrict; exact B1|]. split; [exact B2|].
    eapply Forall2_impl; [| exact B3]. cbn beta. intros iov bs [E Hb]. split; [exact E| eapply bytes_at_unrestrict; exact Hb].
  -
    destruct Hat as (A1 & A2 & A3 & A4 & A5 & A6 & A7). repeat (split; [assumption|]). eapply bytes_at_unrestrict; exact A7.
  -
    destruct Hat as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [assumption|]). eapply wr_at_unrestrict; exact A8.
  -
    destruct Hat as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). repeat (split; [assumption|]). eapply bytes_at_unrestrict; exact A9.
  -
    destruct Hat as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & iovs & B1 & B2 & B3).
    repeat (split; [assumption|]). exists iovs. split; [eapply bytes_at_unrestrict; exact B1|]. split; [exact B2|].
    eapply Forall2_impl; [| exact B3]. cbn beta. intros iov bs [E Hb]. split; [exact E| eapply bytes_at_unrestrict; exact Hb].
  -
    destruct Hat as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
    repeat (split; [assumption|]). split; [eapply bytes_at_unrestrict; exact A14|].
    split; eapply wr_at_unrestrict; eassumption.
  -
    destruct Hat as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11). repeat (split; [assumption|]). eapply bytes_at_unrestrict; exact A11.
Qed.

End Restrict.

Lemma eff_ret_strip : forall e, eff_ret (strip e) = eff_ret e.
Proof. intros e. reflexivity. Qed.

Lemma ret_alignedb_strip : forall e e', strip e' = strip e -> ret_alignedb e' = ret_alignedb e.
Proof. intros e e' E. unfold ret_alignedb. rewrite <- (eff_ret_strip e'), <- (eff_ret_strip e), E. reflexivity. Qed.

Lemma hideL_strip : forall n e e' H, strip e' = strip e -> hideL n e' H = hideL n e H.
Proof.
  intros n e e' H E. pose proof (ret_alignedb_strip e e' E) as R.
  assert (ER : eff_ret e' = eff_ret e) by (rewrite <- (eff_ret_strip e'), <- (eff_ret_strip e), E; reflexivity).
  destruct n as [n| | | | |]; cbn [hideL]; rewrite ?R, ?ER; try reflexivity.
  all: destruct n; rewrite ?R, ?ER; reflexivity.
Qed.

Lemma allowL_strip : forall n e e' P, strip e' = strip e -> allowL n e' P = allowL n e P.
Proof.
  intros n e e' P E. pose proof (ret_alignedb_strip e e' E) as R.
  assert (ER : eff_ret e' = eff_ret e) by (rewrite <- (eff_ret_strip e'), <- (eff_ret_strip e), E; reflexivity).
  destruct n as [n| | | | |]; cbn [allowL]; rewrite ?R, ?ER; try reflexivity.
Qed.

Lemma perase_wvb_same : forall P mo X, perase P (with_vm_backing (m_vm_lazy mo) X mo) = perase P mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm] X. reflexivity. Qed.

Section Kit.
Variable segs : list Segment.

Notation lzframe := (lzframe segs minvL).

Definition hide_ok (n : nodeL) (eff : resp) (H : word -> bool) (accs : list (word * nat)) : Prop :=
  (forall a, hideL n eff H a = true -> H a = true)
  \/ (accs = [] /\ forall a, hideL n eff H a = true -> H a = true \/ find_segment segs (bv_unsigned a) 1 = None).
#[using="Type"] Lemma hide_ok_mono : forall n eff H accs, (forall a, hideL n eff H a = true -> H a = true) -> hide_ok n eff H accs.
Proof. intros n eff H accs M. left. exact M. Qed.
#[using="Type"] Lemma hide_ok_strip : forall n rsp eff' H accs, strip eff' = strip rsp -> hide_ok n eff' H accs -> hide_ok n rsp H accs.
Proof. intros n rsp eff' H accs E HK. unfold hide_ok in *. rewrite <- (hideL_strip n rsp eff' H E). exact HK. Qed.

Record factsL (n : nodeL) (H : word -> bool) (P : list word) (msF : machine_state) (mo : Model) (x8 : word) : Prop := mkFL {
  fl_svc : ms_svc_pending msF = Some x8;

  fl_complete : forall eff mo1 evs, syscall_spec (sys_input segs msF x8) mo (Ok eff mo1 evs) ->
      nstepL n (perase P mo) eff (perase (allowL n eff P) mo1) evs
      /\ m_halted mo1 = None
      /\ MInv (ivl (allowL n eff P)) mo1
      /\ lazy_cover (hideL n eff H) (m_vm_lazy mo1) (ivl (allowL n eff P))
      /\ P_aligned (allowL n eff P)
      /\ minvL (perase (allowL n eff P) mo1)
      /\ AsanAcct.ranges_avoid H (syscall_effect_accesses eff)
      /\ eff_copies eff = []
      /\ hzero (hideL n eff H) (nret msF eff)
      /\ hide_ok n eff H (syscall_effect_accesses eff)

      /\ (forall x, H x = true -> hideL n eff H x = false ->
            zb x = true \/ zeros_cover (eff_zeros eff) x = true \/ zeros_cover (eff_unmaps eff) x = true);
  fl_nounmod : ~ syscall_spec (sys_input segs msF x8) mo Unmodeled;

  fl_sound : forall eff moE' evs, nstepL n (perase P mo) eff moE' evs ->
      exists eff' mo1, strip eff' = strip eff /\ syscall_spec (sys_input segs msF x8) mo (Ok eff' mo1 evs)
                       /\ perase (allowL n eff P) mo1 = moE';
  fl_progress : exists eff moE' evs, nstepL n (perase P mo) eff moE' evs }.

#[using="Type"] Lemma materialize_after : forall n H P eff accs mo1,
  MInv (ivl (allowL n eff P)) mo1 ->
  lazy_cover (hideL n eff H) (m_vm_lazy mo1) (ivl (allowL n eff P)) ->
  P_aligned (allowL n eff P) ->
  hide_ok n eff H accs ->
  AsanAcct.ranges_avoid H accs ->
  exists mat', materialize_model_accesses mo1 accs = Some (with_vm_backing (m_vm_lazy mo1) mat' mo1)
               /\ MInv (ivl (allowL n eff P)) (with_vm_backing (m_vm_lazy mo1) mat' mo1).
Proof.
  intros n H P eff accs mo1 HI HC HA [HS|[EA _]] HR.
  - apply (AsanAcct.materialize_restricted H (ivl (allowL n eff P)) mo1 _); [| apply A_wf_ivl; exact HA| exact HI| exact HR].
    intros w Hl Hw. apply HC; [exact Hl|]. destruct (hideL n eff H w) eqn:E; [| reflexivity]. rewrite (HS w E) in Hw. discriminate.
  -
    rewrite EA. exists (m_vm_materialized mo1).
    assert (E : with_vm_backing (m_vm_lazy mo1) (m_vm_materialized mo1) mo1 = mo1) by (destruct mo1 as [fd [maps lazy mat] io fs proc lim tm]; reflexivity).
    rewrite E. split; [| exact HI]. unfold materialize_model_accesses, materialize_accesses. cbn. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma node_kitL : forall n H P msF mo x8,
  factsL n H P msF mo x8 -> lzframe H P mo -> hzero H msF ->
  (forall e st, sstep segs (mkCfg msF mo) e st ->
     exists rsp mo', st = SNext (mkCfg (nret msF rsp) mo')
        /\ nstepL n (perase P mo) rsp (perase (allowL n rsp P) mo') e
        /\ lzframe (hideL n rsp H) (allowL n rsp P) mo' /\ hzero (hideL n rsp H) (nret msF rsp)
        /\ restrict (hideL n rsp H) (nret msF rsp) = nretL nodeL hideL n rsp H (restrict H msF))
  /\ (forall rsp moE' evs, nstepL n (perase P mo) rsp moE' evs ->
        exists mo', perase (allowL n rsp P) mo' = moE'
          /\ sstep segs (mkCfg msF mo) evs (SNext (mkCfg (nret msF rsp) mo'))
          /\ lzframe (hideL n rsp H) (allowL n rsp P) mo' /\ hzero (hideL n rsp H) (nret msF rsp)
          /\ restrict (hideL n rsp H) (nret msF rsp) = nretL nodeL hideL n rsp H (restrict H msF))
  /\ (exists rsp moE' evs, nstepL n (perase P mo) rsp moE' evs).
Proof.
  intros n H P msF mo x8 [Hsvc Hc Hnu Hs Hw] HF HZ. pose proof HF as [Hh Hm HI HC HA HO].
  split; [| split; [| exact Hw]].
  - intros e st Hst.
    destruct (sstep_svc_inv segs msF mo x8 e st Hsvc Hst)
      as [(eff & mo1 & ev & Hspec & [(mo'' & Hh' & -> & Hmat & ->) | [(Hh' & -> & Hmat & ->) | [(code & Hh' & _ & -> & ->) | (sig & Hk' & -> & ->)]]])
         | (Hspec & -> & ->)].
    + destruct (Hc _ _ _ Hspec) as (Hn & Hh1 & HI1 & HC1 & HA1 & Hm1 & HR1 & HCP & HZ1 & HS1 & HUV).
      destruct (materialize_after n H P eff _ mo1 HI1 HC1 HA1 HS1 HR1) as (mat' & Hmat' & HI2).
      rewrite Hmat' in Hmat. injection Hmat as <-.
      exists eff, (with_vm_backing (m_vm_lazy mo1) mat' mo1). split; [reflexivity|].
      rewrite perase_wvb_same. split; [exact Hn|]. split.
      { constructor; rewrite ?AsanAcct.m_halted_wvb, ?AsanAcct.m_vm_lazy_wvb, ?perase_wvb_same; try assumption.
        intros a Ha. destruct HS1 as [HS1|[_ HS1]]; [apply HO; apply HS1; exact Ha| destruct (HS1 a Ha) as [h|f]; [apply HO; exact h| exact f]]. }
      split; [exact HZ1|]. apply restrict_nretL; [exact HCP| exact HZ| exact HUV].
    + destruct (Hc _ _ _ Hspec) as (Hn & Hh1 & HI1 & HC1 & HA1 & Hm1 & HR1 & HCP & HZ1 & HS1 & HUV).
      destruct (materialize_after n H P eff _ mo1 HI1 HC1 HA1 HS1 HR1) as (mat' & Hmat' & _). rewrite Hmat' in Hmat. discriminate.
    + destruct (Hc _ _ _ Hspec) as (_ & Hh1 & _). congruence.
    + destruct (Hc _ _ _ Hspec) as (_ & Hh1 & _). rewrite (m_killed_of_m_halted_none _ Hh1) in Hk'. discriminate.
    + exfalso. exact (Hnu Hspec).
  - intros rsp moE' evs Hn.
    destruct (Hs _ _ _ Hn) as (eff' & mo1 & Hstrip & Hspec & HE).
    destruct (Hc _ _ _ Hspec) as (Hn' & Hh1 & HI1 & HC1 & HA1 & Hm1 & HR1 & HCP & HZ1 & HS1 & HUV).
    pose proof (hide_ok_strip _ _ _ _ _ Hstrip HS1) as HS1'. clear HS1. rename HS1' into HS1.
    rewrite (hideL_strip n rsp eff' H Hstrip), (allowL_strip n rsp eff' P Hstrip) in *.
    destruct (materialize_after n H P rsp _ mo1 HI1 HC1 HA1 HS1 HR1) as (mat' & Hmat' & HI2).
    exists (with_vm_backing (m_vm_lazy mo1) mat' mo1). rewrite perase_wvb_same. split; [exact HE|]. split.
    { rewrite <- nret_strip, <- Hstrip, nret_strip. unfold nret.
      apply (sstep_syscall segs msF mo x8 eff' mo1 _ evs Hh Hsvc Hspec Hh1 Hmat'). }
    split.
    { constructor; rewrite ?AsanAcct.m_halted_wvb, ?AsanAcct.m_vm_lazy_wvb, ?perase_wvb_same; try assumption.
      intros a Ha. destruct HS1 as [HS1|[_ HS1]]; [apply HO; apply HS1; exact Ha| destruct (HS1 a Ha) as [h|f]; [apply HO; exact h| exact f]]. }
    split. { rewrite <- (nret_strip msF rsp), <- Hstrip, nret_strip. exact HZ1. }
    apply restrict_nretL; [| exact HZ|].

    { change (eff_copies rsp) with (eff_copies (strip rsp)). rewrite <- Hstrip. exact HCP. }
    change (eff_zeros rsp) with (eff_zeros (strip rsp)). change (eff_unmaps rsp) with (eff_unmaps (strip rsp)).
    rewrite <- Hstrip. exact HUV.
Qed.

Record factsL_ns (n : nodeL) (H : word -> bool) (P : list word) (msF : machine_state) (mo : Model) (x8 : word) : Prop := mkFLns {
  fln_svc : ms_svc_pending msF = Some x8;
  fln_complete : forall eff mo1 evs, syscall_spec (sys_input segs msF x8) mo (Ok eff mo1 evs) ->
      ~ spurious_refusal_cfg ACFG (sys_input segs msF x8) mo eff ->
      nstepL n (perase P mo) eff (perase (allowL n eff P) mo1) evs
      /\ m_halted mo1 = None
      /\ MInv (ivl (allowL n eff P)) mo1
      /\ lazy_cover (hideL n eff H) (m_vm_lazy mo1) (ivl (allowL n eff P))
      /\ P_aligned (allowL n eff P)
      /\ minvL (perase (allowL n eff P) mo1)
      /\ AsanAcct.ranges_avoid H (syscall_effect_accesses eff)
      /\ eff_copies eff = []
      /\ hzero (hideL n eff H) (nret msF eff)
      /\ hide_ok n eff H (syscall_effect_accesses eff)
      /\ (forall x, H x = true -> hideL n eff H x = false ->
            zb x = true \/ zeros_cover (eff_zeros eff) x = true \/ zeros_cover (eff_unmaps eff) x = true);
  fln_nounmod : ~ syscall_spec (sys_input segs msF x8) mo Unmodeled;
  fln_sound : forall eff moE' evs, nstepL n (perase P mo) eff moE' evs ->
      exists eff' mo1, strip eff' = strip eff
        /\ (syscall_spec (sys_input segs msF x8) mo (Ok eff' mo1 evs)
            /\ ~ spurious_refusal_cfg ACFG (sys_input segs msF x8) mo eff')
        /\ perase (allowL n eff P) mo1 = moE';
  fln_progress : exists eff moE' evs, nstepL n (perase P mo) eff moE' evs;
  fln_nohalt : forall eff mo1 evs, syscall_spec (sys_input segs msF x8) mo (Ok eff mo1 evs) -> m_halted mo1 = None }.

#[using="Type"] Lemma factsL_ns_of_factsL : forall n H P msF mo x8,
  ~ In (bv_unsigned x8) alloc_mark_sysnos -> factsL n H P msF mo x8 -> factsL_ns n H P msF mo x8.
Proof.
  intros n H P msF mo x8 Hnin [Hsvc Hc Hnu Hs Hw]. constructor.
  - exact Hsvc.
  - intros eff mo1 evs Hspec _. exact (Hc _ _ _ Hspec).
  - exact Hnu.
  - intros eff moE' evs Hn. destruct (Hs _ _ _ Hn) as (eff' & mo1 & E & Hspec & HE).
    exists eff', mo1. split; [exact E|]. split; [| exact HE]. split; [exact Hspec|].
    apply acfg_nonspurious. rewrite in_sysno_sys_input. exact Hnin.
  - exact Hw.
  - intros eff mo1 evs Hspec. exact (proj1 (proj2 (Hc _ _ _ Hspec))).
Qed.

#[using="Type"] Lemma node_kitL_ns : forall n H P msF mo x8,
  factsL_ns n H P msF mo x8 -> lzframe H P mo -> hzero H msF ->
  (forall e st, sstep_cfg segs ACFG (mkCfg msF mo) e st ->
     exists rsp mo', st = SNext (mkCfg (nret msF rsp) mo')
        /\ nstepL n (perase P mo) rsp (perase (allowL n rsp P) mo') e
        /\ lzframe (hideL n rsp H) (allowL n rsp P) mo' /\ hzero (hideL n rsp H) (nret msF rsp)
        /\ restrict (hideL n rsp H) (nret msF rsp) = nretL nodeL hideL n rsp H (restrict H msF))
  /\ (forall rsp moE' evs, nstepL n (perase P mo) rsp moE' evs ->
        exists mo', perase (allowL n rsp P) mo' = moE'
          /\ sstep_cfg segs ACFG (mkCfg msF mo) evs (SNext (mkCfg (nret msF rsp) mo'))
          /\ lzframe (hideL n rsp H) (allowL n rsp P) mo' /\ hzero (hideL n rsp H) (nret msF rsp)
          /\ restrict (hideL n rsp H) (nret msF rsp) = nretL nodeL hideL n rsp H (restrict H msF))
  /\ (exists rsp moE' evs, nstepL n (perase P mo) rsp moE' evs).
Proof.
  intros n H P msF mo x8 [Hsvc Hc Hnu Hs Hw Hnh] HF HZ. pose proof HF as [Hh Hm HI HC HA HO].
  split; [| split; [| exact Hw]].
  - intros e st Hst.
    destruct (sstep_cfg_sys_inv segs ACFG msF mo x8 e st Hsvc Hst)
      as [(eff & mo1 & ev & Hspec & Hns & Hh' & Hmat) | [(eff & mo1 & ev & code & Hspec & Hh' & _ & _ & _)
         | [(eff & mo1 & ev & sig & Hspec & Hk' & _ & _) | (Hspec & _ & _)]]].
    + destruct (Hc _ _ _ Hspec Hns) as (Hn & Hh1 & HI1 & HC1 & HA1 & Hm1 & HR1 & HCP & HZ1 & HS1 & HUV).
      destruct (materialize_after n H P eff _ mo1 HI1 HC1 HA1 HS1 HR1) as (mat' & Hmat' & HI2).
      rewrite Hmat' in Hmat. cbv beta iota in Hmat. destruct Hmat as [-> ->].
      exists eff, (with_vm_backing (m_vm_lazy mo1) mat' mo1). split; [reflexivity|].
      rewrite perase_wvb_same. split; [exact Hn|]. split.
      { constructor; rewrite ?AsanAcct.m_halted_wvb, ?AsanAcct.m_vm_lazy_wvb, ?perase_wvb_same; try assumption.
        intros a Ha. destruct HS1 as [HS1|[_ HS1]]; [apply HO; apply HS1; exact Ha| destruct (HS1 a Ha) as [h|f]; [apply HO; exact h| exact f]]. }
      split; [exact HZ1|]. apply restrict_nretL; [exact HCP| exact HZ| exact HUV].
    + rewrite (Hnh _ _ _ Hspec) in Hh'. discriminate.
    + rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hspec)) in Hk'. discriminate.
    + exfalso. exact (Hnu Hspec).
  - intros rsp moE' evs Hn.
    destruct (Hs _ _ _ Hn) as (eff' & mo1 & Hstrip & [Hspec Hns] & HE).
    destruct (Hc _ _ _ Hspec Hns) as (Hn' & Hh1 & HI1 & HC1 & HA1 & Hm1 & HR1 & HCP & HZ1 & HS1 & HUV).
    pose proof (hide_ok_strip _ _ _ _ _ Hstrip HS1) as HS1'. clear HS1. rename HS1' into HS1.
    rewrite (hideL_strip n rsp eff' H Hstrip), (allowL_strip n rsp eff' P Hstrip) in *.
    destruct (materialize_after n H P rsp _ mo1 HI1 HC1 HA1 HS1 HR1) as (mat' & Hmat' & HI2).
    exists (with_vm_backing (m_vm_lazy mo1) mat' mo1). rewrite perase_wvb_same. split; [exact HE|]. split.
    { rewrite <- nret_strip, <- Hstrip, nret_strip. unfold nret.
      apply (sstep_cfg_syscall segs ACFG msF mo x8 eff' mo1 _ evs Hh Hsvc Hspec Hns Hh1 Hmat'). }
    split.
    { constructor; rewrite ?AsanAcct.m_halted_wvb, ?AsanAcct.m_vm_lazy_wvb, ?perase_wvb_same; try assumption.
      intros a Ha. destruct HS1 as [HS1|[_ HS1]]; [apply HO; apply HS1; exact Ha| destruct (HS1 a Ha) as [h|f]; [apply HO; exact h| exact f]]. }
    split. { rewrite <- (nret_strip msF rsp), <- Hstrip, nret_strip. exact HZ1. }
    apply restrict_nretL; [| exact HZ|].
    { change (eff_copies rsp) with (eff_copies (strip rsp)). rewrite <- Hstrip. exact HCP. }
    change (eff_zeros rsp) with (eff_zeros (strip rsp)). change (eff_unmaps rsp) with (eff_unmaps (strip rsp)).
    rewrite <- Hstrip. exact HUV.
Qed.

End Kit.

Lemma strip_vm_perase : forall P mo, strip_vm (perase P mo) = strip_vm mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma strip_vm_with_fds : forall f mo, strip_vm (with_fds f mo) = with_fds f (strip_vm mo).
Proof. intros f [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma strip_vm_with_fs : forall f mo, strip_vm (with_fs f mo) = with_fs f (strip_vm mo).
Proof. intros f [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma strip_vm_with_tid : forall t mo, strip_vm (with_tid t mo) = with_tid t (strip_vm mo).
Proof. intros t [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma strip_vm_with_halted : forall c mo, strip_vm (with_halted c mo) = with_halted c (strip_vm mo).
Proof. intros c [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma strip_vm_with_vmmaps : forall h mo, strip_vm (with_vmmaps h mo) = with_vmmaps h (strip_vm mo).
Proof. intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_fds_strip_vm : forall mo, m_fds (strip_vm mo) = m_fds mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_fs_strip_vm : forall mo, m_fs (strip_vm mo) = m_fs mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_tid_strip_vm : forall mo, m_tid (strip_vm mo) = m_tid mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_vmmaps_strip_vm : forall mo, m_vmmaps (strip_vm mo) = m_vmmaps mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_halted_strip_vm : forall mo, m_halted (strip_vm mo) = m_halted mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma minvL_perase : forall P mo, minvL (perase P mo) <-> minvL mo.
Proof.
  intros P mo. unfold minvL. rewrite strip_vm_perase.
  unfold lazy_in_maps, BackingAlgebra.model_ivs_wf. rewrite m_vm_lazy_perase, m_vmmaps_perase. tauto.
Qed.

Lemma minvL_fdframe : forall mo mo',
  m_vm mo' = m_vm mo -> m_vmmaps mo' = m_vmmaps mo -> minv (strip_vm mo') -> minvL mo -> minvL mo'.
Proof.
  intros mo mo' Ev Eh Hm (_ & HL & HW & HS). split; [exact Hm|].
  unfold lazy_in_maps, BackingAlgebra.model_ivs_wf in *.
  replace (m_vm_lazy mo') with (m_vm_lazy mo) by (unfold m_vm_lazy; rewrite Ev; reflexivity).
  rewrite Eh. split; [exact HL|]. split; [exact HW| exact HS].
Qed.

Lemma MInv_fdframe : forall A mo mo',
  m_vm mo' = m_vm mo -> m_vmmaps mo' = m_vmmaps mo -> MInv A mo -> MInv A mo'.
Proof.
  intros A mo mo' Ev Eh HI. eapply AsanAcct.MInv_transport; [exact HI| | |].
  - unfold m_vm_materialized. rewrite Ev. reflexivity.
  - unfold m_vm_lazy. rewrite Ev. reflexivity.
  - unfold AsanAcct.eager_used. unfold m_vm_lazy. rewrite Ev, Eh. exact (AsanAcct.minv_budget _ _ HI).
Qed.

Lemma nret_mem_nomem : forall ms r, ms_mem (nret ms (mkEffect r [] [])) = ms_mem ms.
Proof. intros ms r. unfold nret, advance_past_svc, apply_effect. cbn -[set_reg]. rewrite ms_mem_set_reg. reflexivity. Qed.

Lemma hzero_nret_nomem : forall H ms r, hzero H ms -> hzero H (nret ms (mkEffect r [] [])).
Proof. intros H ms r HZ a Ha. rewrite nret_mem_nomem. exact (HZ a Ha). Qed.

Lemma hzero_nret_strip : forall H ms e e', strip e' = strip e -> hzero H (nret ms e) -> hzero H (nret ms e').
Proof. intros H ms e e' E HZ. rewrite <- nret_strip, E, nret_strip. exact HZ. Qed.

Lemma accesses_eff0 : forall r, syscall_effect_accesses (mkEffect r [] []) = [].
Proof. reflexivity. Qed.

Lemma apply_writes_hidden : forall H ws m x,
  AsanAcct.ranges_avoid H (write_accesses ws) -> H x = true -> apply_writes m ws x = m x.
Proof.
  intros H ws. induction ws as [|[a bs] ws IH]; intros m x HR Hx; cbn [apply_writes]; [reflexivity|].
  cbn [write_accesses] in HR.
  rewrite (IH _ x (fun a' n' Hin => HR a' n' (or_intror Hin)) Hx).
  apply (AsanAcct.write_to_mem_hidden H); [| exact Hx]. exact (HR a (length bs) (or_introl eq_refl)).
Qed.

Lemma nret_mem_writes : forall ms r ws x,
  ms_mem (nret ms (mkEffect r ws [])) x = apply_writes (ms_mem ms) ws x.
Proof. intros ms r ws x. unfold nret, advance_past_svc, apply_effect. cbn -[set_reg apply_writes]. rewrite ms_mem_set_reg. reflexivity. Qed.

Lemma hzero_nret_writes : forall H ms r ws,
  AsanAcct.ranges_avoid H (write_accesses ws) -> hzero H ms -> hzero H (nret ms (mkEffect r ws [])).
Proof. intros H ms r ws HR HZ a Ha. rewrite nret_mem_writes, (apply_writes_hidden H ws _ a HR Ha). exact (HZ a Ha). Qed.

Lemma ranges_avoid_delivered : forall H (buf : Z) bs,
  0 <= buf -> (forall i, 0 <= i < Z.of_nat (length bs) -> H (wa (buf + i)) = false) ->
  AsanAcct.ranges_avoid H (write_accesses (delivered_writes (Z_to_bv 64 buf) bs)).
Proof.
  intros H buf bs Hb HV. destruct bs as [|b bs]; cbn [delivered_writes write_accesses].
  - apply AsanAcct.ranges_avoid_nil.
  - apply AsanAcct.ranges_avoid_cons; [| apply AsanAcct.ranges_avoid_nil].
    intros k Hk. unfold AsanAcct.woff. specialize (HV (Z.of_nat k) ltac:(cbn [length] in *; lia)). unfold wa in HV.
    rewrite <- HV. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_l. reflexivity.
Qed.

Lemma woff_wa : forall a k, AsanAcct.woff a k = wa (bv_unsigned a + Z.of_nat k).
Proof. intros a k. reflexivity. Qed.

Lemma woff_add16 : forall (a : word) k, AsanAcct.woff (a + 16)%bv k = AsanAcct.woff a (16 + k).
Proof.
  intros a k. unfold AsanAcct.woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  rewrite bv_wrap_add_idemp_l. f_equal. change (bv_unsigned (16 : word)) with 16%Z. lia.
Qed.

Lemma ranges_avoid_copy_iovecs : forall H mp k a,
  (forall j, (j < 16 * k)%nat -> H (AsanAcct.woff a j) = false) ->
  AsanAcct.ranges_avoid H (copy_iovecs_accesses mp a k).
Proof.
  intros H mp k. induction k as [|k IH]; intros a HV; cbn [copy_iovecs_accesses].
  - apply AsanAcct.ranges_avoid_nil.
  - apply AsanAcct.ranges_avoid_cons.
    + intros j Hj. apply HV. lia.
    + destruct (read_iovec_entry mp a); try apply AsanAcct.ranges_avoid_nil.
      apply IH. intros j Hj. rewrite woff_add16. apply HV. lia.
Qed.

Lemma ranges_avoid_import_iovecs : forall H mp a n,
  (forall j, (j < 16 * word_to_nat n)%nat -> H (AsanAcct.woff a j) = false) ->
  AsanAcct.ranges_avoid H (import_iovecs_accesses mp a n).
Proof.
  intros H mp a n HV. unfold import_iovecs_accesses.
  destruct (bv_eqb n (Z_to_bv 64 1)) eqn:E1.
  { apply bv_eqb_eq in E1. subst n. destruct (negb (access_okb a 16)); [apply AsanAcct.ranges_avoid_nil|].
    apply AsanAcct.ranges_avoid_cons; [| apply AsanAcct.ranges_avoid_nil]. intros j Hj. apply HV.
    unfold word_to_nat. rewrite unsigned_lit64 by lia. cbn. lia. }
  destruct (bv_eqb n (Z_to_bv 64 0)); [apply AsanAcct.ranges_avoid_nil|].
  destruct (IOV_MAX <? bv_unsigned n)%Z; [apply AsanAcct.ranges_avoid_nil|].
  destruct (negb (access_okb a (16 * bv_unsigned n))); [apply AsanAcct.ranges_avoid_nil|].
  apply ranges_avoid_copy_iovecs. exact HV.
Qed.

Section PerKind.
Variable segs : list Segment.
Variable H : word -> bool.
Variable P : list word.
Variable msF : machine_state.
Variable mo : Model.
Hypothesis HF : lzframe segs minvL H P mo.
Hypothesis HZ : hzero H msF.

Let Hh : m_halted mo = None := lf_halt _ _ _ _ _ HF.
Let HO : H_off_segments segs H := lf_off _ _ _ _ _ HF.
Let HI : MInv (ivl P) mo := lf_MInv _ _ _ _ _ HF.
Let HC : lazy_cover H (m_vm_lazy mo) (ivl P) := lf_cover _ _ _ _ _ HF.
Let HA : P_aligned P := lf_al _ _ _ _ _ HF.

#[using="segs H P HF"] Lemma HML : minvL mo.
Proof. apply (minvL_perase P). exact (lf_minv _ _ _ _ _ HF). Qed.

#[using="segs H P HF"] Lemma HM0 : minv (strip_vm mo).
Proof. exact (proj1 HML). Qed.

#[using="segs HF Hh HI HC HA"] Lemma fdkind_frame : forall n eff mo1,
  hideL n eff H = H -> allowL n eff P = P ->
  m_vm mo1 = m_vm mo -> m_vmmaps mo1 = m_vmmaps mo -> m_halted mo1 = m_halted mo ->
  minv (strip_vm mo1) ->
  AsanAcct.ranges_avoid H (syscall_effect_accesses eff) -> eff_copies eff = [] ->
  hzero H (nret msF eff) ->
  m_halted mo1 = None
  /\ MInv (ivl (allowL n eff P)) mo1
  /\ lazy_cover (hideL n eff H) (m_vm_lazy mo1) (ivl (allowL n eff P))
  /\ P_aligned (allowL n eff P)
  /\ minvL (perase (allowL n eff P) mo1)
  /\ AsanAcct.ranges_avoid H (syscall_effect_accesses eff)
  /\ eff_copies eff = []
  /\ hzero (hideL n eff H) (nret msF eff)
  /\ hide_ok segs n eff H (syscall_effect_accesses eff)
  /\ (forall x, H x = true -> hideL n eff H x = false ->
        zb x = true \/ zeros_cover (eff_zeros eff) x = true \/ zeros_cover (eff_unmaps eff) x = true).
Proof.
  intros n eff mo1 EH EP Ev Eh Ehl Hm HR HCP HZ1. rewrite EH, EP.
  split; [rewrite Ehl; exact Hh|]. split; [eapply MInv_fdframe; eauto|].
  split; [unfold m_vm_lazy; rewrite Ev; exact HC|]. split; [exact HA|].
  split; [apply minvL_perase; eapply minvL_fdframe; eauto using HML|].
  split; [exact HR|]. split; [exact HCP|]. split; [exact HZ1|]. split; [apply hide_ok_mono; intros a Ha; rewrite EH in Ha; exact Ha|].
  intros x Hx Hx'. congruence.
Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma close_factsL : forall fd,
  at_node segs (NClose fd) (restrict H msF) -> factsL segs (LNode (NClose fd)) H P msF mo (Z_to_bv 64 57).
Proof.
  intros fd Hat. apply (at_node_unrestrict segs H HO) in Hat. destruct Hat as (Hsvc & Hfd & Ha0).
  pose proof HM0 as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS). rewrite !m_fds_strip_vm, ?m_fs_strip_vm, ?m_tid_strip_vm in *.
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 57)) mo o <->
                        close_spec (Z_to_bv 64 fd) (sys_input segs msF (Z_to_bv 64 57)) mo o).
  { intros o. rewrite (syscall_spec_57 _ _ _ (sysno_of segs msF _ 57 ltac:(lia) eq_refl)).
    rewrite in_a0_si, Ha0, fd32_small by lia. reflexivity. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  -
    set (mo1 := with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
    assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 57)) mo o <->
              o = Ok (mkEffect (Z_to_bv 64 0) [] []) mo1 []).
    { intros o. rewrite D. apply (close_outcome _ _ _ _ _ Hlk). }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL nstep allowL]. rewrite m_fds_perase, Hlk. subst mo1. rewrite perase_with_fds. repeat split; try lia; reflexivity.
      * apply fdkind_frame; try reflexivity.
        -- subst mo1. rewrite strip_vm_with_fds. rewrite <- m_fds_strip_vm. apply minv_remove; [exact HM0| lia].
        -- rewrite accesses_eff0. apply AsanAcct.ranges_avoid_nil.
        -- apply hzero_nret_nomem. exact HZ.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. destruct Hn as (-> & _ & Hn). rewrite m_fds_perase, Hlk in Hn. destruct Hn as [Hs ->].
      eexists (mkEffect (Z_to_bv 64 0) [] []), mo1. split; [rewrite Hs; reflexivity|]. split; [apply OUT; reflexivity|].
      cbn [allowL]. subst mo1. rewrite perase_with_fds. reflexivity.
    + exists (eff0 (Z_to_bv 64 0)), (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) (perase P mo)), [].
      cbn [nstepL nstep]. rewrite m_fds_perase, Hlk. repeat split; try lia; reflexivity.
  -
    assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 57)) mo o <->
              o = Ok (mkEffect (errno_ret EBADF) [] []) mo []).
    { intros o. rewrite D. apply (close_ebadf_outcome _ _ _ _ Hlk). }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL nstep allowL]. rewrite m_fds_perase, Hlk. repeat split; try lia; reflexivity.
      * apply fdkind_frame; try reflexivity.
        -- exact HM0.
        -- rewrite accesses_eff0. apply AsanAcct.ranges_avoid_nil.
        -- apply hzero_nret_nomem. exact HZ.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. destruct Hn as (-> & _ & Hn). rewrite m_fds_perase, Hlk in Hn. destruct Hn as [Hs ->].
      eexists (mkEffect (errno_ret EBADF) [] []), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT; reflexivity|]. reflexivity.
    + exists (efferr EBADF), (perase P mo), []. cbn [nstepL nstep]. rewrite m_fds_perase, Hlk. repeat split; try lia; reflexivity.
Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma ioctl_factsL : forall fd req,
  at_node segs (NIoctl fd req) (restrict H msF) -> factsL segs (LNode (NIoctl fd req)) H P msF mo (Z_to_bv 64 29).
Proof.
  intros fd req Hat. apply (at_node_unrestrict segs H HO) in Hat. destruct Hat as (Hsvc & Hfd & -> & Ha0 & Ha1).
  pose proof HM0 as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS). rewrite !m_fds_strip_vm, ?m_fs_strip_vm, ?m_tid_strip_vm in *.
  assert (He : exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)).
  { assert (fd = 0 \/ fd = 1 \/ fd = 2) as [-> | [-> | ->]] by lia; eexists; eassumption. }
  destruct He as [c Hlk].
  assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 29)) mo o <->
            o = Ok (mkEffect (errno_ret ENOTTY) [] []) mo []).
  { intros o. rewrite (syscall_spec_29 _ _ _ (sysno_of segs msF _ 29 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, Ha0, Ha1, fd32_small by lia.

    apply (ioctl_tty_outcome _ _ _ _ _ _ Hlk tty_only_TIOCGWINSZ); [intros rd wr; discriminate | discriminate]. }
  split.
  - exact Hsvc.
  - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
    + cbn [nstepL nstep allowL]. repeat split; reflexivity.
    + apply fdkind_frame; try reflexivity; [exact HM0| rewrite accesses_eff0; apply AsanAcct.ranges_avoid_nil| apply hzero_nret_nomem; exact HZ].
  - intros Hs. apply OUT in Hs. discriminate.
  - intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. destruct Hn as (-> & Hs & ->).
    eexists (mkEffect (errno_ret ENOTTY) [] []), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT; reflexivity| reflexivity].
  - exists (efferr ENOTTY), (perase P mo), []. cbn [nstepL nstep]. repeat split; reflexivity.
Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma set_tid_factsL :
  at_node segs NSetTid (restrict H msF) -> factsL segs (LNode NSetTid) H P msF mo (Z_to_bv 64 96).
Proof.
  intros Hat. apply (at_node_unrestrict segs H HO) in Hat. cbn [at_node] in Hat. rename Hat into Hsvc.
  pose proof HM0 as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS). rewrite !m_fds_strip_vm, ?m_fs_strip_vm, ?m_tid_strip_vm in *.
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 96)) mo o <->
                        set_tid_address_spec (sys_input segs msF (Z_to_bv 64 96)) mo o).
  { intros o. apply syscall_spec_96. apply (sysno_of segs msF _ 96 ltac:(lia) eq_refl). }
  destruct (m_tid mo) as [t0|] eqn:Htid.
  - assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 96)) mo o <-> o = Ok (mkEffect t0 [] []) mo []).
    { intros o. rewrite D. apply (set_tid_known_outcome _ _ _ _ Htid). }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL nstep allowL]. rewrite m_tid_perase, Htid. split; [reflexivity|]. exists t0. repeat split; reflexivity.
      * apply fdkind_frame; try reflexivity; [exact HM0| rewrite accesses_eff0; apply AsanAcct.ranges_avoid_nil| apply hzero_nret_nomem; exact HZ].
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. destruct Hn as (-> & t & Hs & Hn). rewrite m_tid_perase, Htid in Hn. destruct Hn as [-> ->].
      eexists (mkEffect t0 [] []), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT; reflexivity| reflexivity].
    + exists (eff0 t0), (perase P mo), []. cbn [nstepL nstep]. rewrite m_tid_perase, Htid. split; [reflexivity|]. exists t0. repeat split; reflexivity.
  - assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 96)) mo o <->
              exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE) /\ o = Ok (mkEffect t [] []) (with_tid t mo) []).
    { intros o. rewrite D. apply (set_tid_fresh_outcome _ _ _ Htid). }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as (t & Ht & Hs). apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL nstep allowL]. rewrite m_tid_perase, Htid, perase_with_tid. split; [reflexivity|]. exists t. repeat split; try reflexivity; lia.
      * apply fdkind_frame; try reflexivity.
        -- rewrite strip_vm_with_tid. apply minv_with_tid; [exact HM0| exact Ht].
        -- rewrite accesses_eff0; apply AsanAcct.ranges_avoid_nil.
        -- apply hzero_nret_nomem; exact HZ.
    + intros Hs. apply OUT in Hs. destruct Hs as (t & _ & Hs). discriminate.
    + intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. destruct Hn as (-> & t & Hs & Hn). rewrite m_tid_perase, Htid in Hn. destruct Hn as [Ht ->].
      eexists (mkEffect t [] []), (with_tid t mo). split; [rewrite Hs; reflexivity|].
      split; [apply OUT; exists t; split; [exact Ht|reflexivity]|]. cbn [allowL]. rewrite perase_with_tid. reflexivity.
    + exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) (perase P mo)), []. cbn [nstepL nstep]. rewrite m_tid_perase, Htid.
      split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|]. split; [| reflexivity].
      rewrite unsigned_lit64 by lia. unfold PID_MAX_ENVELOPE. lia.
Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma read_factsL : forall fd buf count,
  at_node segs (NRead fd buf count) (restrict H msF) -> factsL segs (LNode (NRead fd buf count)) H P msF mo (Z_to_bv 64 63).
Proof.
  intros fd buf count HatR. pose proof (at_node_unrestrict segs H HO _ _ HatR) as Hat.
  destruct Hat as (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hbc & Hwr).
  destruct HatR as (_ & _ & _ & _ & _ & _ & _ & HwrR). rewrite AsanAcct.restrict_mem in HwrR.
  pose proof HM0 as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS). rewrite !m_fds_strip_vm, ?m_fs_strip_vm, ?m_tid_strip_vm in *.
  pose proof Hwr as (Hb0 & _ & _).
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 63)) mo o <->
                        read_spec (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) (sys_input segs msF (Z_to_bv 64 63)) mo o).
  { intros o. rewrite (syscall_spec_63 _ _ _ (sysno_of segs msF _ 63 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2, fd32_small by lia. reflexivity. }
  assert (Hcnt : bv_unsigned (Z_to_bv 64 count) = count) by (apply unsigned_lit64; lia).
  assert (ACC : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { apply access_okb_of_le; [lia|]. rewrite unsigned_lit64, Hcnt by lia. lia. }

  assert (DET : forall E, (forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 63)) mo o <-> o = Ok (mkEffect E [] []) mo []) ->
            (forall eff mo' evs, nstep (NRead fd buf count) (perase P mo) eff mo' evs <-> (evs = [] /\ strip eff = mkEffect E [] [] /\ mo' = perase P mo)) ->
            factsL segs (LNode (NRead fd buf count)) H P msF mo (Z_to_bv 64 63)).
  { intros E OUT NST. split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL allowL]. apply NST. repeat split; reflexivity.
      * apply fdkind_frame; try reflexivity; [exact HM0| rewrite accesses_eff0; apply AsanAcct.ranges_avoid_nil| apply hzero_nret_nomem; exact HZ].
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff moE' evs Hn. cbn [nstepL] in Hn. apply NST in Hn. destruct Hn as (-> & Hs & ->).
      eexists (mkEffect E [] []), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT; reflexivity| reflexivity].
    + exists (mkEffect E [] []), (perase P mo), ([] : list event). cbn [nstepL]. apply NST. repeat split; reflexivity. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  2:{
    apply (DET (errno_ret EBADF)).
    - intros o. rewrite D. apply (read_ebadf_outcome _ _ _ _ _ _ Hlk).
    - intros eff mo' evs. cbn [nstep]. rewrite m_fds_perase, Hlk. unfold efferr, eff0. tauto. }
  destruct e as [ch | p off | p off | p off | p off | | sk | pid wr | dnr dnw | ].
  9-10: exfalso; exact (MK _ _ Hlk).
  -   exfalso. apply MC in Hlk. rewrite unsigned_lit64 in Hlk by lia. lia.
  -
    destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
    set (bs := file_read data off (Z_to_bv 64 count)).
    assert (Hbs : (Z.of_nat (length bs) <= count)).
    { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as HL. subst bs. unfold word_to_nat in HL. rewrite Hcnt in HL. lia. }
    assert (Hclamp : Z_to_bv 64 (rw_count_clamp (Z_to_bv 64 count)) = Z_to_bv 64 count).
    { rewrite rw_count_clamp_small by (rewrite Hcnt; unfold MAX_RW_COUNT; lia). apply Z_to_bv_bv_unsigned. }
    destruct (read_bytes_map_wr_at segs (ms_mem msF) buf count (len_word bs) Hwr
                ltac:(rewrite len_word_unsigned by (unfold two_pow_64; lia); lia) ltac:(lia) ltac:(lia)) as [w Hw].
    set (mo1 := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo).
    assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 63)) mo o <->
              o = Ok (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []) mo1 []).
    { intros o. rewrite D.
      pose proof (read_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count)
                    (sys_input segs msF (Z_to_bv 64 63)) mo o p off data w Hlk ACC Hfs) as R.
      cbv zeta in R. rewrite Hclamp in R. apply R. rewrite in_wmem_si. exact Hw. }
    assert (HRA : AsanAcct.ranges_avoid H (write_accesses (delivered_writes (Z_to_bv 64 buf) bs))).
    { apply ranges_avoid_delivered; [lia|]. intros i Hi. apply (wr_at_visible segs H HO _ _ _ HwrR). lia. }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL nstep allowL]. rewrite m_fds_perase, m_fs_perase, Hlk, Hfs. subst mo1. rewrite perase_with_fds. repeat split; reflexivity.
      * apply fdkind_frame; try reflexivity.
        -- subst mo1. rewrite strip_vm_with_fds, <- m_fds_strip_vm. eapply minv_update_file; [exact HM0|]. rewrite m_fds_strip_vm. exact Hlk.
        -- exact HRA.
        -- apply hzero_nret_writes; [exact HRA| exact HZ].
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. destruct Hn as [-> Hn]. rewrite m_fds_perase, m_fs_perase, Hlk, Hfs in Hn. destruct Hn as [Hs ->].
      eexists (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []), mo1. split; [rewrite Hs; reflexivity|].
      split; [apply OUT; reflexivity|]. cbn [allowL]. subst mo1. rewrite perase_with_fds. reflexivity.
    + eexists (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []), _, [].
      cbn [nstepL nstep]. rewrite m_fds_perase, m_fs_perase, Hlk, Hfs. repeat split; reflexivity.
  -
    apply (DET (errno_ret EBADF)).
    + intros o. rewrite D. apply (read_wronly_outcome _ _ _ _ _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite m_fds_perase, Hlk. unfold efferr, eff0. tauto.
  -   exfalso. exact (MK _ _ Hlk).
  -   exfalso. exact (MK _ _ Hlk).
  -
    apply (DET (errno_ret EISDIR)).
    + intros o. rewrite D. apply (read_dir_outcome _ _ _ _ _ _ Hlk ACC).
    + intros eff mo' evs. cbn [nstep]. rewrite m_fds_perase, Hlk. unfold efferr, eff0. tauto.
  - exfalso. exact (MK _ _ Hlk).
  - exfalso. exact (MK _ _ Hlk).
Qed.

#[using="Type"] Lemma cstr_access_len_le : forall path mp a fuel,
  bytes_in mp a (path ++ [Z_to_bv 8 0]) -> (cstr_access_len_aux mp (wa a) fuel <= length path + 1)%nat.
Proof.
  induction path as [|c path IH]; intros mp a fuel Hin; destruct fuel as [|fuel]; cbn [cstr_access_len_aux app length]; try lia.
  - apply bytes_in_cons in Hin as [E _]. rewrite E. unfold bv_eqb. rewrite Z.eqb_refl. lia.
  - apply bytes_in_cons in Hin as [E Hin]. rewrite E. destruct (bv_eqb c (Z_to_bv 8 0)); [lia|].
    fold (path ++ [Z_to_bv 8 0]) in Hin. rewrite wa_succ. specialize (IH mp (a + 1)%Z fuel Hin). lia.
Qed.

#[using="Type"] Lemma accesses_with_copyins : forall R r, syscall_effect_accesses (with_copyins R (mkEffect r [] [])) = R.
Proof. intros R r. unfold syscall_effect_accesses, with_copyins. cbn. apply app_nil_r. Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma open_factsL : forall path,
  at_node segs (NOpen path) (restrict H msF) -> factsL segs (LNode (NOpen path)) H P msF mo (Z_to_bv 64 56).
Proof.
  intros path HatR. pose proof (at_node_unrestrict segs H HO _ _ HatR) as Hat.
  destruct Hat as (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hrom & Hpath).
  destruct HatR as (_ & _ & _ & _ & _ & _ & HpathR). unfold areg in HpathR. rewrite AsanAcct.restrict_mem, AsanAcct.restrict_regs in HpathR. fold (areg msF 11) in HpathR.
  pose proof HM0 as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS). rewrite !m_fds_strip_vm, ?m_fs_strip_vm, ?m_tid_strip_vm in *.
  set (i := sys_input segs msF (Z_to_bv 64 56)) in *.
  set (pathp := areg msF 11) in *. set (flags := areg msF 12) in *.
  assert (Hmfl : modeled_open_flags flags = true).
  { unfold modeled_open_flags. rewrite Hfl. reflexivity. }
  assert (D : forall o, syscall_spec i mo o <-> openat_spec AT_FDCWD32 pathp flags i mo o).
  { intros o. subst i. rewrite (syscall_spec_56 _ _ _ (sysno_of segs msF _ 56 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0. unfold AT_FDCWD32, AT_FDCWD. reflexivity. }
  assert (Hin : bytes_in (in_mem i) (bv_unsigned pathp) (path ++ [Z_to_bv 8 0])).
  { subst i. rewrite in_mem_si. eapply bytes_at_in; eassumption. }
  pose proof (bytes_at_bound _ _ _ _ Hpath) as Hbnd. rewrite length_app in Hbnd. cbn [length] in Hbnd.
  assert (Hpw : wa (bv_unsigned pathp) = pathp) by apply wa_unsigned_id.

  assert (HRA : AsanAcct.ranges_avoid H (open_reads i pathp)).
  { unfold open_reads. apply AsanAcct.ranges_avoid_cons; [| apply AsanAcct.ranges_avoid_nil].
    intros k Hk. rewrite <- Hpw in Hk. pose proof (cstr_access_len_le path (in_mem i) (bv_unsigned pathp) path_max Hin) as HL.
    unfold AsanAcct.woff. apply (bytes_at_visible segs H HO _ _ _ HpathR). rewrite length_app. cbn [length]. lia. }

  assert (DETC : forall E,
            (forall o, syscall_spec i mo o <-> o = Ok (with_copyins (open_reads i pathp) (mkEffect E [] [])) mo []) ->
            (forall eff mo' evs, nstep (NOpen path) (perase P mo) eff mo' evs <-> (evs = [] /\ strip eff = mkEffect E [] [] /\ mo' = perase P mo)) ->
            factsL segs (LNode (NOpen path)) H P msF mo (Z_to_bv 64 56)).
  { intros E OUT NST. split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL allowL]. apply NST. rewrite strip_with_copyins. repeat split; reflexivity.
      * apply fdkind_frame; try reflexivity; [exact HM0| rewrite accesses_with_copyins; exact HRA|].
        apply (hzero_nret_strip H msF (mkEffect E [] [])); [rewrite strip_with_copyins; reflexivity|]. apply hzero_nret_nomem; exact HZ.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff moE' evs Hn. cbn [nstepL] in Hn. apply NST in Hn. destruct Hn as (-> & Hs & ->).
      eexists (with_copyins (open_reads i pathp) (mkEffect E [] [])), mo. split; [rewrite strip_with_copyins, Hs; reflexivity|].
      split; [apply OUT; reflexivity| reflexivity].
    + exists (mkEffect E [] []), (perase P mo), ([] : list event). cbn [nstepL]. apply NST. repeat split; reflexivity. }
  assert (OPENC : forall ent,
            (forall o, syscall_spec i mo o <-> open_out (open_reads i pathp) mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) o) ->
            (forall moX eff mo' evs, m_fds moX = m_fds mo -> m_fs moX = m_fs mo ->
               nstep (NOpen path) moX eff mo' evs <-> (evs = [] /\ open_result moX ent eff mo')) ->
            match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
            factsL segs (LNode (NOpen path)) H P msF mo (Z_to_bv 64 56)).
  { intros ent OUT NST Hent. split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as [(e & He & Hs)|(Hfree & Hs)]; apply Ok_inj in Hs as (-> & -> & ->).
      * split. { cbn [nstepL allowL]. apply NST; [apply m_fds_perase| apply m_fs_perase|]. split; [reflexivity|]. left. exists e.
                 rewrite strip_with_copyins. repeat split; auto. }
        apply fdkind_frame; try reflexivity; [exact HM0| rewrite accesses_with_copyins; exact HRA|].
        apply (hzero_nret_strip H msF (mkEffect (errno_ret e) [] [])); [rewrite strip_with_copyins; reflexivity|]. apply hzero_nret_nomem; exact HZ.
      * split. { cbn [nstepL allowL]. apply NST; [apply m_fds_perase| apply m_fs_perase|]. split; [reflexivity|]. right.
                 rewrite m_fds_perase, strip_with_copyins, perase_with_fds. repeat split; auto. }
        apply fdkind_frame; try reflexivity.
        -- rewrite strip_vm_with_fds, <- m_fds_strip_vm. apply minv_open_insert; rewrite ?m_fds_strip_vm, ?m_fs_strip_vm; [exact HM0| exact Hfree| exact Hent].
        -- rewrite accesses_with_copyins; exact HRA.
        -- apply (hzero_nret_strip H msF (mkEffect (alloc_fd (m_fds mo)) [] [])); [rewrite strip_with_copyins; reflexivity|]. apply hzero_nret_nomem; exact HZ.
    + intros Hs. apply OUT in Hs. destruct Hs as [(e & _ & Hs)|(_ & Hs)]; discriminate.
    + intros eff moE' evs Hn. cbn [nstepL] in Hn. apply NST in Hn; [| apply m_fds_perase| apply m_fs_perase].
      destruct Hn as [-> [(e & He & Hs & ->)|(Hfree & Hs & ->)]].
      * eexists (with_copyins (open_reads i pathp) (mkEffect (errno_ret e) [] [])), mo. split; [rewrite strip_with_copyins, Hs; reflexivity|].
        split; [apply OUT; left; exists e; split; [exact He|reflexivity]| reflexivity].
      * rewrite m_fds_perase in Hfree, Hs |- *.
        eexists (with_copyins (open_reads i pathp) (mkEffect (alloc_fd (m_fds mo)) [] [])), _. split; [rewrite strip_with_copyins, Hs; reflexivity|].
        split; [apply OUT; right; split; [exact Hfree|reflexivity]|]. cbn [allowL]. rewrite perase_with_fds. reflexivity.
    + exists (efferr ENOMEM), (perase P mo), ([] : list event). cbn [nstepL]. apply NST; [apply m_fds_perase| apply m_fs_perase|].
      split; [reflexivity|]. left. exists ENOMEM. split; [cbn; tauto|]. split; reflexivity. }
  destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
  {
    assert (Hc : read_cstr (in_mem i) pathp = CstrTooLong).
    { unfold read_cstr. rewrite <- Hpw. apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
      apply bytes_in_app in Hin as [H1 _]. exact H1. }
    apply (DETC (errno_ret ENAMETOOLONG)).
    - intros o. rewrite D. apply (openat_toolong_outcome _ _ _ _ _ Hmfl _ Hc).
    - intros eff mo' evs. cbn [nstep]. rewrite (proj2 (Nat.leb_le _ _) Hlong). unfold efferr, eff0. tauto. }
  assert (Hleb : (path_max <=? length path)%nat = false) by (apply Nat.leb_gt; lia).
  assert (Hc : read_cstr (in_mem i) pathp = CstrOk path).
  { unfold read_cstr. rewrite <- Hpw. apply read_cstr_aux_bytes_in; [exact Hshort|exact Hnz|exact Hin]. }
  destruct path as [|c path'].
  {
    apply (DETC (errno_ret ENOENT)).
    - intros o. rewrite D. apply (openat_empty_outcome _ _ _ _ _ Hmfl _ Hc).
    - intros eff mo' evs. cbn [nstep]. rewrite Hleb. unfold efferr, eff0. tauto. }
  assert (Hdir : AT_FDCWD32 = AT_FDCWD32) by reflexivity.
  destruct (path_is_dirref (c :: path')) eqn:Hdot.
  {
    apply (OPENC FdDir).
    - intros o. rewrite D. apply (openat_dirref_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path')); assumption.
    - intros moX eff mo' evs EF ES. cbn [nstep]. rewrite Hleb, Hdot. tauto.
    - exact I. }
  destruct (fs_lookup (m_fs mo) (c :: path')) as [d|] eqn:Hfs.
  {
    apply (OPENC (FdFile (c :: path') (Z_to_bv 64 0))).
    - intros o. rewrite D. apply (openat_file_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path') d); try assumption. discriminate.
    - intros moX eff mo' evs EF ES. cbn [nstep]. rewrite Hleb, Hdot, ES, Hfs. tauto.
    - cbn. congruence. }
  {
    apply (DETC (errno_ret ENOENT)).
    - intros o. rewrite D. apply (openat_absent_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path')); try assumption. discriminate.
    - intros eff mo' evs. cbn [nstep]. rewrite Hleb, Hdot, m_fs_perase, Hfs. unfold efferr, eff0. tauto. }
Qed.

#[using="P mo HF HO"] Lemma ranges_avoid_iov_prefix : forall mp iovs bufs k,
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bytes_at segs (AsanAcct.mrestrict H mp) (bv_unsigned (fst iov)) bs) iovs bufs ->
  Z.of_nat (length (concat bufs)) <= 2^24 ->
  AsanAcct.ranges_avoid H (iov_prefix_accesses iovs k).
Proof.
  intros mp iovs bufs k HF2. revert k. induction HF2 as [|[base len] bs iovs' bufs' [Hl Hb] HF2 IH]; intros k Htot.
  - destruct k; cbn; apply AsanAcct.ranges_avoid_nil.
  - cbn [concat] in Htot. rewrite length_app in Htot. cbn [fst snd] in Hl, Hb.
    assert (Hlen : word_to_nat len = length bs).
    { subst len. unfold word_to_nat. rewrite unsigned_lit64 by lia. apply Nat2Z.id. }
    destruct k as [|k']; [cbn; apply AsanAcct.ranges_avoid_nil|]. cbn [iov_prefix_accesses].
    rewrite word_to_nat_bounded_eq_min, Hlen.
    destruct (Nat.eqb (Nat.min (length bs) (S k')) 0).
    + apply IH. lia.
    + apply AsanAcct.ranges_avoid_cons; [| apply IH; lia].
      intros j Hj. rewrite woff_wa. apply (bytes_at_visible segs H HO _ _ _ Hb). lia.
Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma writev_factsL : forall fd bufs,
  at_node segs (NWritev fd bufs) (restrict H msF) -> factsL segs (LNode (NWritev fd bufs)) H P msF mo (Z_to_bv 64 66).
Proof.
  intros fd bufs HatR.
  destruct HatR as (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Harr & iovs & HiovR & Hbnd & HFR).
  unfold areg in Ha0, Ha2, Harr, HiovR, HFR.
  cbn [AsanAcct.restrict ms_regs ms_mem ms_svc_pending ms_rom] in Hsvc, Ha0, Ha2, Hrom, Harr, HiovR, HFR.
  fold (areg msF 10) in Ha0. fold (areg msF 12) in Ha2. fold (areg msF 11) in Harr. fold (areg msF 11) in HiovR.
  pose proof (bytes_at_unrestrict segs H HO _ _ _ HiovR) as Hiov.
  assert (HFF : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bytes_at segs (ms_mem msF) (bv_unsigned (fst iov)) bs) iovs bufs).
  { eapply Forall2_impl; [| exact HFR]. cbn beta. intros iov bs0 [E Hb]. split; [exact E| eapply bytes_at_unrestrict; eauto]. }
  pose proof HM0 as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS). rewrite !m_fds_strip_vm, ?m_fs_strip_vm, ?m_tid_strip_vm in *.
  set (i := sys_input segs msF (Z_to_bv 64 66)) in *.
  set (iovp := areg msF 11) in *.
  assert (Hlen : length iovs = length bufs) by (eapply Forall2_length; exact HFF).
  destruct (iov_ok_of_bytes_at segs msF iovs bufs Hrom Htot HFF) as [HF' Hsmall].
  set (bs := concat bufs) in *.
  assert (Emem : in_mem i = ms_read_byte msF) by (subst i; apply in_mem_si). rewrite <- Emem in HF'.
  assert (Htotal : iovs_total iovs = Z.of_nat (length bs)) by (subst bs; eapply iovs_total_ok; exact HF').
  assert (Hgather : gather_iovecs (in_mem i) iovs = Some bs) by (subst bs; eapply gather_iovecs_ok; exact HF').
  assert (Hc32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  pose proof (bytes_at_bound _ _ _ _ Hiov) as Hiovb.
  assert (Himp : import_iovecs (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite Hc32, <- Hlen, <- (wa_unsigned_id iovp).
    apply import_iovecs_bytes_in; [rewrite Emem; eapply bytes_at_in; eassumption| exact Hsmall| exact Hbnd| lia| lia| lia]. }
  assert (Hch : fd_lookup (m_fds mo) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd))).
  { rewrite fd32_small by lia. destruct Hfd as [-> | ->]; assumption. }
  assert (Hch0 : w_is0 (Z_to_bv 64 fd) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (Hrw : iovs_total iovs <= MAX_RW_COUNT) by (rewrite Htotal; unfold MAX_RW_COUNT; lia).
  assert (D : forall o, syscall_spec i mo o <->
              writev_spec (fd32 (Z_to_bv 64 fd)) iovp (Z_to_bv 64 (Z.of_nat (length bufs))) i mo o).
  { intros o. subst i. rewrite (syscall_spec_66 _ _ _ (sysno_of segs msF _ 66 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2. reflexivity. }

  assert (HRAI : AsanAcct.ranges_avoid H (import_iovecs_accesses (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))).
  { apply ranges_avoid_import_iovecs. intros j Hj. rewrite woff_wa. apply (bytes_at_visible segs H HO _ _ _ HiovR).
    rewrite length_iovec_bytes. rewrite Hc32 in Hj. unfold word_to_nat in Hj. rewrite unsigned_lit64 in Hj by lia. rewrite Nat2Z.id in Hj. lia. }
  assert (HRAP : forall k, AsanAcct.ranges_avoid H (iov_prefix_accesses iovs k)).
  { intros k. eapply ranges_avoid_iov_prefix; [exact HFR| exact Htot]. }
  destruct bs as [|b0 bs'] eqn:Ebs.
  -
    assert (OUT : forall o, syscall_spec i mo o <->
       o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))
                            (mkEffect (Z_to_bv 64 0) [] [])) mo []).
    { intros o. rewrite D. apply (writev_chan_zero_outcome _ _ _ _ _ _ _ iovs Hch Hch0 Himp). rewrite Htotal; reflexivity. }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL nstep allowL]. fold bs. rewrite Ebs. split; [reflexivity|]. left. rewrite strip_with_copyins. repeat split; reflexivity.
      * apply fdkind_frame; try reflexivity; [exact HM0| rewrite accesses_with_copyins; exact HRAI|].
        apply (hzero_nret_strip H msF (mkEffect (Z_to_bv 64 0) [] [])); [rewrite strip_with_copyins; reflexivity|]. apply hzero_nret_nomem; exact HZ.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. fold bs in Hn. rewrite Ebs in Hn.
      destruct Hn as [-> [(_ & Hs & ->)|(k & Hk & _)]]; [|cbn in Hk; lia].
      eexists _, mo. split; [|split; [apply OUT; reflexivity| reflexivity]]. rewrite strip_with_copyins, Hs. reflexivity.
    + exists (eff0 (Z_to_bv 64 0)), (perase P mo), ([] : list event). cbn [nstepL nstep]. fold bs. rewrite Ebs.
      split; [reflexivity|]. left. repeat split; reflexivity.
  -
    rewrite <- Ebs in *.
    assert (Hbs1 : 1 <= Z.of_nat (length bs)) by (rewrite Ebs; cbn [length]; lia).
    assert (OUT : forall o, syscall_spec i mo o <->
       exists k, (1 <= k <= length bs)%nat /\
         o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] []
                   (import_iovecs_accesses (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
                      ++ iov_prefix_accesses iovs k))
                mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))).
    { intros o. rewrite D. apply (writev_chan_outcome _ _ _ _ _ _ _ iovs bs Hch Hch0 Himp Hrw Hgather Hbs1). }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as (k & Hk & Hs). apply Ok_inj in Hs as (-> & -> & ->). split.
      * cbn [nstepL nstep allowL]. fold bs. split; [reflexivity|]. right. exists k. split; [exact Hk|]. split; reflexivity.
      * apply fdkind_frame; try reflexivity; [exact HM0| |].
        -- unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. rewrite app_nil_r.
           apply AsanAcct.ranges_avoid_app; [exact HRAI| apply HRAP].
        -- apply (hzero_nret_strip H msF (mkEffect (Z_to_bv 64 (Z.of_nat k)) [] [])); [reflexivity|]. apply hzero_nret_nomem; exact HZ.
    + intros Hs. apply OUT in Hs. destruct Hs as (k & _ & Hs). discriminate.
    + intros eff moE' evs Hn. cbn [nstepL nstep] in Hn. fold bs in Hn.
      destruct Hn as [-> [(E & _ & _)|(k & Hk & Hs & ->)]]; [rewrite Ebs in E; discriminate|].
      eexists _, mo. split; [|split; [apply OUT; exists k; split; [exact Hk|reflexivity]| reflexivity]]. rewrite Hs. reflexivity.
    + exists (eff0 (Z_to_bv 64 1)), (perase P mo), (map (WriteEv (Z_to_bv 64 fd)) (firstn 1 bs)). cbn [nstepL nstep]. fold bs.
      split; [reflexivity|]. right. exists 1%nat. split; [rewrite Ebs; cbn [length]; lia|]. split; reflexivity.
Qed.

End PerKind.

Record mm_factsL (segs : list Segment) : Prop := mkMMF {
  mmf_munmap : forall H P msF mo addr len,
      lzframe segs minvL H P mo -> hzero H msF ->
      at_node segs (NMunmap addr len) (restrict H msF) -> nsafeL (LNode (NMunmap addr len)) (perase P mo) ->
      factsL segs (LNode (NMunmap addr len)) H P msF mo (Z_to_bv 64 215);
  mmf_mmap : forall H P msF mo addr len prot flags,
      lzframe segs minvL H P mo -> hzero H msF ->
      at_node segs (NMmap addr len prot flags) (restrict H msF) -> nsafeL (LNode (NMmap addr len prot flags)) (perase P mo) ->
      factsL_ns segs (LNode (NMmap addr len prot flags)) H P msF mo (Z_to_bv 64 222);
  mmf_heap : forall H P msF mo len off,
      lzframe segs minvL H P mo -> hzero H msF ->
      at_nodeL segs (LMmapHeap len off) (restrict H msF) -> nsafeL (LMmapHeap len off) (perase P mo) ->
      factsL_ns segs (LMmapHeap len off) H P msF mo (Z_to_bv 64 222);
  mmf_nr : forall H P msF mo len,
      lzframe segs minvL H P mo -> hzero H msF ->
      at_nodeL segs (LMmapNR len) (restrict H msF) -> nsafeL (LMmapNR len) (perase P mo) ->
      factsL_ns segs (LMmapNR len) H P msF mo (Z_to_bv 64 222);
  mmf_fixed : forall H P msF mo addr len flags,
      lzframe segs minvL H P mo -> hzero H msF ->
      at_nodeL segs (LMmapFixed addr len flags) (restrict H msF) -> nsafeL (LMmapFixed addr len flags) (perase P mo) ->
      factsL_ns segs (LMmapFixed addr len flags) H P msF mo (Z_to_bv 64 222);
  mmf_commit : forall H P msF mo addr len off,
      lzframe segs minvL H P mo -> hzero H msF ->
      at_nodeL segs (LMmapCommit addr len off) (restrict H msF) -> nsafeL (LMmapCommit addr len off) (perase P mo) ->
      factsL_ns segs (LMmapCommit addr len off) H P msF mo (Z_to_bv 64 222);
  mmf_madv : forall H P msF mo addr len,
      lzframe segs minvL H P mo -> hzero H msF ->
      at_nodeL segs (LMadvise addr len) (restrict H msF) -> nsafeL (LMadvise addr len) (perase P mo) ->
      factsL segs (LMadvise addr len) H P msF mo (Z_to_bv 64 233) }.

Section Assembly.
Variable segs : list Segment.
Hypothesis MMF : mm_factsL segs.

Definition is_exit (n : nodeL) : Prop := match n with LNode (NExit _) => True | _ => False end.

#[using="MMF"] Lemma all_factsL : forall n H P msF mo,
  ~ is_exit n ->
  at_nodeL segs n (restrict H msF) -> lzframe segs minvL H P mo -> hzero H msF -> nsafeL n (perase P mo) ->
  exists x8, factsL_ns segs n H P msF mo x8.
Proof.
  intros n H P msF mo Hne Hat HF HZ Hsafe.
  destruct n as [n|len off|len|addr len flags|addr len off|addr len]; cbn [at_nodeL] in Hat.
  -
    destruct n; cbn [nsafeL] in Hsafe;
      try (destruct Hsafe as [_ Hx]; exfalso; exact Hx);
      try (exfalso; exact (Hne I)).
    + eexists. apply factsL_ns_of_factsL; [| apply writev_factsL; eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
    + eexists. apply factsL_ns_of_factsL; [| apply open_factsL; eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
    + eexists. apply factsL_ns_of_factsL; [| apply read_factsL; eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
    + eexists. apply factsL_ns_of_factsL; [| apply close_factsL; eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
    + eexists. apply factsL_ns_of_factsL; [| apply ioctl_factsL; eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
    + eexists. apply factsL_ns_of_factsL; [| apply set_tid_factsL; eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
    + eexists. apply (mmf_mmap segs MMF); eassumption.
    + eexists. apply factsL_ns_of_factsL; [| apply (mmf_munmap segs MMF); eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
  - eexists. apply (mmf_heap segs MMF); eassumption.
  - eexists. apply (mmf_nr segs MMF); eassumption.
  - eexists. apply (mmf_fixed segs MMF); eassumption.
  - eexists. apply (mmf_commit segs MMF); eassumption.
  - eexists. apply factsL_ns_of_factsL; [| apply (mmf_madv segs MMF); eassumption]; apply alloc_no_b_false; vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma exit_factsL : forall c H P msF mo,
  at_node segs (NExit c) (restrict H msF) -> lzframe segs minvL H P mo ->
  (forall evs X, sstep segs (mkCfg msF mo) evs X ->
     X = SNext (mkCfg msF (with_halted (exit_code c) mo)) /\ evs = [ExitEv (exit_code c) (m_fs mo)])
  /\ sstep segs (mkCfg msF mo) [ExitEv (exit_code c) (m_fs mo)] (SNext (mkCfg msF (with_halted (exit_code c) mo))).
Proof.
  intros c H P msF mo Hat HF. apply (exit_node_facts segs msF mo c); [| exact (lf_halt _ _ _ _ _ HF)].
  eapply at_node_unrestrict; [exact (lf_off _ _ _ _ _ HF)| exact Hat].
Qed.

#[using="MMF"] Theorem nodesL_sound_of : node_soundL nodeL segs (at_nodeL segs) nstepL nexitL minvL nsafeL hideL allowL.
Proof.
  constructor.
  -
    intros n ms Hat. destruct n as [n|len off|len|addr len flags|addr len off|addr len]; cbn [at_nodeL] in Hat.
    + exact (ns_pending _ _ _ _ _ _ _ _ (nodes_sound segs) n ms Hat).
    + destruct Hat as [[Hs _] _]. rewrite Hs. discriminate.
    + destruct Hat as [Hs _]. rewrite Hs. discriminate.
    + destruct Hat as [[Hs _] _]. rewrite Hs. discriminate.
    + destruct Hat as [[Hs _] _]. rewrite Hs. discriminate.
    + destruct Hat as [[Hs _] _]. rewrite Hs. discriminate.
  -
    intros n msF mo H P e st Hat HF HZ Hsafe Hst.
    assert (Hcase : (exists c, n = LNode (NExit c)) \/ ~ is_exit n).
    { destruct n as [n| | | | |]; [destruct n|..]; first [left; eexists; reflexivity | right; intros []]. }
    destruct Hcase as [[c ->] | Hne].
    + right. destruct (exit_factsL c H P msF mo Hat HF) as [Hc _]. destruct (Hc _ _ (sstep_of_cfg segs _ _ _ Hst)) as [-> ->].
      eexists _, _. split; [reflexivity|]. split; [| split; [rewrite m_fs_with_halted; reflexivity| apply m_halted_with_halted]].
      cbn [nexitL nexit]. rewrite perase_with_halted. split; reflexivity.
    + destruct (all_factsL n H P msF mo Hne Hat HF HZ Hsafe) as [x8 FL].
      destruct (node_kitL_ns segs n H P msF mo x8 FL HF HZ) as (Hc & _ & _). left. exact (Hc _ _ Hst).
  -
    intros n msF mo H P rsp moE' evs Hat HF HZ Hsafe Hn.
    assert (Hne : ~ is_exit n).
    { destruct n as [n| | | | |]; [destruct n|..]; try (intros []; fail). cbn [nstepL nstep] in Hn. destruct Hn. }
    destruct (all_factsL n H P msF mo Hne Hat HF HZ Hsafe) as [x8 FL].
    destruct (node_kitL_ns segs n H P msF mo x8 FL HF HZ) as (_ & Hs & _). exact (Hs _ _ _ Hn).
  -
    intros n msF mo H P code moE' Hat HF HZ Hsafe HX.
    destruct n as [n| | | | |]; [destruct n|..]; try (destruct HX; fail). cbn [nexitL nexit] in HX. destruct HX as [-> ->].
    exists (with_halted (exit_code code0) mo). rewrite perase_with_halted. split; [reflexivity|].
    split; [apply m_halted_with_halted|]. rewrite m_fs_with_halted, m_fs_perase.
    pose proof (at_node_unrestrict segs H (lf_off _ _ _ _ _ HF) _ _ Hat) as Hat'.
    destruct (proj1 Hat') as [Hsvc|Hsvc];
      (eapply (transparent_nonalloc_no segs msF _ _ _ Hsvc); [reflexivity| vm_compute; reflexivity|]);
      exact (proj2 (exit_factsL code0 H P msF mo Hat HF)).
  -
    intros n msF mo H P Hat HF HZ Hsafe.
    assert (Hcase : (exists c, n = LNode (NExit c)) \/ ~ is_exit n).
    { destruct n as [n| | | | |]; [destruct n|..]; first [left; eexists; reflexivity | right; intros []]. }
    destruct Hcase as [[c ->] | Hne].
    + right. eexists _, _. cbn [nexitL nexit]. split; reflexivity.
    + destruct (all_factsL n H P msF mo Hne Hat HF HZ Hsafe) as [x8 FL].
      destruct (node_kitL_ns segs n H P msF mo x8 FL HF HZ) as (_ & _ & Hp). left. exact Hp.
Qed.

End Assembly.
