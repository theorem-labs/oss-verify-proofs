(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Stable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Embed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Raw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.LB_WRealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Section RawRealloc.
Context {St : Type} {AS : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.AllocSt St}.
Hypothesis MQ : malloc_core_fq_stmt.

(* [comment removed for export] *)
#[using="MQ"] Theorem raw_reallocF_Q_pt X P G p n n' s0 mo0 :
  frame_ok G -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  FQ ((p, n) :: X) P G s0 mo0 -> ROOMN (map snd ((p, n) :: X)) P n' ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_reallocF peekG (Some p) n')
        (fun r s mo => match r with
                       | Some q => FQ ((q, n') :: X) P G s mo /\ (forall q0 sz, In (q0, sz) X -> conc (ps_m s) q0 = conc (ps_m s0) q0)
                       | None => FQ ((p, n) :: X) P G s mo /\ (forall q0 sz, In (q0, sz) ((p, n) :: X) -> conc (ps_m s) q0 = conc (ps_m s0) q0)
                       end
                       /\ ps_rest s = ps_rest s0 /\ vm_only mo0 mo).
Proof.
  intros HG Hn' Hov Hnx HQ HF HR. unfold raw_reallocF.
  eapply mspec_bind; [apply mspec_get|]. intros s1.
  apply mspec_pointwise. intros ? ? [-> [-> ->]].
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HGs].
  apply (ROOMN_eq ((p, n) :: X) BL P n' HP) in HR.
  assert (Hin : In (p, n) (map blk_ptr BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n_] & Ebp & Hk). unfold blk_ptr in Ebp. cbn [bslot boff bsize fst snd] in Ebp.
  assert (En : n_ = n) by congruence. subst n_. assert (Ep : p = aadd c (UNIT * off)) by congruence.
  pose proof (blk_ptr_remove_perm c off n BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP.
  assert (HPX : Permutation X (map blk_ptr (bl_remove c BL))).
  { apply (Permutation_cons_inv (a := (p, n))). etransitivity; [exact HP|]. rewrite Ep.
    change (blk_ptr (c, off, n)) with (aadd c (UNIT * off), n) in BP. exact BP. }
  destruct (realloc_ftq MQ P (PHI P + R63 BL + bigb n') (ps_m s0) L BL LS c off n n' INV SI HAQ Hk Hn' Hov Hnx HR ltac:(unfold PGSZ; lia) HQ) as [FT _].
  rewrite <- Ep in FT.
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_LI (realloc (ps_m s0) (Some p) n') _ (Gsince G s0 mo0) L s0 (Gsince_frame G s0 mo0 HG) FT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. split; [reflexivity| apply vm_only_refl]. }
  intros [st' q]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HL' & (HG' & Hr' & Hvo') & Hm' & Hx).
  unfold realloc_postQ in HPost. cbn [fst snd] in HPost.
  (* [comment removed for export] *)
  assert (STABX : forall BLr, cstable (ps_m s0) BLr st' -> forall Y, Permutation Y (map blk_ptr BLr) ->
            forall q0 sz, In (q0, sz) Y -> conc st' q0 = conc (ps_m s0) q0).
  { intros BLr CS Y PY q0 sz Hin0. assert (Hin' : In (q0, sz) (map blk_ptr BLr)) by (eapply Permutation_in; [exact PY| exact Hin0]).
    apply in_map_iff in Hin' as ([[c0 off0] n0] & Ebp0 & Hk0). unfold blk_ptr in Ebp0. cbn [bslot boff bsize fst snd] in Ebp0.
    assert (Eq0 : q0 = aadd c0 (UNIT * off0)) by congruence. rewrite Eq0. change c0 with (bslot (c0, off0, n0)). apply CS. exact Hk0. }
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->]. unfold FQ. autorewrite with alloc_lens.
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']. }
  split; [| split; [exact Hr'| exact Hvo']].
  destruct q as [q|].
  - destruct HPost as [(c' & off' & LS' & Hq' & Hoff & INV' & Hc' & SI' & HAQ') CS].
    split; [| exact (STABX _ CS X HPX)].
    split; [| exact HG2]. exists L', LS', (((c', off'), n') :: bl_remove c BL). split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'|].
    cbn [map]. unfold blk_ptr at 1. cbn [bslot boff bsize fst snd]. rewrite <- Hq'. apply perm_skip. exact HPX.
  - destruct HPost as [((LS' & INV') & SI' & HAQ') CS].
    split; [| exact (STABX _ CS ((p, n) :: X) HP)].
    split; [| exact HG2]. exists L', LS', BL. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'| exact HP].
Qed.

#[using="MQ"] Theorem raw_reallocF_Q X P G p n n' :
  frame_ok G -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  mspec (fun s mo => FQ ((p, n) :: X) P G s mo /\ ROOMN (map snd ((p, n) :: X)) P n') (raw_reallocF peekG (Some p) n')
        (fun r s mo => match r with Some q => FQ ((q, n') :: X) P G s mo | None => FQ ((p, n) :: X) P G s mo end).
Proof.
  intros HG Hn' Hov Hnx HQ. apply mspec_pointwise. intros s0 mo0 [HF HR].
  eapply mspec_post; [apply (raw_reallocF_Q_pt X P G p n n' s0 mo0 HG Hn' Hov Hnx HQ HF HR)|]. intros a s mo [H _]. destruct a; exact (proj1 H).
Qed.
End RawRealloc.

End WithCeil.
