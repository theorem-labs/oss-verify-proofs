(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP AMalloc_iface AEmbRep AFrameD AEmbFrame ARefill_iface_x AC6Frame
     ANullPres ASecModel.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition c6_pieceS (L : alayout) (RESV : list (Z * Z)) (st : astate) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     c6_piece L iv
  \/ (al_ptr_array L <= fst iv /\ snd iv <= al_ptr_array L + 8388608)
  \/ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ asec_ranges st) = true.

Theorem c6_frameS : forall L RESV RNG st m m' (W : list ivl),
  alayout_ok L -> aresv_ok L RESV -> axg RESV RNG st m -> axflags L st m -> munch W m m' -> Forall (c6_pieceS L RESV st) W ->
  axg RESV RNG st m' /\ axflags L st m'.
Proof.
  intros L RESV RNG st m m' W ALO ARV (XC & EC & ER & ECL) AXF MU PCS.
  pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT1 & OT2 & _ & OTi). unfold iclr, AIMG_LO, AIMG_HI in OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj_img _ _ (ao_nodes L ALO) ltac:(lia)) as ONi. pose proof (aobj_img _ _ (ao_store L ALO) ltac:(lia)) as OSi. unfold AIMG_HI in ONi, OSi.
  pose proof (aobj_img _ _ (ao_ptr L ALO) ltac:(lia)) as OPi. unfold AIMG_HI in OPi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_ptr_res L ALO) as DPR.
  unfold adisj in DTR, DNR, DSR, DPR.
  pose proof ARV as (PCI & PCS' & PCR & PCP & PCT & _ & PCN & PCST & _). fold (al_res L) in PCR.

  assert (VAL : forall lo hi l h x, avoids_all lo (hi - lo) (RESV ++ asec_ranges st) = true -> pcov RESV l h -> l <= x < h -> ~ (lo <= x < hi)).
  { intros lo hi l h x AV PC Hx IN. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    apply (avoids_pcov_out RESV lo (hi - lo) l h x PC AV Hx). lia. }

  assert (IC : forall x, c6_img x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_pieceS in K. cbn [fst snd] in K.
    intros IN. destruct (K ltac:(lia)) as [K1|[K2|K3]].
    - unfold c6_piece in K1. cbn [fst snd] in K1. specialize (K1 ltac:(lia)). unfold c6_img, AEMB, AINSTANCE, AERRNO, ATP in *.
      clear -K1 IN Hx ATR OT1 OT2 OTi ORH ONi OSi. lia.
    - unfold c6_img, AEMB in Hx. clear -K2 IN Hx OPi. lia.
    - apply (VAL lo hi 0x10000 AIMG_HI x K3 PCI); [unfold c6_img, AEMB, AIMG_HI in *; clear -Hx; lia| exact IN]. }

  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { pose proof EC as EC1. unfold emb_cells in EC1. unfold emb_clr in ECL. destruct (a_emb st) as [[d cap] sz] eqn:EA. intros x Hx.
    destruct (Z.eqb_spec cap 0) as [E0|NZ]; [exfalso; lia|].
    destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2.
    destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    pose proof (pcov_clear _ _ _ _ _ PCI AV ltac:(unfold AIMG_HI; lia) ltac:(lia)) as Q1.
    pose proof (pcov_clear _ _ _ _ _ PCS' AV ltac:(lia) ltac:(lia)) as Q2.
    pose proof (pcov_clear _ _ _ _ _ PCR AV ltac:(lia) ltac:(lia)) as Q3.
    pose proof (pcov_clear _ _ _ _ _ PCT AV ltac:(lia) ltac:(lia)) as Q4.
    pose proof (pcov_clear _ _ _ _ _ PCN AV ltac:(lia) ltac:(lia)) as Q5.
    pose proof (pcov_clear _ _ _ _ _ PCST AV ltac:(lia) ltac:(lia)) as Q6.
    pose proof (pcov_clear _ _ _ _ _ PCP AV ltac:(lia) ltac:(lia)) as Q7.
    apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_pieceS in K. cbn [fst snd] in K.
    intros IN. destruct (K ltac:(lia)) as [K1|[K2|K3]].
    - unfold c6_piece in K1. cbn [fst snd] in K1. specialize (K1 ltac:(lia)). unfold AIMG_HI, AINSTANCE, AERRNO, ATP in *.
      clear -K1 IN Hx P6 Q1 Q2 Q3 Q4 Q5 Q6 RSP ATR. lia.
    - clear -K2 IN Hx Q7. lia.
    -
      unfold avoids_all in K3. rewrite forallb_app in K3. apply andb_prop in K3 as [_ K3]. unfold asec_ranges in K3. rewrite forallb_app in K3.
      apply andb_prop in K3 as [_ K3]. unfold emb_iv in K3. rewrite EA in K3. replace (cap =? 0) with false in K3 by (symmetry; apply Z.eqb_neq; exact NZ).
      cbn [forallb] in K3. rewrite andb_true_r in K3. unfold iv_clear in K3. cbn [fst snd] in K3. apply orb_prop in K3 as [Q|Q]; apply Z.leb_le in Q; lia. }
  split.
  - split; [exact (exh_cells_frameC m m' W XC MU IC)|]. split; [exact (emb_cells_frameC st m m' W EC MU IC DB)|]. split; [exact ER| exact ECL].
  - intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add].
    intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_pieceS in K. cbn [fst snd] in K.
    intros IN.
    assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
    destruct (K ltac:(lia)) as [K1|[K2|K3]].
    + unfold c6_piece in K1. cbn [fst snd] in K1. specialize (K1 ltac:(lia)).
      unfold K_NUM_CLASSES, AINSTANCE, AERRNO, ATP in *. rewrite RIE in Hx.
      clear -K1 IN Hx Hc ATR OT1 OT2 OTi ORS ORH RSP ONi OSi DTR DNR DSR. lia.
    + unfold K_NUM_CLASSES in *. rewrite RIE in Hx. clear -K2 IN Hx Hc RSP DPR. lia.
    + apply (VAL lo hi _ _ x K3 PCR); [unfold K_NUM_CLASSES in *; rewrite RIE in Hx; clear -Hx Hc RSP; lia| exact IN].
Qed.

Lemma st_sec_x : forall st nres' a ms n, a_emb (st_sec st nres' a ms n) = a_emb st /\ a_exh (st_sec st nres' a ms n) = a_exh st.
Proof. intros. destruct st. split; reflexivity. Qed.
Lemma achunks_st_sec : forall st nres' a ms n iv, In iv (flat_map sec_iv (achunks (st_sec st nres' a ms n))) ->
  iv = (a, a + ms) \/ In iv (flat_map sec_iv (achunks st)).
Proof.
  intros st nres' a ms n iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  destruct (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & EL & _ & EQ1 & _ & EQ2 & _).
  unfold achunks in Hch. rewrite EL, EQ1, EQ2 in Hch. apply in_app_or in Hch as [Hch|Hch].
  - apply in_map_iff in Hch as ([p ch'] & E & Hp). cbn [snd] in E. subst ch'.
    apply list_elem_of_In in Hp. apply elem_of_map_to_list in Hp. apply lookup_insert_Some in Hp as [[_ E]|[_ Hp]].
    + subst ch. cbn [sec_iv] in Hin. destruct Hin as [<-|[]]. left. reflexivity.
    + right. apply in_flat_map. exists ch. split; [| exact Hin]. unfold achunks. apply in_or_app. left. apply in_map_iff. exists (p, ch). split; [reflexivity|].
      apply list_elem_of_In. apply elem_of_map_to_list. exact Hp.
  - right. apply in_flat_map. exists ch. split; [| exact Hin]. unfold achunks. apply in_or_app. right. exact Hch.
Qed.
Lemma axg_st_sec : forall RESV RNG st nres' a ms n m,
  avoids_all a ms (RESV ++ asec_ranges st) = true -> axg RESV RNG st m -> axg RESV RNG (st_sec st nres' a ms n) m.
Proof.
  intros RESV RNG st nres' a ms n m AV (XC & EC & ER & ECL). destruct (st_sec_x st nres' a ms n) as [EE _].
  split; [exact XC|]. split; [unfold emb_cells in *; rewrite EE; exact EC|]. split; [unfold emb_rng in *; rewrite EE; exact ER|].
  unfold emb_clr in *. rewrite EE. destruct (a_emb st) as [[d cap] sz] eqn:EA.
  destruct (Z.eqb_spec cap 0) as [E0|NZ]; [left; exact E0|]. destruct ECL as [Z0|ECL]; [exfalso; exact (NZ Z0)| right].
  unfold avoids_all in *. rewrite forallb_app in *. apply andb_prop in ECL as [E1 E2]. apply andb_true_intro. split; [exact E1|].
  apply forallb_forall. intros iv Hiv. destruct (achunks_st_sec st nres' a ms n iv Hiv) as [->|OLD]; [| exact (proj1 (forallb_forall _ _) E2 iv OLD)].
  apply andb_prop in AV as [_ AV]. unfold asec_ranges in AV. rewrite forallb_app in AV. apply andb_prop in AV as [_ AV]. unfold emb_iv in AV. rewrite EA in AV.
  replace (cap =? 0) with false in AV by (symmetry; apply Z.eqb_neq; exact NZ). cbn [forallb] in AV. rewrite andb_true_r in AV.
  unfold iv_clear in *. cbn [fst snd] in *. apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; apply orb_true_iff; [right| left]; apply Z.leb_le; lia.
Qed.
Lemma axflags_st_sec : forall L st nres' a ms n m, axflags L st m -> axflags L (st_sec st nres' a ms n) m.
Proof.
  intros L st nres' a ms n m AXF c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. destruct (st_sec_x st nres' a ms n) as [_ EX].
  rewrite (exh_mem_eq_list c st (st_sec st nres' a ms n) EX). exact AXF.
Qed.
End CANSEC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB AMalloc_iface.TwinB AEmbRep.TwinB AFrameD.TwinB AEmbFrame.TwinB ARefill_iface_x.TwinB AC6Frame.TwinB ANullPres.TwinB ASecModel.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition c6_pieceS (L : alayout) (RESV : list (Z * Z)) (st : astate) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     c6_piece L iv
  \/ (al_ptr_array L <= fst iv /\ snd iv <= al_ptr_array L + 8388608)
  \/ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ asec_ranges st) = true.

Theorem c6_frameS : forall L RESV RNG st m m' (W : list ivl),
  alayout_ok L -> aresv_ok L RESV -> axg RESV RNG st m -> axflags L st m -> munch W m m' -> Forall (c6_pieceS L RESV st) W ->
  axg RESV RNG st m' /\ axflags L st m'.
Proof.
  intros L RESV RNG st m m' W ALO ARV (XC & EC & ER & ECL) AXF MU PCS.
  pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT1 & OT2 & _ & OTi). unfold iclr, AIMG_LO, AIMG_HI in OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj_img _ _ (ao_nodes L ALO) ltac:(lia)) as ONi. pose proof (aobj_img _ _ (ao_store L ALO) ltac:(lia)) as OSi. unfold AIMG_HI in ONi, OSi.
  pose proof (aobj_img _ _ (ao_ptr L ALO) ltac:(lia)) as OPi. unfold AIMG_HI in OPi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_ptr_res L ALO) as DPR.
  unfold adisj in DTR, DNR, DSR, DPR.
  pose proof ARV as (PCI & PCS' & PCR & PCP & PCT & _ & PCN & PCST & _). fold (al_res L) in PCR.

  assert (VAL : forall lo hi l h x, avoids_all lo (hi - lo) (RESV ++ asec_ranges st) = true -> pcov RESV l h -> l <= x < h -> ~ (lo <= x < hi)).
  { intros lo hi l h x AV PC Hx IN. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    apply (avoids_pcov_out RESV lo (hi - lo) l h x PC AV Hx). lia. }

  assert (IC : forall x, c6_img x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_pieceS in K. cbn [fst snd] in K.
    intros IN. destruct (K ltac:(lia)) as [K1|[K2|K3]].
    - unfold c6_piece in K1. cbn [fst snd] in K1. specialize (K1 ltac:(lia)). unfold c6_img, AEMB, AINSTANCE, AERRNO, ATP in *.
      clear -K1 IN Hx ATR OT1 OT2 OTi ORH ONi OSi. lia.
    - unfold c6_img, AEMB in Hx. clear -K2 IN Hx OPi. lia.
    - apply (VAL lo hi 0x10000 AIMG_HI x K3 PCI); [unfold c6_img, AEMB, AIMG_HI in *; clear -Hx; lia| exact IN]. }

  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { pose proof EC as EC1. unfold emb_cells in EC1. unfold emb_clr in ECL. destruct (a_emb st) as [[d cap] sz] eqn:EA. intros x Hx.
    destruct (Z.eqb_spec cap 0) as [E0|NZ]; [exfalso; lia|].
    destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2.
    destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    pose proof (pcov_clear _ _ _ _ _ PCI AV ltac:(unfold AIMG_HI; lia) ltac:(lia)) as Q1.
    pose proof (pcov_clear _ _ _ _ _ PCS' AV ltac:(lia) ltac:(lia)) as Q2.
    pose proof (pcov_clear _ _ _ _ _ PCR AV ltac:(lia) ltac:(lia)) as Q3.
    pose proof (pcov_clear _ _ _ _ _ PCT AV ltac:(lia) ltac:(lia)) as Q4.
    pose proof (pcov_clear _ _ _ _ _ PCN AV ltac:(lia) ltac:(lia)) as Q5.
    pose proof (pcov_clear _ _ _ _ _ PCST AV ltac:(lia) ltac:(lia)) as Q6.
    pose proof (pcov_clear _ _ _ _ _ PCP AV ltac:(lia) ltac:(lia)) as Q7.
    apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_pieceS in K. cbn [fst snd] in K.
    intros IN. destruct (K ltac:(lia)) as [K1|[K2|K3]].
    - unfold c6_piece in K1. cbn [fst snd] in K1. specialize (K1 ltac:(lia)). unfold AIMG_HI, AINSTANCE, AERRNO, ATP in *.
      clear -K1 IN Hx P6 Q1 Q2 Q3 Q4 Q5 Q6 RSP ATR. lia.
    - clear -K2 IN Hx Q7. lia.
    -
      unfold avoids_all in K3. rewrite forallb_app in K3. apply andb_prop in K3 as [_ K3]. unfold asec_ranges in K3. rewrite forallb_app in K3.
      apply andb_prop in K3 as [_ K3]. unfold emb_iv in K3. rewrite EA in K3. replace (cap =? 0) with false in K3 by (symmetry; apply Z.eqb_neq; exact NZ).
      cbn [forallb] in K3. rewrite andb_true_r in K3. unfold iv_clear in K3. cbn [fst snd] in K3. apply orb_prop in K3 as [Q|Q]; apply Z.leb_le in Q; lia. }
  split.
  - split; [exact (exh_cells_frameC m m' W XC MU IC)|]. split; [exact (emb_cells_frameC st m m' W EC MU IC DB)|]. split; [exact ER| exact ECL].
  - intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add].
    intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_pieceS in K. cbn [fst snd] in K.
    intros IN.
    assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
    destruct (K ltac:(lia)) as [K1|[K2|K3]].
    + unfold c6_piece in K1. cbn [fst snd] in K1. specialize (K1 ltac:(lia)).
      unfold K_NUM_CLASSES, AINSTANCE, AERRNO, ATP in *. rewrite RIE in Hx.
      clear -K1 IN Hx Hc ATR OT1 OT2 OTi ORS ORH RSP ONi OSi DTR DNR DSR. lia.
    + unfold K_NUM_CLASSES in *. rewrite RIE in Hx. clear -K2 IN Hx Hc RSP DPR. lia.
    + apply (VAL lo hi _ _ x K3 PCR); [unfold K_NUM_CLASSES in *; rewrite RIE in Hx; clear -Hx Hc RSP; lia| exact IN].
Qed.

Lemma st_sec_x : forall st nres' a ms n, a_emb (st_sec st nres' a ms n) = a_emb st /\ a_exh (st_sec st nres' a ms n) = a_exh st.
Proof. intros. destruct st. split; reflexivity. Qed.
Lemma achunks_st_sec : forall st nres' a ms n iv, In iv (flat_map sec_iv (achunks (st_sec st nres' a ms n))) ->
  iv = (a, a + ms) \/ In iv (flat_map sec_iv (achunks st)).
Proof.
  intros st nres' a ms n iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  destruct (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & EL & _ & EQ1 & _ & EQ2 & _).
  unfold achunks in Hch. rewrite EL, EQ1, EQ2 in Hch. apply in_app_or in Hch as [Hch|Hch].
  - apply in_map_iff in Hch as ([p ch'] & E & Hp). cbn [snd] in E. subst ch'.
    apply list_elem_of_In in Hp. apply elem_of_map_to_list in Hp. apply lookup_insert_Some in Hp as [[_ E]|[_ Hp]].
    + subst ch. cbn [sec_iv] in Hin. destruct Hin as [<-|[]]. left. reflexivity.
    + right. apply in_flat_map. exists ch. split; [| exact Hin]. unfold achunks. apply in_or_app. left. apply in_map_iff. exists (p, ch). split; [reflexivity|].
      apply list_elem_of_In. apply elem_of_map_to_list. exact Hp.
  - right. apply in_flat_map. exists ch. split; [| exact Hin]. unfold achunks. apply in_or_app. right. exact Hch.
Qed.
Lemma axg_st_sec : forall RESV RNG st nres' a ms n m,
  avoids_all a ms (RESV ++ asec_ranges st) = true -> axg RESV RNG st m -> axg RESV RNG (st_sec st nres' a ms n) m.
Proof.
  intros RESV RNG st nres' a ms n m AV (XC & EC & ER & ECL). destruct (st_sec_x st nres' a ms n) as [EE _].
  split; [exact XC|]. split; [unfold emb_cells in *; rewrite EE; exact EC|]. split; [unfold emb_rng in *; rewrite EE; exact ER|].
  unfold emb_clr in *. rewrite EE. destruct (a_emb st) as [[d cap] sz] eqn:EA.
  destruct (Z.eqb_spec cap 0) as [E0|NZ]; [left; exact E0|]. destruct ECL as [Z0|ECL]; [exfalso; exact (NZ Z0)| right].
  unfold avoids_all in *. rewrite forallb_app in *. apply andb_prop in ECL as [E1 E2]. apply andb_true_intro. split; [exact E1|].
  apply forallb_forall. intros iv Hiv. destruct (achunks_st_sec st nres' a ms n iv Hiv) as [->|OLD]; [| exact (proj1 (forallb_forall _ _) E2 iv OLD)].
  apply andb_prop in AV as [_ AV]. unfold asec_ranges in AV. rewrite forallb_app in AV. apply andb_prop in AV as [_ AV]. unfold emb_iv in AV. rewrite EA in AV.
  replace (cap =? 0) with false in AV by (symmetry; apply Z.eqb_neq; exact NZ). cbn [forallb] in AV. rewrite andb_true_r in AV.
  unfold iv_clear in *. cbn [fst snd] in *. apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; apply orb_true_iff; [right| left]; apply Z.leb_le; lia.
Qed.
Lemma axflags_st_sec : forall L st nres' a ms n m, axflags L st m -> axflags L (st_sec st nres' a ms n) m.
Proof.
  intros L st nres' a ms n m AXF c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. destruct (st_sec_x st nres' a ms n) as [_ EX].
  rewrite (exh_mem_eq_list c st (st_sec st nres' a ms n) EX). exact AXF.
Qed.
End CANSEC.
End TwinB.
