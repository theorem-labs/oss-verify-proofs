(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto AMalloc_iface AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA GStatKit HarnCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Atx.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_ATX : Forall (fun k => exists iv, In iv (aci AI) /\ fst iv <= fst k /\ snd k <= snd iv) ATX_DOM.
  Hypothesis CI_RS : exists iv, In iv (aci AI) /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.

  Definition atx_P (cb : Z) (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := exists reg : bool, atx_cells reg cb m.
  Definition atx_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := in_ranges ATX_DOM a.
  Definition atx_comp (cb : Z) : gcomp := mkGC (atx_P cb) atx_dom.

  #[using="Type"] Lemma atx_cells_agree : forall (P : Z -> Prop) reg cb (m m' : mem),
    atx_cells reg cb m -> agrees_on P m m' -> (forall a, in_ranges ATX_DOM a -> P a) -> atx_cells reg cb m'.
  Proof.
    intros P reg cb m m' AC AG HP.
    assert (KC : forall k A cs, In k ATX_DOM -> fst k <= A -> A + Z.of_nat (cells_size cs) <= snd k -> rw_cells asegs m A cs -> rw_cells asegs m' A cs).
    { intros k A cs Hk H1 H2 HC. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply HP. exists k. split; [exact Hk| lia]. }
    unfold atx_cells in *. destruct AC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & (cdt & thr & sec & tm1 & C12)).
    repeat lazymatch goal with
           | |- _ /\ _ => split
           | |- ex _ => exists cdt, thr, sec, tm1
           | |- rw_cells asegs m' ?A _ =>
               first [ eapply (KC (DRV_INIT_FLAG, DRV_INIT_FLAG + 8)); [unfold ATX_DOM, ATX_KEEP; left; reflexivity | unfold DRV_INIT_FLAG; cbn; lia | unfold DRV_INIT_FLAG; cbn; lia | eassumption]
                     | eapply (KC (ATX, ATX + 544)); [unfold ATX_DOM, ATX_KEEP; right; left; reflexivity | unfold ATX; cbn; lia | unfold ATX; cbn; lia | eassumption]
                     | eapply (KC (0x601848, 0x601850)); [unfold ATX_DOM, ATX_KEEP; right; right; left; reflexivity | cbn; lia | cbn; lia | eassumption] ]
           end.
  Qed.

  #[using="Type"] Lemma atx_keep_img : forall k, In k ATX_DOM -> 0x10000 <= fst k /\ snd k <= 0x603000 /\ (snd k <= READ_STAGE \/ READ_STAGE + 65536 <= fst k)
    /\ (snd k <= 0x5e14f0 \/ 0x5e24f0 <= fst k).
  Proof.
    intros k Hk. unfold ATX_DOM, ATX_KEEP in Hk. cbn [app] in Hk.
    repeat (destruct Hk as [<-|Hk]; [cbn [fst snd]; unfold READ_STAGE, DRV_INIT_FLAG, ATX; lia|]). destruct Hk.
  Qed.

  #[using="AF CI_ATX"] Lemma atx_ok : forall cb, gcomp_ok AI (atx_comp cb).
  Proof.
    intros cb. constructor; cbn [gc_P gc_dom atx_comp]; unfold atx_P, atx_dom.
    - intros L RNG RNG' s s' FB m m' [reg AC] _ AG _ _ _. exists reg. eapply (atx_cells_agree (in_ranges ATX_DOM)); [exact AC| exact AG| intros a Ha; exact Ha].
    - intros L RNG s FB m LB SP a _ _ _ Ha (k & Hk & Rk). left. right. left.
      destruct (proj1 (Forall_forall _ _) CI_ATX k Hk) as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - intros L RNG s CL FB FL m a AH _ Ha (k & Hk & Rk). eapply (img_not_client AI AF); [exact AH|].
      destruct (atx_keep_img k Hk) as (K1 & K2 & _). unfold AIMG_HI. lia.
    - intros L s FB a (k & Hk & Rk). destruct (atx_keep_img k Hk) as (K1 & K2 & K3).
      intros [X|X]; [lia|]. pose proof ATPv_img as TI. unfold ATP in X. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition atx_indep (c : gcomp) : Prop := forall L (s : PS) FB a, gc_dom c L s FB a -> ~ in_ranges ATX_KEEP a.

  Section AtxLaws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis INDEP : Forall atx_indep (cs1 ++ cs2).
    #[local] Notation GSTATc cb := (GSTAT_of (cs1 ++ atx_comp cb :: cs2)).

    #[using="Type"] Lemma ga_get_real : forall cb L RNG (s : PS) CL FB FL (m : mem), GIOA_real AI (GSTATc cb) L RNG s CL FB FL m -> exists reg, atx_cells reg cb m.
    Proof.
      intros cb L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 GC).
    Qed.

    (* [comment removed for export] *)
    #[using="AF CI_ATX CI_RS AI_block_tls CSOK INDEP"] Lemma ga_set_real : forall cb cb' reg' L RNG (s : PS) CL FB FL (m m' : mem) W,
      GIOA_real AI (GSTATc cb) L RNG s CL FB FL m -> munch (ATX_KEEP ++ W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
      atx_cells reg' cb' m' ->
      GIOA_real AI (GSTATc cb') L RNG s CL FB FL m'.
    Proof.
      intros cb cb' reg' L RNG s CL FB FL m m' W G MU WM FW AC'.
      pose proof G as (AH & RV & AD & EF & SZ & ND & (ERR & GC)).
      assert (ERR' : exists e : word, rw_cells asegs m' (ATP + -164) [C4 e]).
      { eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        apply (agrees_on_of_munch _ (ATX_KEEP ++ W)); [exact MU| exact WM|]. intros a Ha Ra. apply outside_app2.
        - apply outside_of. intros iv Hi Ri. destruct (atx_keep_img iv ltac:(unfold ATX_DOM; apply in_or_app; left; exact Hi)) as (K1 & K2 & _ & K4). pose proof ATPv_img as TI. unfold ATP in Ra. lia.
        - eapply (errno_outside AI AF AI_block_tls); eassumption. }
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [_ GC2].
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in INDEP as [IN1 IN2].
      assert (G0 : GIOA_real AI (GSTAT_of (cs1 ++ cs2)) L RNG s CL FB FL m).
      { split; [exact AH|]. split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
        split; [exact ERR|]. apply gconj_app. split; assumption. }
      assert (COMP : forall cs, Forall (gcomp_ok AI) cs -> Forall atx_indep cs -> gconj cs L RNG s FB m -> gconj cs L RNG s FB m').
      { intros cs OKs INs GCs. eapply gconj_map; [exact GCs|]. intros c Hc PC.
        pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. pose proof (proj1 (Forall_forall _ _) INs c Hc) as I1.
        eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply (agrees_on_of_munch _ (ATX_KEEP ++ W)); [exact MU| exact WM|]. intros a Ha Da.
        apply outside_app2.
        - apply outside_of. intros iv Hi Ra. apply (I1 _ _ _ _ Da). exists iv. split; [exact Hi| exact Ra].
        - apply (drv_outside FL CL); [exact FW| eapply (gk_client AI c OK); eassumption| exact (gk_drv AI c OK _ _ _ _ Da)]. }
      split.
      { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. apply Forall_app. split.
        - apply Forall_forall. intros k Hk. assert (Hk' : In k ATX_DOM) by (unfold ATX_DOM; apply in_or_app; left; exact Hk). left. left. right. left.
          destruct (proj1 (Forall_forall _ _) CI_ATX k Hk') as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv|]. destruct (atx_keep_img k Hk') as (K1 & K2 & _). lia.
        - eapply Forall_impl; [| exact FW]. intros iv K. left. eapply (drv_iv_arange AI AF (cs1 ++ cs2) CI_RS); [exact G0| exact K]. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split; [exact ERR'|].
      apply gconj_app. split; [exact (COMP cs1 OK1 IN1 GC1)|]. cbn [gconj]. split; [| exact (COMP cs2 OK2 IN2 GC2)].
      cbn [gc_P atx_comp]. unfold atx_P. exists reg'. exact AC'.
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma atx_cells_cb : forall reg cb cb' (m m' : mem),
      atx_cells reg cb m -> munch [(DRV_IN_CB, DRV_IN_CB + 1)] m m' -> wmono asegs m m' ->
      rw_cells asegs m' 0x5e0c54 [C1 (Z_to_bv 8 cb')] -> atx_cells reg cb' m'.
    Proof.
      intros reg cb cb' m m' AC MU WM HC. unfold atx_cells in *.
      destruct AC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & (cdt & thr & sec & tm1 & C12)).
      split; [eapply rw_cells_transport; [exact C1| exact MU| exact WM| cbn; unfold DRV_IN_CB; lia]|].
      split; [exact HC|].
      repeat lazymatch goal with
             | |- _ /\ _ => split
             | |- ex _ => exists cdt, thr, sec, tm1
             | |- rw_cells asegs m' _ _ => eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; unfold DRV_IN_CB; lia]
             end.
    Qed.

    #[using="Type"] Lemma sub_fp_cb : forall W, sub_fp [(DRV_IN_CB, DRV_IN_CB + 1)] (ATX_KEEP ++ W).
    Proof.
      intros W x Hx. unfold ATX_KEEP in Hx. cbn [app outside fst snd] in Hx. destruct Hx as (H1 & _).
      cbn [outside fst snd]. split; [unfold DRV_INIT_FLAG, DRV_IN_CB in *; lia| exact I].
    Qed.

    #[using="AF CI_ATX CI_RS AI_block_tls CSOK INDEP"] Theorem gia_atx_laws_real : gia_atx_laws (GIOA_real AI (GSTATc 0)).
    Proof.
      constructor.
      - exact (ga_get_real 0).
      - intros L RNG s CL FB FL m m' W reg' G MU WM FW AC'. eapply (ga_set_real 0 0); eassumption.
    Qed.

    #[using="AF CI_ATX CI_RS AI_block_tls CSOK INDEP"] Theorem gia_cb_laws_real : gia_cb_laws (GIOA_real AI (GSTATc 0)) (GIOA_real AI (GSTATc 1)).
    Proof.
      constructor.
      - intros L RNG s CL FB FL m m' G MU WM HC. destruct (ga_get_real 0 _ _ _ _ _ _ _ G) as [reg AC].
        eapply (ga_set_real 0 1 reg) with (W := []); [exact G| eapply munch_weaken; [apply sub_fp_cb| exact MU]| exact WM| constructor|].
        eapply atx_cells_cb; eassumption.
      - exact (ga_get_real 1).
      - intros L RNG s CL FB FL m m' G MU WM HC. destruct (ga_get_real 1 _ _ _ _ _ _ _ G) as [reg AC].
        eapply (ga_set_real 1 0 reg) with (W := []); [exact G| eapply munch_weaken; [apply sub_fp_cb| exact MU]| exact WM| constructor|].
        eapply atx_cells_cb; eassumption.
    Qed.
  End AtxLaws.
End Atx.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Atx.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_ATX : Forall (fun k => exists iv, In iv (aci AI) /\ fst iv <= fst k /\ snd k <= snd iv) ATX_DOM.
  Hypothesis CI_RS : exists iv, In iv (aci AI) /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.

  Definition atx_P (cb : Z) (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := exists reg : bool, atx_cells reg cb m.
  Definition atx_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := in_ranges ATX_DOM a.
  Definition atx_comp (cb : Z) : gcomp := mkGC (atx_P cb) atx_dom.

  #[using="Type"] Lemma atx_cells_agree : forall (P : Z -> Prop) reg cb (m m' : mem),
    atx_cells reg cb m -> agrees_on P m m' -> (forall a, in_ranges ATX_DOM a -> P a) -> atx_cells reg cb m'.
  Proof.
    intros P reg cb m m' AC AG HP.
    assert (KC : forall k A cs, In k ATX_DOM -> fst k <= A -> A + Z.of_nat (cells_size cs) <= snd k -> rw_cells asegs m A cs -> rw_cells asegs m' A cs).
    { intros k A cs Hk H1 H2 HC. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply HP. exists k. split; [exact Hk| lia]. }
    unfold atx_cells in *. destruct AC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & (cdt & thr & sec & tm1 & C12)).
    repeat lazymatch goal with
           | |- _ /\ _ => split
           | |- ex _ => exists cdt, thr, sec, tm1
           | |- rw_cells asegs m' ?A _ =>
               first [ eapply (KC (DRV_INIT_FLAG, DRV_INIT_FLAG + 8)); [unfold ATX_DOM, ATX_KEEP; left; reflexivity | unfold DRV_INIT_FLAG; cbn; lia | unfold DRV_INIT_FLAG; cbn; lia | eassumption]
                     | eapply (KC (ATX, ATX + 544)); [unfold ATX_DOM, ATX_KEEP; right; left; reflexivity | unfold ATX; cbn; lia | unfold ATX; cbn; lia | eassumption]
                     | eapply (KC (0x601c48, 0x601c50)); [unfold ATX_DOM, ATX_KEEP; right; right; left; reflexivity | cbn; lia | cbn; lia | eassumption] ]
           end.
  Qed.

  #[using="Type"] Lemma atx_keep_img : forall k, In k ATX_DOM -> 0x10000 <= fst k /\ snd k <= 0x604000 /\ (snd k <= READ_STAGE \/ READ_STAGE + 65536 <= fst k)
    /\ (snd k <= 0x5e18f0 \/ 0x5e28f0 <= fst k).
  Proof.
    intros k Hk. unfold ATX_DOM, ATX_KEEP in Hk. cbn [app] in Hk.
    repeat (destruct Hk as [<-|Hk]; [cbn [fst snd]; unfold READ_STAGE, DRV_INIT_FLAG, ATX; lia|]). destruct Hk.
  Qed.

  #[using="AF CI_ATX"] Lemma atx_ok : forall cb, gcomp_ok AI (atx_comp cb).
  Proof.
    intros cb. constructor; cbn [gc_P gc_dom atx_comp]; unfold atx_P, atx_dom.
    - intros L RNG RNG' s s' FB m m' [reg AC] _ AG _ _ _. exists reg. eapply (atx_cells_agree (in_ranges ATX_DOM)); [exact AC| exact AG| intros a Ha; exact Ha].
    - intros L RNG s FB m LB SP a _ _ _ Ha (k & Hk & Rk). left. right. left.
      destruct (proj1 (Forall_forall _ _) CI_ATX k Hk) as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - intros L RNG s CL FB FL m a AH _ Ha (k & Hk & Rk). eapply (img_not_client AI AF); [exact AH|].
      destruct (atx_keep_img k Hk) as (K1 & K2 & _). unfold AIMG_HI. lia.
    - intros L s FB a (k & Hk & Rk). destruct (atx_keep_img k Hk) as (K1 & K2 & K3).
      intros [X|X]; [lia|]. pose proof ATPv_img as TI. unfold ATP in X. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition atx_indep (c : gcomp) : Prop := forall L (s : PS) FB a, gc_dom c L s FB a -> ~ in_ranges ATX_KEEP a.

  Section AtxLaws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis INDEP : Forall atx_indep (cs1 ++ cs2).
    #[local] Notation GSTATc cb := (GSTAT_of (cs1 ++ atx_comp cb :: cs2)).

    #[using="Type"] Lemma ga_get_real : forall cb L RNG (s : PS) CL FB FL (m : mem), GIOA_real AI (GSTATc cb) L RNG s CL FB FL m -> exists reg, atx_cells reg cb m.
    Proof.
      intros cb L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 GC).
    Qed.

    (* [comment removed for export] *)
    #[using="AF CI_ATX CI_RS AI_block_tls CSOK INDEP"] Lemma ga_set_real : forall cb cb' reg' L RNG (s : PS) CL FB FL (m m' : mem) W,
      GIOA_real AI (GSTATc cb) L RNG s CL FB FL m -> munch (ATX_KEEP ++ W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
      atx_cells reg' cb' m' ->
      GIOA_real AI (GSTATc cb') L RNG s CL FB FL m'.
    Proof.
      intros cb cb' reg' L RNG s CL FB FL m m' W G MU WM FW AC'.
      pose proof G as (AH & RV & AD & EF & SZ & ND & (ERR & GC)).
      assert (ERR' : exists e : word, rw_cells asegs m' (ATP + -164) [C4 e]).
      { eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        apply (agrees_on_of_munch _ (ATX_KEEP ++ W)); [exact MU| exact WM|]. intros a Ha Ra. apply outside_app2.
        - apply outside_of. intros iv Hi Ri. destruct (atx_keep_img iv ltac:(unfold ATX_DOM; apply in_or_app; left; exact Hi)) as (K1 & K2 & _ & K4). pose proof ATPv_img as TI. unfold ATP in Ra. lia.
        - eapply (errno_outside AI AF AI_block_tls); eassumption. }
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [_ GC2].
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in INDEP as [IN1 IN2].
      assert (G0 : GIOA_real AI (GSTAT_of (cs1 ++ cs2)) L RNG s CL FB FL m).
      { split; [exact AH|]. split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
        split; [exact ERR|]. apply gconj_app. split; assumption. }
      assert (COMP : forall cs, Forall (gcomp_ok AI) cs -> Forall atx_indep cs -> gconj cs L RNG s FB m -> gconj cs L RNG s FB m').
      { intros cs OKs INs GCs. eapply gconj_map; [exact GCs|]. intros c Hc PC.
        pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. pose proof (proj1 (Forall_forall _ _) INs c Hc) as I1.
        eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply (agrees_on_of_munch _ (ATX_KEEP ++ W)); [exact MU| exact WM|]. intros a Ha Da.
        apply outside_app2.
        - apply outside_of. intros iv Hi Ra. apply (I1 _ _ _ _ Da). exists iv. split; [exact Hi| exact Ra].
        - apply (drv_outside FL CL); [exact FW| eapply (gk_client AI c OK); eassumption| exact (gk_drv AI c OK _ _ _ _ Da)]. }
      split.
      { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. apply Forall_app. split.
        - apply Forall_forall. intros k Hk. assert (Hk' : In k ATX_DOM) by (unfold ATX_DOM; apply in_or_app; left; exact Hk). left. left. right. left.
          destruct (proj1 (Forall_forall _ _) CI_ATX k Hk') as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv|]. destruct (atx_keep_img k Hk') as (K1 & K2 & _). lia.
        - eapply Forall_impl; [| exact FW]. intros iv K. left. eapply (drv_iv_arange AI AF (cs1 ++ cs2) CI_RS); [exact G0| exact K]. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split; [exact ERR'|].
      apply gconj_app. split; [exact (COMP cs1 OK1 IN1 GC1)|]. cbn [gconj]. split; [| exact (COMP cs2 OK2 IN2 GC2)].
      cbn [gc_P atx_comp]. unfold atx_P. exists reg'. exact AC'.
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma atx_cells_cb : forall reg cb cb' (m m' : mem),
      atx_cells reg cb m -> munch [(DRV_IN_CB, DRV_IN_CB + 1)] m m' -> wmono asegs m m' ->
      rw_cells asegs m' 0x5e1054 [C1 (Z_to_bv 8 cb')] -> atx_cells reg cb' m'.
    Proof.
      intros reg cb cb' m m' AC MU WM HC. unfold atx_cells in *.
      destruct AC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & (cdt & thr & sec & tm1 & C12)).
      split; [eapply rw_cells_transport; [exact C1| exact MU| exact WM| cbn; unfold DRV_IN_CB; lia]|].
      split; [exact HC|].
      repeat lazymatch goal with
             | |- _ /\ _ => split
             | |- ex _ => exists cdt, thr, sec, tm1
             | |- rw_cells asegs m' _ _ => eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; unfold DRV_IN_CB; lia]
             end.
    Qed.

    #[using="Type"] Lemma sub_fp_cb : forall W, sub_fp [(DRV_IN_CB, DRV_IN_CB + 1)] (ATX_KEEP ++ W).
    Proof.
      intros W x Hx. unfold ATX_KEEP in Hx. cbn [app outside fst snd] in Hx. destruct Hx as (H1 & _).
      cbn [outside fst snd]. split; [unfold DRV_INIT_FLAG, DRV_IN_CB in *; lia| exact I].
    Qed.

    #[using="AF CI_ATX CI_RS AI_block_tls CSOK INDEP"] Theorem gia_atx_laws_real : gia_atx_laws (GIOA_real AI (GSTATc 0)).
    Proof.
      constructor.
      - exact (ga_get_real 0).
      - intros L RNG s CL FB FL m m' W reg' G MU WM FW AC'. eapply (ga_set_real 0 0); eassumption.
    Qed.

    #[using="AF CI_ATX CI_RS AI_block_tls CSOK INDEP"] Theorem gia_cb_laws_real : gia_cb_laws (GIOA_real AI (GSTATc 0)) (GIOA_real AI (GSTATc 1)).
    Proof.
      constructor.
      - intros L RNG s CL FB FL m m' G MU WM HC. destruct (ga_get_real 0 _ _ _ _ _ _ _ G) as [reg AC].
        eapply (ga_set_real 0 1 reg) with (W := []); [exact G| eapply munch_weaken; [apply sub_fp_cb| exact MU]| exact WM| constructor|].
        eapply atx_cells_cb; eassumption.
      - exact (ga_get_real 1).
      - intros L RNG s CL FB FL m m' G MU WM HC. destruct (ga_get_real 1 _ _ _ _ _ _ _ G) as [reg AC].
        eapply (ga_set_real 1 0 reg) with (W := []); [exact G| eapply munch_weaken; [apply sub_fp_cb| exact MU]| exact WM| constructor|].
        eapply atx_cells_cb; eassumption.
    Qed.
  End AtxLaws.
End Atx.
End CANSEC1.
End TwB.
