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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA GStatKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Harn.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_HARN : exists iv, In iv (aci AI) /\ fst iv <= OUTFILE_ADDR /\ OUTFILE_ADDR + 8 <= snd iv.

  Definition harn_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    match ps_outfile s with
    | None => rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
    | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
    end.
  Definition harn_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := OUTFILE_ADDR <= a < OUTFILE_ADDR + 8.
  Definition harn_comp : gcomp := mkGC harn_P harn_dom.

  #[using="AF CI_HARN"] Lemma harn_ok : gcomp_ok AI harn_comp.
  Proof.
    constructor; cbn [gc_P gc_dom harn_comp]; unfold harn_P, harn_dom.
    - intros L RNG RNG' s s' FB m m' HPm _ AG _ EO _. rewrite EO.
      destruct (ps_outfile s) as [q|].
      + (nd_pre HPm 3%nat; intros A HA HC; nd_post). exists A. split; [exact HA|]. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. unfold harn_dom. lia.
      + eapply agrees_rw_cells; [exact AG| exact HPm|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. unfold harn_dom. lia.
    - intros L RNG s FB m LB SP a _ _ _ _ Da. left. right. left. destruct CI_HARN as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (img_not_client AI AF); [exact AH|]. unfold OUTFILE_ADDR, AIMG_HI in *. lia.
    - intros L s FB a Da [X|X]; unfold OUTFILE_ADDR, READ_STAGE in *; [lia|]. pose proof ATPv_img as TI. unfold ATP in X. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition harn_indep (c : gcomp) : Prop :=
    (forall L RNG (s : PS) FB (m : mem) o, gc_P c L RNG s FB m -> gc_P c L RNG (set_outfile o s) FB m)
    /\ (forall L (s : PS) FB a, gc_dom c L s FB a -> ~ (OUTFILE_ADDR <= a < OUTFILE_ADDR + 8)).

  #[using="Type"] Lemma gconj_app : forall cs1 cs2 L RNG (s : PS) FB (m : mem),
    gconj (cs1 ++ cs2) L RNG s FB m <-> gconj cs1 L RNG s FB m /\ gconj cs2 L RNG s FB m.
  Proof.
    induction cs1 as [|c cs1 IH]; intros cs2 L RNG s FB m; cbn [app gconj]; [tauto|]. rewrite IH. tauto.
  Qed.

  Section HarnLaws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis INDEP : Forall harn_indep (cs1 ++ cs2).
    #[local] Notation GSTAT := (GSTAT_of (cs1 ++ harn_comp :: cs2)).

    #[using="Type"] Lemma gh_outfile_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA_real AI GSTAT L RNG s CL FB FL m ->
      match ps_outfile s with
      | None => rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
      | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
      end.
    Proof.
      intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 GC).
    Qed.

    #[using="CI_HARN CSOK INDEP"] Lemma gh_set_outfile_real : forall L RNG (s : PS) CL FB FL (m m' : mem) (o : option aptr), GIOA_real AI GSTAT L RNG s CL FB FL m -> ps_outfile s = None ->
      match o with
      | None => rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
      | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
      end ->
      munch [(OUTFILE_ADDR, OUTFILE_ADDR + 8)] m m' -> wmono asegs m m' ->
      GIOA_real AI GSTAT L RNG (set_outfile o s) CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' o G EO HC MU WM. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [_ GC2].
      assert (OUT : forall (P : Z -> Prop), (forall a, P a -> ~ (OUTFILE_ADDR <= a < OUTFILE_ADDR + 8)) -> agrees_on P m m').
      { intros P HP. apply (agrees_on_of_munch _ [(OUTFILE_ADDR, OUTFILE_ADDR + 8)]); [exact MU| exact WM|].
        intros a _ Pa. cbn [outside fst snd]. split; [exact (HP a Pa)| exact I]. }
      assert (COMP : forall cs, Forall (gcomp_ok AI) cs -> Forall harn_indep cs -> gconj cs L RNG s FB m -> gconj cs L RNG (set_outfile o s) FB m').
      { intros cs OKs INs GCs. eapply gconj_map; [exact GCs|]. intros c Hc PC.
        pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. destruct (proj1 (Forall_forall _ _) INs c Hc) as [I1 I2].
        apply I1. eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply OUT. intros a Da. exact (I2 _ _ _ _ Da). }
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in INDEP as [IN1 IN2].
      split.
      { cbn [ps_heap set_outfile]. eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. constructor; [| constructor]. left.
        destruct CI_HARN as (iv & Hiv & I1 & I2). left. right. left. exists iv. split; [exact Hiv|]. cbn [fst snd]. lia. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split.
      { eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        apply OUT. intros a Ha. pose proof ATPv_img as TI. unfold ATP, OUTFILE_ADDR in *. lia. }
      apply gconj_app. split; [exact (COMP cs1 OK1 IN1 GC1)|]. cbn [gconj]. split; [| exact (COMP cs2 OK2 IN2 GC2)].
      cbn [gc_P harn_comp]. unfold harn_P. cbn [ps_outfile set_outfile]. exact HC.
    Qed.

    #[using="CI_HARN CSOK INDEP"] Theorem gia_harn_laws_real : gia_harn_laws (GIOA_real AI GSTAT).
    Proof. constructor; [exact gh_outfile_real| exact gh_set_outfile_real]. Qed.
  End HarnLaws.
End Harn.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Harn.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_HARN : exists iv, In iv (aci AI) /\ fst iv <= OUTFILE_ADDR /\ OUTFILE_ADDR + 8 <= snd iv.

  Definition harn_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    match ps_outfile s with
    | None => rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
    | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
    end.
  Definition harn_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := OUTFILE_ADDR <= a < OUTFILE_ADDR + 8.
  Definition harn_comp : gcomp := mkGC harn_P harn_dom.

  #[using="AF CI_HARN"] Lemma harn_ok : gcomp_ok AI harn_comp.
  Proof.
    constructor; cbn [gc_P gc_dom harn_comp]; unfold harn_P, harn_dom.
    - intros L RNG RNG' s s' FB m m' HPm _ AG _ EO _. rewrite EO.
      destruct (ps_outfile s) as [q|].
      + (nd_pre HPm 3%nat; intros A HA HC; nd_post). exists A. split; [exact HA|]. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. unfold harn_dom. lia.
      + eapply agrees_rw_cells; [exact AG| exact HPm|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. unfold harn_dom. lia.
    - intros L RNG s FB m LB SP a _ _ _ _ Da. left. right. left. destruct CI_HARN as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (img_not_client AI AF); [exact AH|]. unfold OUTFILE_ADDR, AIMG_HI in *. lia.
    - intros L s FB a Da [X|X]; unfold OUTFILE_ADDR, READ_STAGE in *; [lia|]. pose proof ATPv_img as TI. unfold ATP in X. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition harn_indep (c : gcomp) : Prop :=
    (forall L RNG (s : PS) FB (m : mem) o, gc_P c L RNG s FB m -> gc_P c L RNG (set_outfile o s) FB m)
    /\ (forall L (s : PS) FB a, gc_dom c L s FB a -> ~ (OUTFILE_ADDR <= a < OUTFILE_ADDR + 8)).

  #[using="Type"] Lemma gconj_app : forall cs1 cs2 L RNG (s : PS) FB (m : mem),
    gconj (cs1 ++ cs2) L RNG s FB m <-> gconj cs1 L RNG s FB m /\ gconj cs2 L RNG s FB m.
  Proof.
    induction cs1 as [|c cs1 IH]; intros cs2 L RNG s FB m; cbn [app gconj]; [tauto|]. rewrite IH. tauto.
  Qed.

  Section HarnLaws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis INDEP : Forall harn_indep (cs1 ++ cs2).
    #[local] Notation GSTAT := (GSTAT_of (cs1 ++ harn_comp :: cs2)).

    #[using="Type"] Lemma gh_outfile_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA_real AI GSTAT L RNG s CL FB FL m ->
      match ps_outfile s with
      | None => rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
      | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
      end.
    Proof.
      intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 GC).
    Qed.

    #[using="CI_HARN CSOK INDEP"] Lemma gh_set_outfile_real : forall L RNG (s : PS) CL FB FL (m m' : mem) (o : option aptr), GIOA_real AI GSTAT L RNG s CL FB FL m -> ps_outfile s = None ->
      match o with
      | None => rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
      | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
      end ->
      munch [(OUTFILE_ADDR, OUTFILE_ADDR + 8)] m m' -> wmono asegs m m' ->
      GIOA_real AI GSTAT L RNG (set_outfile o s) CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' o G EO HC MU WM. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [_ GC2].
      assert (OUT : forall (P : Z -> Prop), (forall a, P a -> ~ (OUTFILE_ADDR <= a < OUTFILE_ADDR + 8)) -> agrees_on P m m').
      { intros P HP. apply (agrees_on_of_munch _ [(OUTFILE_ADDR, OUTFILE_ADDR + 8)]); [exact MU| exact WM|].
        intros a _ Pa. cbn [outside fst snd]. split; [exact (HP a Pa)| exact I]. }
      assert (COMP : forall cs, Forall (gcomp_ok AI) cs -> Forall harn_indep cs -> gconj cs L RNG s FB m -> gconj cs L RNG (set_outfile o s) FB m').
      { intros cs OKs INs GCs. eapply gconj_map; [exact GCs|]. intros c Hc PC.
        pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. destruct (proj1 (Forall_forall _ _) INs c Hc) as [I1 I2].
        apply I1. eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply OUT. intros a Da. exact (I2 _ _ _ _ Da). }
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in INDEP as [IN1 IN2].
      split.
      { cbn [ps_heap set_outfile]. eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. constructor; [| constructor]. left.
        destruct CI_HARN as (iv & Hiv & I1 & I2). left. right. left. exists iv. split; [exact Hiv|]. cbn [fst snd]. lia. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split.
      { eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        apply OUT. intros a Ha. pose proof ATPv_img as TI. unfold ATP, OUTFILE_ADDR in *. lia. }
      apply gconj_app. split; [exact (COMP cs1 OK1 IN1 GC1)|]. cbn [gconj]. split; [| exact (COMP cs2 OK2 IN2 GC2)].
      cbn [gc_P harn_comp]. unfold harn_P. cbn [ps_outfile set_outfile]. exact HC.
    Qed.

    #[using="CI_HARN CSOK INDEP"] Theorem gia_harn_laws_real : gia_harn_laws (GIOA_real AI GSTAT).
    Proof. constructor; [exact gh_outfile_real| exact gh_set_outfile_real]. Qed.
  End HarnLaws.
End Harn.
End CANSEC1.
End TwB.
