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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto AMalloc_iface AFake_iface AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA StdioLawsA StdioCompA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_glue_foKitA__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strerrA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA ExitHeapA GStatKit DrvStatA StaticsA TlsObjA HarnCompA StdioLawsInstA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section StrerrInst.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_LOC : exists iv, In iv (aci AI) /\ fst iv <= 0x6018a8 /\ 0x6018b0 <= snd iv.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition strerr_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
       rw_cells asegs m (ATP + -48) [C8 (Z_to_bv 64 0x601880)]
    /\ rw_cells asegs m 0x6018a8 [C8 (Z_to_bv 64 0)]
    /\ exists old, rw_cells asegs m (ATP + 20) [CB 256 old].
  Definition strerr_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop :=
    (ATP + -48 <= a < ATP + -40) \/ (0x6018a8 <= a < 0x6018b0) \/ (ATP + 20 <= a < ATP + 276).
  Definition strerr_comp : gcomp := mkGC strerr_P strerr_dom.

  #[using="AF AI_block_tls CI_LOC"] Lemma strerr_ok : gcomp_ok AI strerr_comp.
  Proof.
    constructor; cbn [gc_P gc_dom strerr_comp]; unfold strerr_P, strerr_dom.
    - intros L RNG RNG' s s' FB m m' (P1 & P2 & [old P3]) _ AG _ _ _.
      split; [eapply agrees_rw_cells; [exact AG| exact P1|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; left; lia|].
      split; [eapply agrees_rw_cells; [exact AG| exact P2|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; left; lia|].
      exists old. eapply agrees_rw_cells; [exact AG| exact P3|]. cbn [cells_size csize Nat.add]. intros a Ha. right; right. lia.
    - intros L RNG s FB m LB SP a _ _ _ _ [K|[K|K]].
      + right. left. left. unfold ATP in K. lia.
      + left. right. left. destruct CI_LOC as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
      + right. left. left. unfold ATP in K. lia.
    - intros L RNG s CL FB FL m a AH _ Ha [K|[K|K]] REG.
      + eapply (tls_not_client AI AF AI_block_tls); [exact AH| | exact REG]. lia.
      + eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      + eapply (tls_not_client AI AF AI_block_tls); [exact AH| | exact REG]. lia.
    - intros L s FB a [K|[K|K]] [D|D]; unfold READ_STAGE in D; pose proof ATPv_img as TI; unfold ATP in *; lia.
  Qed.

  #[using="AI_block_tls"] Lemma strerr_stdio_indep : stdio_indep AI strerr_comp.
  Proof.
    constructor; cbn [gc_P gc_dom strerr_comp]; unfold strerr_P, strerr_dom.
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da X. unfold stdio_static in X. pose proof ATPv_img as TI. unfold ATP in *. lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. destruct Da as [D|[D|D]].
      + apply in_block_In in K as (b & Hb & Rb).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as T. unfold hb_of in T. cbn [ab_addr ab_size] in T. lia.
      + destruct (fb_block_band AI _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; lia.
      + apply in_block_In in K as (b & Hb & Rb).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as T. unfold hb_of in T. cbn [ab_addr ab_size] in T. lia.
  Qed.

  #[using="Type"] Lemma strerr_harn_indep : harn_indep strerr_comp.
  Proof.
    split; cbn [gc_P gc_dom strerr_comp]; unfold strerr_P, strerr_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a Da R. unfold OUTFILE_ADDR in R. pose proof ATPv_img as TI. unfold ATP in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition tlsbuf_indep (c : gcomp) : Prop :=
    forall L RNG (s : PS) FB (m : mem) a, gc_P c L RNG s FB m -> gc_dom c L s FB a -> ~ (ATP + 16 <= a < ATP + 276).

  (* [comment removed for export] *)
  #[using="Type"] Lemma tlsbuf_of_band : forall (c : gcomp),
    (forall L (s : PS) FB a, gc_dom c L s FB a -> (0x10000 <= a < 0x603000 /\ (a < 0x5e14f0 \/ 0x5e24f0 <= a)) \/ (0x7fff7000 <= a < 0x10007fff8000)) -> tlsbuf_indep c.
  Proof.
    intros c BAND L RNG s FB m a _ Da K. pose proof ATPv_img as TI. pose proof ATPv_sh as TS. unfold ATP in K.
    destruct (BAND L s FB a Da) as [B|B]; lia.
  Qed.

  #[using="Type"] Lemma args_tlsbuf : forall USP n, ATOP + 64 <= USP -> 0 <= n -> USP + n + 8 <= 2^47 -> tlsbuf_indep (args_comp USP n).
  Proof.
    intros USP n G1 G2 G3. apply tlsbuf_of_band. cbn [gc_dom args_comp]. intros L s FB a Da. right.
    destruct (args_dom_band USP n G1 G3 a Da) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma unp_tlsbuf : tlsbuf_indep unp_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom unp_comp]. intros L s FB a Da. right. unfold unp_dom, AIMSH_LO, AIMSH_LEN in Da. lia. Qed.
  #[using="Type"] Lemma globals_tlsbuf : tlsbuf_indep globals_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom globals_comp]. intros L s FB a Da. right. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia. Qed.
  #[using="Type"] Lemma stdinp_tlsbuf : tlsbuf_indep stdinp_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom stdinp_comp]. intros L s FB a Da. right. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia. Qed.
  #[using="Type"] Lemma stacksh_tlsbuf : tlsbuf_indep stacksh_comp.
  Proof.
    apply tlsbuf_of_band. cbn [gc_dom stacksh_comp]. intros L s FB a [Da D47]. right.
    destruct (stacksh_band L a Da D47) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma tlsobj_tlsbuf : tlsbuf_indep tlsobj_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom tlsobj_comp]. intros L s FB a Da. right. destruct (tlsobj_band a Da) as (B & _). lia. Qed.
  #[using="Type"] Lemma harn_tlsbuf : tlsbuf_indep harn_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom harn_comp]. intros L s FB a Da. left. unfold harn_dom, OUTFILE_ADDR in Da. lia. Qed.
  #[using="Type"] Lemma exitci_tlsbuf : tlsbuf_indep exitci_comp.
  Proof.
    intros L RNG s FB m a _ Da K. cbn [gc_dom exitci_comp] in Da. unfold exitci_dom, exit_dom in Da. pose proof ATPv_img as TI. pose proof ATPv_sh as TS.
    unfold ATP in K. destruct Da as [D|[(k & Hk & Rk)|D]]; [lia| | unfold AIMSH_LO, AIMSH_LEN in D; lia].
    unfold EXIT_CI_KEEP in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
  Qed.
  #[using="Type"] Lemma files_tlsbuf : tlsbuf_indep (files_comp).
  Proof.
    intros L RNG s FB m a _ Da K. cbn [gc_dom files_comp] in Da. unfold files_dom in Da. pose proof ATPv_img as TI. unfold ATP in K.
    destruct Da as [D|[_ [N1 N2]]]; [unfold stdio_static in D; lia|]. apply N2. unfold ATP. lia.
  Qed.
  #[using="Type"] Lemma env_tlsbuf : tlsbuf_indep env_comp.
  Proof.
    intros L RNG s FB m a _ Da K. cbn [gc_dom env_comp] in Da. unfold env_dom in Da. pose proof ATPv_img as TI. pose proof ATPv_sh as TS. unfold ATP in K.
    destruct Da as [D|[D|[_ [N1 N2]]]].
    - destruct (env_cell_img a D) as (B & B2 & _). lia.
    - unfold AIMSH_LO, AIMSH_LEN in D. lia.
    - apply N2. unfold ATP. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells asegs m (ATP + 16) [C4 (Z_to_bv 64 0)].

  Section Laws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis TIND : Forall tlsbuf_indep (cs1 ++ cs2).
    #[local] Notation GSTAT := (GSTAT_of (cs1 ++ strerr_comp :: cs2)).
    #[local] Notation GIOA := (GIOA_real AI GSTAT).

    #[using="Type"] Lemma g_strerr : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> strerr_P L RNG s FB m.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 GC). Qed.

    #[using="AI_lsan"] Lemma ge_cells_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> strerr_cells m.
    Proof.
      intros L RNG s CL FB FL m G. pose proof G as (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      (nd_pre (g_strerr _ _ _ _ _ _ _ G) 3%nat; intros P1 P2 P3; nd_post).
      unfold strerr_cells, GLOBAL_LOCALE, PCAP_TLS_ERRBUF.
      split. { apply (relro_word m _ _ RO); [unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. }
      split; [exact (AI_lsan _ _ _ _ _ AH)|]. split; [exact P1|]. split; [exact P2| exact P3].
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma ser_outside_split : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
    Proof.
      induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn [app outside] in *; [split; [exact I| exact H]|].
      destruct H as [H1 H2]. destruct (IH W2 x H2) as [A B]. split; [split; [exact H1| exact A]| exact B].
    Qed.

    (* [comment removed for export] *)
    #[using="CSOK TIND"] Lemma strerr_frame_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W SP new,
      GIOA L RNG s CL FB FL m -> munch (W ++ [(ATP + 16, ATP + 20 + 256)]) m m' -> wmono asegs m m' ->
      Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
      rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
      rw_cells asegs m' (ATP + 20) [CB 256 new] ->
      GIOA L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W SP new G MU WM FW HSP LS NEW. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [(P1 & P2 & _) GC2].
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in TIND as [TI1 TI2].
      (* [comment removed for export] *)
      assert (OUT : forall c, gcomp_ok AI c -> tlsbuf_indep c -> gc_P c L RNG s FB m -> forall a, 0 <= a < 2^64 -> gc_dom c L s FB a ->
                      outside (W ++ [(ATP + 16, ATP + 20 + 256)]) a).
      { intros c OK TI PC a Ha Da. apply outside_app2.
        - apply outside_of. intros iv Hi Ra. pose proof (proj1 (Forall_forall _ _) FW iv Hi) as [K1 K2].
          apply (gk_client AI c OK _ _ _ _ _ _ _ _ AH PC Ha Da). left. lia.
        - cbn [outside]. split; [| exact I]. intros Ra. apply (TI _ _ _ _ _ _ PC Da). lia. }
      assert (STEP : forall cs, Forall (gcomp_ok AI) cs -> Forall tlsbuf_indep cs -> gconj cs L RNG s FB m -> gconj cs L RNG s FB m').
      { intros cs OKs TIs GCs. eapply gconj_map; [exact GCs|]. intros c Hc PC.
        pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. pose proof (proj1 (Forall_forall _ _) TIs c Hc) as TI.
        eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply (agrees_on_of_munch _ (W ++ [(ATP + 16, ATP + 20 + 256)])); [exact MU| exact WM|]. intros a Ha Da. exact (OUT c OK TI PC a Ha Da). }
      assert (AGT : agrees_on (fun a => (ATP + -164 <= a < ATP + -160) \/ (ATP + -48 <= a < ATP + -40) \/ (0x6018a8 <= a < 0x6018b0)) m m').
      { apply (agrees_on_of_munch _ (W ++ [(ATP + 16, ATP + 20 + 256)])); [exact MU| exact WM|]. intros a Ha Da.
        pose proof ATPv_img as TI. pose proof atp_lin as ((TL & _) & _). apply outside_app2.
        - apply outside_of. intros iv Hi Ra. pose proof (proj1 (Forall_forall _ _) FW iv Hi) as [K1 K2]. pose proof atop_range as AR. unfold ATP in *. lia.
        - cbn [outside]. split; [| exact I]. unfold ATP in *. lia. }
      (* [comment removed for export] *)
      assert (MU' : munch ((W ++ [(ATP + 20, ATP + 20 + 256)]) ++ [(ATP + 16, ATP + 20)]) m m').
      { eapply munch_weaken; [| exact MU]. intros x Hx. apply ser_outside_split in Hx as [Hx H3]. apply ser_outside_split in Hx as [HW H2].
        apply outside_app2; [exact HW|]. cbn [outside] in H2, H3 |- *. destruct H2 as [H2 _]. destruct H3 as [H3 _]. split; [lia| exact I]. }
      split.
      { eapply (AI_frame_lsan AI); [exact AH| exact MU'| exact WM| | exact LS]. apply Forall_app. split.
        - eapply Forall_impl; [| exact FW]. intros iv [K1 K2]. left. left. left. exact K1.
        - constructor; [| constructor]. right. left. cbn [fst snd]. unfold atls_client, ATP. right; right. lia. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split.
      { destruct ERR as [e0 ERR]. exists e0. eapply agrees_rw_cells; [exact AGT| exact ERR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. left. lia. }
      apply gconj_app. split; [exact (STEP cs1 OK1 TI1 GC1)|]. cbn [gconj]. split; [| exact (STEP cs2 OK2 TI2 GC2)].
      cbn [gc_P strerr_comp]. unfold strerr_P.
      split; [eapply agrees_rw_cells; [exact AGT| exact P1|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; left; lia|].
      split; [eapply agrees_rw_cells; [exact AGT| exact P2|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; right; lia|].
      exists new. exact NEW.
    Qed.
  End Laws.
End StrerrInst.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strerrA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section StrerrInst.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_LOC : exists iv, In iv (aci AI) /\ fst iv <= 0x601ca8 /\ 0x601cb0 <= snd iv.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition strerr_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
       rw_cells asegs m (ATP + -48) [C8 (Z_to_bv 64 0x601c80)]
    /\ rw_cells asegs m 0x601ca8 [C8 (Z_to_bv 64 0)]
    /\ exists old, rw_cells asegs m (ATP + 20) [CB 256 old].
  Definition strerr_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop :=
    (ATP + -48 <= a < ATP + -40) \/ (0x601ca8 <= a < 0x601cb0) \/ (ATP + 20 <= a < ATP + 276).
  Definition strerr_comp : gcomp := mkGC strerr_P strerr_dom.

  #[using="AF AI_block_tls CI_LOC"] Lemma strerr_ok : gcomp_ok AI strerr_comp.
  Proof.
    constructor; cbn [gc_P gc_dom strerr_comp]; unfold strerr_P, strerr_dom.
    - intros L RNG RNG' s s' FB m m' (P1 & P2 & [old P3]) _ AG _ _ _.
      split; [eapply agrees_rw_cells; [exact AG| exact P1|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; left; lia|].
      split; [eapply agrees_rw_cells; [exact AG| exact P2|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; left; lia|].
      exists old. eapply agrees_rw_cells; [exact AG| exact P3|]. cbn [cells_size csize Nat.add]. intros a Ha. right; right. lia.
    - intros L RNG s FB m LB SP a _ _ _ _ [K|[K|K]].
      + right. left. left. unfold ATP in K. lia.
      + left. right. left. destruct CI_LOC as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
      + right. left. left. unfold ATP in K. lia.
    - intros L RNG s CL FB FL m a AH _ Ha [K|[K|K]] REG.
      + eapply (tls_not_client AI AF AI_block_tls); [exact AH| | exact REG]. lia.
      + eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      + eapply (tls_not_client AI AF AI_block_tls); [exact AH| | exact REG]. lia.
    - intros L s FB a [K|[K|K]] [D|D]; unfold READ_STAGE in D; pose proof ATPv_img as TI; unfold ATP in *; lia.
  Qed.

  #[using="AI_block_tls"] Lemma strerr_stdio_indep : stdio_indep AI strerr_comp.
  Proof.
    constructor; cbn [gc_P gc_dom strerr_comp]; unfold strerr_P, strerr_dom.
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da X. unfold stdio_static in X. pose proof ATPv_img as TI. unfold ATP in *. lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. destruct Da as [D|[D|D]].
      + apply in_block_In in K as (b & Hb & Rb).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as T. unfold hb_of in T. cbn [ab_addr ab_size] in T. lia.
      + destruct (fb_block_band AI _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; lia.
      + apply in_block_In in K as (b & Hb & Rb).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as T. unfold hb_of in T. cbn [ab_addr ab_size] in T. lia.
  Qed.

  #[using="Type"] Lemma strerr_harn_indep : harn_indep strerr_comp.
  Proof.
    split; cbn [gc_P gc_dom strerr_comp]; unfold strerr_P, strerr_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a Da R. unfold OUTFILE_ADDR in R. pose proof ATPv_img as TI. unfold ATP in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition tlsbuf_indep (c : gcomp) : Prop :=
    forall L RNG (s : PS) FB (m : mem) a, gc_P c L RNG s FB m -> gc_dom c L s FB a -> ~ (ATP + 16 <= a < ATP + 276).

  (* [comment removed for export] *)
  #[using="Type"] Lemma tlsbuf_of_band : forall (c : gcomp),
    (forall L (s : PS) FB a, gc_dom c L s FB a -> (0x10000 <= a < 0x604000 /\ (a < 0x5e18f0 \/ 0x5e28f0 <= a)) \/ (0x7fff7000 <= a < 0x10007fff8000)) -> tlsbuf_indep c.
  Proof.
    intros c BAND L RNG s FB m a _ Da K. pose proof ATPv_img as TI. pose proof ATPv_sh as TS. unfold ATP in K.
    destruct (BAND L s FB a Da) as [B|B]; lia.
  Qed.

  #[using="Type"] Lemma args_tlsbuf : forall USP n, ATOP + 64 <= USP -> 0 <= n -> USP + n + 8 <= 2^47 -> tlsbuf_indep (args_comp USP n).
  Proof.
    intros USP n G1 G2 G3. apply tlsbuf_of_band. cbn [gc_dom args_comp]. intros L s FB a Da. right.
    destruct (args_dom_band USP n G1 G3 a Da) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma unp_tlsbuf : tlsbuf_indep unp_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom unp_comp]. intros L s FB a Da. right. unfold unp_dom, AIMSH_LO, AIMSH_LEN in Da. lia. Qed.
  #[using="Type"] Lemma globals_tlsbuf : tlsbuf_indep globals_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom globals_comp]. intros L s FB a Da. right. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia. Qed.
  #[using="Type"] Lemma stdinp_tlsbuf : tlsbuf_indep stdinp_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom stdinp_comp]. intros L s FB a Da. right. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia. Qed.
  #[using="Type"] Lemma stacksh_tlsbuf : tlsbuf_indep stacksh_comp.
  Proof.
    apply tlsbuf_of_band. cbn [gc_dom stacksh_comp]. intros L s FB a [Da D47]. right.
    destruct (stacksh_band L a Da D47) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma tlsobj_tlsbuf : tlsbuf_indep tlsobj_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom tlsobj_comp]. intros L s FB a Da. right. destruct (tlsobj_band a Da) as (B & _). lia. Qed.
  #[using="Type"] Lemma harn_tlsbuf : tlsbuf_indep harn_comp.
  Proof. apply tlsbuf_of_band. cbn [gc_dom harn_comp]. intros L s FB a Da. left. unfold harn_dom, OUTFILE_ADDR in Da. lia. Qed.
  #[using="Type"] Lemma exitci_tlsbuf : tlsbuf_indep exitci_comp.
  Proof.
    intros L RNG s FB m a _ Da K. cbn [gc_dom exitci_comp] in Da. unfold exitci_dom, exit_dom in Da. pose proof ATPv_img as TI. pose proof ATPv_sh as TS.
    unfold ATP in K. destruct Da as [D|[(k & Hk & Rk)|D]]; [lia| | unfold AIMSH_LO, AIMSH_LEN in D; lia].
    unfold EXIT_CI_KEEP in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
  Qed.
  #[using="Type"] Lemma files_tlsbuf : tlsbuf_indep (files_comp).
  Proof.
    intros L RNG s FB m a _ Da K. cbn [gc_dom files_comp] in Da. unfold files_dom in Da. pose proof ATPv_img as TI. unfold ATP in K.
    destruct Da as [D|[_ [N1 N2]]]; [unfold stdio_static in D; lia|]. apply N2. unfold ATP. lia.
  Qed.
  #[using="Type"] Lemma env_tlsbuf : tlsbuf_indep env_comp.
  Proof.
    intros L RNG s FB m a _ Da K. cbn [gc_dom env_comp] in Da. unfold env_dom in Da. pose proof ATPv_img as TI. pose proof ATPv_sh as TS. unfold ATP in K.
    destruct Da as [D|[D|[_ [N1 N2]]]].
    - destruct (env_cell_img a D) as (B & B2 & _). lia.
    - unfold AIMSH_LO, AIMSH_LEN in D. lia.
    - apply N2. unfold ATP. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells asegs m (ATP + 16) [C4 (Z_to_bv 64 0)].

  Section Laws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis TIND : Forall tlsbuf_indep (cs1 ++ cs2).
    #[local] Notation GSTAT := (GSTAT_of (cs1 ++ strerr_comp :: cs2)).
    #[local] Notation GIOA := (GIOA_real AI GSTAT).

    #[using="Type"] Lemma g_strerr : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> strerr_P L RNG s FB m.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 GC). Qed.

    #[using="AI_lsan"] Lemma ge_cells_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> strerr_cells m.
    Proof.
      intros L RNG s CL FB FL m G. pose proof G as (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      (nd_pre (g_strerr _ _ _ _ _ _ _ G) 3%nat; intros P1 P2 P3; nd_post).
      unfold strerr_cells, GLOBAL_LOCALE, PCAP_TLS_ERRBUF.
      split. { apply (relro_word m _ _ RO); [unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. }
      split; [exact (AI_lsan _ _ _ _ _ AH)|]. split; [exact P1|]. split; [exact P2| exact P3].
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma ser_outside_split : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
    Proof.
      induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn [app outside] in *; [split; [exact I| exact H]|].
      destruct H as [H1 H2]. destruct (IH W2 x H2) as [A B]. split; [split; [exact H1| exact A]| exact B].
    Qed.

    (* [comment removed for export] *)
    #[using="CSOK TIND"] Lemma strerr_frame_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W SP new,
      GIOA L RNG s CL FB FL m -> munch (W ++ [(ATP + 16, ATP + 20 + 256)]) m m' -> wmono asegs m m' ->
      Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
      rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
      rw_cells asegs m' (ATP + 20) [CB 256 new] ->
      GIOA L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W SP new G MU WM FW HSP LS NEW. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [(P1 & P2 & _) GC2].
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in TIND as [TI1 TI2].
      (* [comment removed for export] *)
      assert (OUT : forall c, gcomp_ok AI c -> tlsbuf_indep c -> gc_P c L RNG s FB m -> forall a, 0 <= a < 2^64 -> gc_dom c L s FB a ->
                      outside (W ++ [(ATP + 16, ATP + 20 + 256)]) a).
      { intros c OK TI PC a Ha Da. apply outside_app2.
        - apply outside_of. intros iv Hi Ra. pose proof (proj1 (Forall_forall _ _) FW iv Hi) as [K1 K2].
          apply (gk_client AI c OK _ _ _ _ _ _ _ _ AH PC Ha Da). left. lia.
        - cbn [outside]. split; [| exact I]. intros Ra. apply (TI _ _ _ _ _ _ PC Da). lia. }
      assert (STEP : forall cs, Forall (gcomp_ok AI) cs -> Forall tlsbuf_indep cs -> gconj cs L RNG s FB m -> gconj cs L RNG s FB m').
      { intros cs OKs TIs GCs. eapply gconj_map; [exact GCs|]. intros c Hc PC.
        pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. pose proof (proj1 (Forall_forall _ _) TIs c Hc) as TI.
        eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply (agrees_on_of_munch _ (W ++ [(ATP + 16, ATP + 20 + 256)])); [exact MU| exact WM|]. intros a Ha Da. exact (OUT c OK TI PC a Ha Da). }
      assert (AGT : agrees_on (fun a => (ATP + -164 <= a < ATP + -160) \/ (ATP + -48 <= a < ATP + -40) \/ (0x601ca8 <= a < 0x601cb0)) m m').
      { apply (agrees_on_of_munch _ (W ++ [(ATP + 16, ATP + 20 + 256)])); [exact MU| exact WM|]. intros a Ha Da.
        pose proof ATPv_img as TI. pose proof atp_lin as ((TL & _) & _). apply outside_app2.
        - apply outside_of. intros iv Hi Ra. pose proof (proj1 (Forall_forall _ _) FW iv Hi) as [K1 K2]. pose proof atop_range as AR. unfold ATP in *. lia.
        - cbn [outside]. split; [| exact I]. unfold ATP in *. lia. }
      (* [comment removed for export] *)
      assert (MU' : munch ((W ++ [(ATP + 20, ATP + 20 + 256)]) ++ [(ATP + 16, ATP + 20)]) m m').
      { eapply munch_weaken; [| exact MU]. intros x Hx. apply ser_outside_split in Hx as [Hx H3]. apply ser_outside_split in Hx as [HW H2].
        apply outside_app2; [exact HW|]. cbn [outside] in H2, H3 |- *. destruct H2 as [H2 _]. destruct H3 as [H3 _]. split; [lia| exact I]. }
      split.
      { eapply (AI_frame_lsan AI); [exact AH| exact MU'| exact WM| | exact LS]. apply Forall_app. split.
        - eapply Forall_impl; [| exact FW]. intros iv [K1 K2]. left. left. left. exact K1.
        - constructor; [| constructor]. right. left. cbn [fst snd]. unfold atls_client, ATP. right; right. lia. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split.
      { destruct ERR as [e0 ERR]. exists e0. eapply agrees_rw_cells; [exact AGT| exact ERR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. left. lia. }
      apply gconj_app. split; [exact (STEP cs1 OK1 TI1 GC1)|]. cbn [gconj]. split; [| exact (STEP cs2 OK2 TI2 GC2)].
      cbn [gc_P strerr_comp]. unfold strerr_P.
      split; [eapply agrees_rw_cells; [exact AGT| exact P1|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; left; lia|].
      split; [eapply agrees_rw_cells; [exact AGT| exact P2|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; right; lia|].
      exists new. exact NEW.
    Qed.
  End Laws.
End StrerrInst.
End CANSEC1.
End TwB.
