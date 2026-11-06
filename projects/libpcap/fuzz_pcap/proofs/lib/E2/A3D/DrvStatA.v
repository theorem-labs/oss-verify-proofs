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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto AMalloc_iface AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA ExitAllA ExitHeapA GStatKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section DrvStat.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Args.
    Variables (USP n : Z).
    Hypothesis USP_lo : ATOP + 64 <= USP.
    Hypothesis USP_n : 0 <= n.
    Hypothesis USP_hi : USP + n + 8 <= 2^47.
    Definition ARGS_LO : Z := 64 * (USP / 64).
    Definition ARGS_HI : Z := 64 * ((USP + n + 63) / 64).
    Definition args_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
      unpoisoned m USP (USP + n) /\ rng RNG USP n
      /\ wr_at asegs m (shad ARGS_LO) (shad ARGS_HI - shad ARGS_LO) /\ rng RNG (shad ARGS_LO) (shad ARGS_HI - shad ARGS_LO).
    Definition args_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := shad ARGS_LO <= a < shad ARGS_HI.
    Definition args_comp : gcomp := mkGC args_P args_dom.

    #[using="rc"] Lemma args_sh : shad ARGS_LO = 2147450880 + 8 * (USP / 64) /\ shad ARGS_HI = 2147450880 + 8 * ((USP + n + 63) / 64).
    Proof. pose proof atop_range as AR. unfold ARGS_LO, ARGS_HI. rewrite !shad_div. unfold ASHOFF. split; Z.div_mod_to_equations; lia. Qed.

    #[using="rc USP_lo USP_n USP_hi"] Lemma args_mobjA : forall L RNG s FB m, args_P L RNG s FB m -> mobjA RNG m USP n.
    Proof.
      intros L RNG s FB m (U & R & W & RS). pose proof atop_range as AR. pose proof USP_hi as H47. change (2^47) with 140737488355328 in H47.
      split; [lia|]. split; [change (2^47) with 140737488355328; lia|]. split; [exact U|]. split; [exact R|]. split.
      - exists ARGS_LO, ARGS_HI. unfold KEND. unfold ARGS_LO, ARGS_HI in *.
        split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
        split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
        split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact W| exact RS].
      - unfold app_blk, KHIGH, KEND. split; [lia|]. right. split; lia.
    Qed.

    #[using="USP_lo USP_hi"] Lemma args_dom_band : forall a, shad ARGS_LO <= a < shad ARGS_HI -> ATOP / 8 + 2147450880 <= a < 0x10007fff8000 /\ ATOP <= 8 * (a - ASHOFF) < 2^47.
    Proof.
      intros a Ha. destruct args_sh as [E1 E2]. rewrite E1, E2 in Ha. pose proof atop_range as AR. pose proof USP_hi as H47.
      change (2^47) with 140737488355328 in *. unfold ASHOFF. clear - Ha USP_lo USP_n AR H47. Z.div_mod_to_equations. lia.
    Qed.

    #[using="AF USP_lo USP_hi"] Lemma args_ok : gcomp_ok AI args_comp.
    Proof.
      constructor; cbn [gc_P gc_dom args_comp].
      - intros L RNG RNG' s s' FB m m' (U & R & W & RS) FP AG _ _ _. destruct args_sh as [E1 E2]. pose proof atop_range as AR. pose proof USP_hi as H47.
        change (2^47) with 140737488355328 in H47.
        split.
        { eapply unpoisoned_agree; [exact U|]. intros sa Hs. apply AG.
          - rewrite !shad_div in Hs. unfold ASHOFF in Hs. clear - Hs USP_lo USP_n AR H47. Z.div_mod_to_equations. lia.
          - unfold args_dom. rewrite E1, E2. rewrite !shad_div in Hs. unfold ASHOFF in Hs. clear - Hs USP_lo USP_n AR H47. Z.div_mod_to_equations. lia. }
        split; [eapply rng_fp_le; [exact FP| exact R]|].
        split; [| eapply rng_fp_le; [exact FP| exact RS]].
        eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. unfold args_dom. lia.
      - intros L RNG s FB m LB SP a _ _ _ Ha Da. left. right. right. right.
        destruct (args_dom_band a Da) as [_ B]. exists (8 * (a - ASHOFF)). split; [left; exact B| symmetry; apply shad_unshad].
      - intros L RNG s CL FB FL m a AH _ Ha Da. eapply (stksh_not_client AI AF); [exact AH| exact (proj1 (args_dom_band a Da))].
      - intros L s FB a Da [D|D]; destruct (args_dom_band a Da) as [B _]; pose proof atop_range as AR.
        + unfold READ_STAGE in D. clear - D B AR. Z.div_mod_to_equations. lia.
        + pose proof ATPv_sh as TS. unfold ATP in D. clear - D B AR TS. Z.div_mod_to_equations. lia.
    Qed.
  End Args.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition unp_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    unpoisoned m DRV_RODATA_LO DRV_RODATA_HI /\ unpoisoned m READ_STAGE (READ_STAGE + 65536).
  Definition unp_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN.
  Definition unp_comp : gcomp := mkGC unp_P unp_dom.

  #[using="AF"] Lemma unp_ok : gcomp_ok AI unp_comp.
  Proof.
    constructor; cbn [gc_P gc_dom unp_comp].
    - intros L RNG RNG' s s' FB m m' (U1 & U2) _ AG _ _ _. split.
      + eapply unpoisoned_agree; [exact U1|]. intros sa Hs. apply AG; rewrite !shad_div in Hs; unfold ASHOFF, DRV_RODATA_LO, DRV_RODATA_HI in Hs;
          [| unfold unp_dom, AIMSH_LO, AIMSH_LEN]; clear - Hs; Z.div_mod_to_equations; lia.
      + eapply unpoisoned_agree; [exact U2|]. intros sa Hs. apply AG; rewrite !shad_div in Hs; unfold ASHOFF, READ_STAGE in Hs;
          [| unfold unp_dom, AIMSH_LO, AIMSH_LEN]; clear - Hs; Z.div_mod_to_equations; lia.
    - intros L RNG s FB m LB SP a _ _ _ _ Da. right. right. left. exact Da.
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (imsh_not_client AI AF); [exact AH| exact Da].
    - intros L s FB a Da. exact (imsh_not_drv a Da).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition exit_dom (a : Z) : Prop :=
    (ATPv + -168 <= a < ATPv + -164) \/ in_ranges EXIT_CI_KEEP a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN).
  Definition exitci_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := exists t, exit_ci t m.
  Definition exitci_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := exit_dom a.
  Definition exitci_comp : gcomp := mkGC exitci_P exitci_dom.

  #[using="Type"] Lemma descs_at_agree : forall (P : Z -> Prop) gs (m m' : mem) d, agrees_on P m m' -> (forall a, d <= a < d + 64 * Z.of_nat (length gs) -> P a) ->
    descs_at m d gs -> descs_at m' d gs.
  Proof.
    intros P gs. induction gs as [|g gs IH]; intros m m' d AG HP DA; cbn [descs_at] in *; [exact I|].
    destruct DA as [D DA]. cbn [length] in HP. split.
    - eapply agrees_rw_cells; [exact AG| exact D|]. rewrite gd_cells_size. intros a Ha. apply HP. lia.
    - eapply (IH m m' (d + 64) AG); [| exact DA]. intros a Ha. apply HP. lia.
  Qed.

  Local Ltac kin := first [left; reflexivity | right; kin].
  Local Ltac kca KC k := eapply (KC k); [unfold EXIT_CI_KEEP; kin| cbn; lia| cbn; lia| eassumption].

  #[using="Type"] Lemma exit_ci_agree : forall t (m m' : mem), exit_ci t m -> agrees_on exit_dom m m' -> exit_ci t m'.
  Proof.
    intros t m m' EC AG.
    assert (KC : forall k A cs, In k EXIT_CI_KEEP -> fst k <= A -> A + Z.of_nat (cells_size cs) <= snd k -> rw_cells asegs m A cs -> rw_cells asegs m' A cs).
    { intros k A cs Hk H1 H2 HC. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. right. left. exists k. split; [exact Hk| lia]. }
    assert (KW : forall A n, wr_at asegs m A n -> AIMSH_LO <= A -> A + n <= AIMSH_LO + AIMSH_LEN -> wr_at asegs m' A n).
    { intros A n HW H1 H2. eapply agrees_wr_at; [exact AG| exact HW|]. intros a Ha. right. right. lia. }
    (nd_pre EC 15%nat; intros TID EXL COV0 FINZ (dso & DSO) Ht RGL FLG MTX DA D69 (ob & OD) SH SH69 SHT; nd_post).
    unfold exit_ci.
    split. { eapply agrees_rw_cells; [exact AG| exact TID|]. intros a Ha. left. cbn [cells_size csize Nat.add] in Ha. lia. }
    split; [kca KC (0x601828, 0x60182c)|].
   
   
    split; [kca KC (0x1404a0, 0x1404a1)|]. split; [kca KC (0xaaf90, 0xaaf91)|].
    split; [exists dso; kca KC (0xa71d0, 0xa71d8)|]. split; [exact Ht|].
    split; [kca KC (0xabe10, 0xabe14)|]. split; [kca KC (0xaaf40, 0xaaf48)|]. split; [kca KC (0xabeb0, 0xabeb8)|].
    split. { eapply (descs_at_agree exit_dom); [exact AG| | exact DA]. intros a Ha. change (Z.of_nat (length GD69)) with 69 in Ha.
             right. left. exists (0xa9db0, 0xaaf30). split; [unfold EXIT_CI_KEEP; kin| cbn [fst snd]; lia]. }
    split; [kca KC (0xa9db0, 0xaaf30)|]. split; [exists ob; kca KC (0x5e0ca0, 0x5e0ca1)|].
    split.
    { apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) GD69_ok g Hg) as OKg. pose proof (proj1 (Forall_forall _ _) SH g Hg) as SHg.
      destruct g as ((((beg, sz), swr), nm), md). unfold gd_shw in *. (nd_pre OKg 4%nat; intros AL SWR BLO BHI; nd_post).
      assert (SWRf : swr mod 8 = 0 /\ 0 < swr) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
      destruct SWRf as [SL SZ]. (pose proof (shadow_window beg swr AL SL SZ BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
      apply KW; [exact SHg| unfold AIMSH_LO, SHW_LO in *; lia| unfold AIMSH_LO, AIMSH_LEN, SHW_LO, SHW_LEN in *; lia]. }
    split; (apply KW; [eassumption| vm_compute; discriminate| vm_compute; discriminate]).
  Qed.

  (* [comment removed for export] *)
  Hypothesis CI_EXIT : Forall (fun k => exists iv, In iv (aci AI) /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP.

  #[using="Type"] Lemma exit_keep_img : forall k, In k EXIT_CI_KEEP -> 0x10000 <= fst k /\ snd k <= 0x603000 /\ (snd k <= READ_STAGE \/ READ_STAGE + 65537 <= fst k)
    /\ (snd k <= 0x5e14f0 \/ 0x5e24f0 <= fst k).
  Proof.
    intros k Hk. unfold EXIT_CI_KEEP in Hk. unfold READ_STAGE.
    repeat (destruct Hk as [<-|Hk]; [cbn [fst snd]; lia|]). destruct Hk.
  Qed.

  #[using="AF AI_block_tls CI_EXIT"] Lemma exitci_ok : gcomp_ok AI exitci_comp.
  Proof.
    constructor; cbn [gc_P gc_dom exitci_comp]; unfold exitci_P, exitci_dom.
    - intros L RNG RNG' s s' FB m m' [t EC] _ AG _ _ _. exists t. eapply exit_ci_agree; eassumption.
    - intros L RNG s FB m LB SP a _ _ _ Ha [D|[(k & Hk & Rk)|D]].
      + right. left. left. lia.
      + left. right. left. (nd_pre (proj1 (Forall_forall _ _) CI_EXIT k Hk) 4%nat; intros iv Hiv I1 I2; nd_post). exists iv. split; [exact Hiv| lia].
      + right. right. left. exact D.
    - intros L RNG s CL FB FL m a AH _ Ha [D|[(k & Hk & Rk)|D]].
      + eapply (tls_not_client AI AF AI_block_tls); [exact AH| unfold ATP; lia].
      + eapply (img_not_client AI AF); [exact AH|]. (nd_pre (exit_keep_img k Hk) 4%nat; intros K1 K2 _ _; nd_post). unfold AIMG_HI. lia.
      + eapply (imsh_not_client AI AF); [exact AH| exact D].
    - intros L s FB a [D|[(k & Hk & Rk)|D]].
      + intros [X|X]; [pose proof ATPv_img as TI; unfold READ_STAGE in X; lia| unfold ATP in X; lia].
      + (nd_pre (exit_keep_img k Hk) 4%nat; intros K1 K2 K3 K4; nd_post). intros [X|X]; [lia|]. pose proof ATPv_img as TI. unfold ATP in X. lia.
      + exact (imsh_not_drv a D).
  Qed.
End DrvStat.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section DrvStat.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Args.
    Variables (USP n : Z).
    Hypothesis USP_lo : ATOP + 64 <= USP.
    Hypothesis USP_n : 0 <= n.
    Hypothesis USP_hi : USP + n + 8 <= 2^47.
    Definition ARGS_LO : Z := 64 * (USP / 64).
    Definition ARGS_HI : Z := 64 * ((USP + n + 63) / 64).
    Definition args_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
      unpoisoned m USP (USP + n) /\ rng RNG USP n
      /\ wr_at asegs m (shad ARGS_LO) (shad ARGS_HI - shad ARGS_LO) /\ rng RNG (shad ARGS_LO) (shad ARGS_HI - shad ARGS_LO).
    Definition args_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := shad ARGS_LO <= a < shad ARGS_HI.
    Definition args_comp : gcomp := mkGC args_P args_dom.

    #[using="rc"] Lemma args_sh : shad ARGS_LO = 2147450880 + 8 * (USP / 64) /\ shad ARGS_HI = 2147450880 + 8 * ((USP + n + 63) / 64).
    Proof. pose proof atop_range as AR. unfold ARGS_LO, ARGS_HI. rewrite !shad_div. unfold ASHOFF. split; Z.div_mod_to_equations; lia. Qed.

    #[using="rc USP_lo USP_n USP_hi"] Lemma args_mobjA : forall L RNG s FB m, args_P L RNG s FB m -> mobjA RNG m USP n.
    Proof.
      intros L RNG s FB m (U & R & W & RS). pose proof atop_range as AR. pose proof USP_hi as H47. change (2^47) with 140737488355328 in H47.
      split; [lia|]. split; [change (2^47) with 140737488355328; lia|]. split; [exact U|]. split; [exact R|]. split.
      - exists ARGS_LO, ARGS_HI. unfold KEND. unfold ARGS_LO, ARGS_HI in *.
        split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
        split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
        split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact W| exact RS].
      - unfold app_blk, KHIGH, KEND. split; [lia|]. right. split; lia.
    Qed.

    #[using="USP_lo USP_hi"] Lemma args_dom_band : forall a, shad ARGS_LO <= a < shad ARGS_HI -> ATOP / 8 + 2147450880 <= a < 0x10007fff8000 /\ ATOP <= 8 * (a - ASHOFF) < 2^47.
    Proof.
      intros a Ha. destruct args_sh as [E1 E2]. rewrite E1, E2 in Ha. pose proof atop_range as AR. pose proof USP_hi as H47.
      change (2^47) with 140737488355328 in *. unfold ASHOFF. clear - Ha USP_lo USP_n AR H47. Z.div_mod_to_equations. lia.
    Qed.

    #[using="AF USP_lo USP_hi"] Lemma args_ok : gcomp_ok AI args_comp.
    Proof.
      constructor; cbn [gc_P gc_dom args_comp].
      - intros L RNG RNG' s s' FB m m' (U & R & W & RS) FP AG _ _ _. destruct args_sh as [E1 E2]. pose proof atop_range as AR. pose proof USP_hi as H47.
        change (2^47) with 140737488355328 in H47.
        split.
        { eapply unpoisoned_agree; [exact U|]. intros sa Hs. apply AG.
          - rewrite !shad_div in Hs. unfold ASHOFF in Hs. clear - Hs USP_lo USP_n AR H47. Z.div_mod_to_equations. lia.
          - unfold args_dom. rewrite E1, E2. rewrite !shad_div in Hs. unfold ASHOFF in Hs. clear - Hs USP_lo USP_n AR H47. Z.div_mod_to_equations. lia. }
        split; [eapply rng_fp_le; [exact FP| exact R]|].
        split; [| eapply rng_fp_le; [exact FP| exact RS]].
        eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. unfold args_dom. lia.
      - intros L RNG s FB m LB SP a _ _ _ Ha Da. left. right. right. right.
        destruct (args_dom_band a Da) as [_ B]. exists (8 * (a - ASHOFF)). split; [left; exact B| symmetry; apply shad_unshad].
      - intros L RNG s CL FB FL m a AH _ Ha Da. eapply (stksh_not_client AI AF); [exact AH| exact (proj1 (args_dom_band a Da))].
      - intros L s FB a Da [D|D]; destruct (args_dom_band a Da) as [B _]; pose proof atop_range as AR.
        + unfold READ_STAGE in D. clear - D B AR. Z.div_mod_to_equations. lia.
        + pose proof ATPv_sh as TS. unfold ATP in D. clear - D B AR TS. Z.div_mod_to_equations. lia.
    Qed.
  End Args.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition unp_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    unpoisoned m DRV_RODATA_LO DRV_RODATA_HI /\ unpoisoned m READ_STAGE (READ_STAGE + 65536).
  Definition unp_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN.
  Definition unp_comp : gcomp := mkGC unp_P unp_dom.

  #[using="AF"] Lemma unp_ok : gcomp_ok AI unp_comp.
  Proof.
    constructor; cbn [gc_P gc_dom unp_comp].
    - intros L RNG RNG' s s' FB m m' (U1 & U2) _ AG _ _ _. split.
      + eapply unpoisoned_agree; [exact U1|]. intros sa Hs. apply AG; rewrite !shad_div in Hs; unfold ASHOFF, DRV_RODATA_LO, DRV_RODATA_HI in Hs;
          [| unfold unp_dom, AIMSH_LO, AIMSH_LEN]; clear - Hs; Z.div_mod_to_equations; lia.
      + eapply unpoisoned_agree; [exact U2|]. intros sa Hs. apply AG; rewrite !shad_div in Hs; unfold ASHOFF, READ_STAGE in Hs;
          [| unfold unp_dom, AIMSH_LO, AIMSH_LEN]; clear - Hs; Z.div_mod_to_equations; lia.
    - intros L RNG s FB m LB SP a _ _ _ _ Da. right. right. left. exact Da.
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (imsh_not_client AI AF); [exact AH| exact Da].
    - intros L s FB a Da. exact (imsh_not_drv a Da).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition exit_dom (a : Z) : Prop :=
    (ATPv + -168 <= a < ATPv + -164) \/ in_ranges EXIT_CI_KEEP a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN).
  Definition exitci_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := exists t, exit_ci t m.
  Definition exitci_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := exit_dom a.
  Definition exitci_comp : gcomp := mkGC exitci_P exitci_dom.

  #[using="Type"] Lemma descs_at_agree : forall (P : Z -> Prop) gs (m m' : mem) d, agrees_on P m m' -> (forall a, d <= a < d + 64 * Z.of_nat (length gs) -> P a) ->
    descs_at m d gs -> descs_at m' d gs.
  Proof.
    intros P gs. induction gs as [|g gs IH]; intros m m' d AG HP DA; cbn [descs_at] in *; [exact I|].
    destruct DA as [D DA]. cbn [length] in HP. split.
    - eapply agrees_rw_cells; [exact AG| exact D|]. rewrite gd_cells_size. intros a Ha. apply HP. lia.
    - eapply (IH m m' (d + 64) AG); [| exact DA]. intros a Ha. apply HP. lia.
  Qed.

  Local Ltac kin := first [left; reflexivity | right; kin].
  Local Ltac kca KC k := eapply (KC k); [unfold EXIT_CI_KEEP; kin| cbn; lia| cbn; lia| eassumption].

  #[using="Type"] Lemma exit_ci_agree : forall t (m m' : mem), exit_ci t m -> agrees_on exit_dom m m' -> exit_ci t m'.
  Proof.
    intros t m m' EC AG.
    assert (KC : forall k A cs, In k EXIT_CI_KEEP -> fst k <= A -> A + Z.of_nat (cells_size cs) <= snd k -> rw_cells asegs m A cs -> rw_cells asegs m' A cs).
    { intros k A cs Hk H1 H2 HC. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. right. left. exists k. split; [exact Hk| lia]. }
    assert (KW : forall A n, wr_at asegs m A n -> AIMSH_LO <= A -> A + n <= AIMSH_LO + AIMSH_LEN -> wr_at asegs m' A n).
    { intros A n HW H1 H2. eapply agrees_wr_at; [exact AG| exact HW|]. intros a Ha. right. right. lia. }
    (nd_pre EC 15%nat; intros TID EXL COV0 FINZ (dso & DSO) Ht RGL FLG MTX DA D69 (ob & OD) SH SH69 SHT; nd_post).
    unfold exit_ci.
    split. { eapply agrees_rw_cells; [exact AG| exact TID|]. intros a Ha. left. cbn [cells_size csize Nat.add] in Ha. lia. }
    split; [kca KC (0x601c28, 0x601c2c)|].
   
   
    split; [kca KC (0x1408a0, 0x1408a1)|]. split; [kca KC (0xab390, 0xab391)|].
    split; [exists dso; kca KC (0xa75b0, 0xa75b8)|]. split; [exact Ht|].
    split; [kca KC (0xac210, 0xac214)|]. split; [kca KC (0xab340, 0xab348)|]. split; [kca KC (0xac2b0, 0xac2b8)|].
    split. { eapply (descs_at_agree exit_dom); [exact AG| | exact DA]. intros a Ha. change (Z.of_nat (length GD69)) with 69 in Ha.
             right. left. exists (0xaa190, 0xab310). split; [unfold EXIT_CI_KEEP; kin| cbn [fst snd]; lia]. }
    split; [kca KC (0xaa190, 0xab310)|]. split; [exists ob; kca KC (0x5e10a0, 0x5e10a1)|].
    split.
    { apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) GD69_ok g Hg) as OKg. pose proof (proj1 (Forall_forall _ _) SH g Hg) as SHg.
      destruct g as ((((beg, sz), swr), nm), md). unfold gd_shw in *. (nd_pre OKg 4%nat; intros AL SWR BLO BHI; nd_post).
      assert (SWRf : swr mod 8 = 0 /\ 0 < swr) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
      destruct SWRf as [SL SZ]. (pose proof (shadow_window beg swr AL SL SZ BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
      apply KW; [exact SHg| unfold AIMSH_LO, SHW_LO in *; lia| unfold AIMSH_LO, AIMSH_LEN, SHW_LO, SHW_LEN in *; lia]. }
    split; (apply KW; [eassumption| vm_compute; discriminate| vm_compute; discriminate]).
  Qed.

  (* [comment removed for export] *)
  Hypothesis CI_EXIT : Forall (fun k => exists iv, In iv (aci AI) /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP.

  #[using="Type"] Lemma exit_keep_img : forall k, In k EXIT_CI_KEEP -> 0x10000 <= fst k /\ snd k <= 0x604000 /\ (snd k <= READ_STAGE \/ READ_STAGE + 65537 <= fst k)
    /\ (snd k <= 0x5e18f0 \/ 0x5e28f0 <= fst k).
  Proof.
    intros k Hk. unfold EXIT_CI_KEEP in Hk. unfold READ_STAGE.
    repeat (destruct Hk as [<-|Hk]; [cbn [fst snd]; lia|]). destruct Hk.
  Qed.

  #[using="AF AI_block_tls CI_EXIT"] Lemma exitci_ok : gcomp_ok AI exitci_comp.
  Proof.
    constructor; cbn [gc_P gc_dom exitci_comp]; unfold exitci_P, exitci_dom.
    - intros L RNG RNG' s s' FB m m' [t EC] _ AG _ _ _. exists t. eapply exit_ci_agree; eassumption.
    - intros L RNG s FB m LB SP a _ _ _ Ha [D|[(k & Hk & Rk)|D]].
      + right. left. left. lia.
      + left. right. left. (nd_pre (proj1 (Forall_forall _ _) CI_EXIT k Hk) 4%nat; intros iv Hiv I1 I2; nd_post). exists iv. split; [exact Hiv| lia].
      + right. right. left. exact D.
    - intros L RNG s CL FB FL m a AH _ Ha [D|[(k & Hk & Rk)|D]].
      + eapply (tls_not_client AI AF AI_block_tls); [exact AH| unfold ATP; lia].
      + eapply (img_not_client AI AF); [exact AH|]. (nd_pre (exit_keep_img k Hk) 4%nat; intros K1 K2 _ _; nd_post). unfold AIMG_HI. lia.
      + eapply (imsh_not_client AI AF); [exact AH| exact D].
    - intros L s FB a [D|[(k & Hk & Rk)|D]].
      + intros [X|X]; [pose proof ATPv_img as TI; unfold READ_STAGE in X; lia| unfold ATP in X; lia].
      + (nd_pre (exit_keep_img k Hk) 4%nat; intros K1 K2 K3 K4; nd_post). intros [X|X]; [lia|]. pose proof ATPv_img as TI. unfold ATP in X. lia.
      + exact (imsh_not_drv a D).
  Qed.
End DrvStat.
End CANSEC1.
End TwB.
