(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA I_ahm I_fflush StdioLawsA StdioCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_main_AA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require MainEntryA__A3D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit StdioLawsInstA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_glue_foKitA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require StrerrCompA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module StdioInitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells MonadF. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA I_ahm I_fflush StdioLawsA StdioCompA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_main_AA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require MainEntryA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit StdioLawsInstA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.

  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  (* [comment removed for export] *)
  #[using="en inp lim w V ms mo AM U HU HMP"] Lemma files_init : forall (L0 : alayout) (R0 : footprint) (s : PS), ps_libc s = libc_init -> files_P L0 R0 s [] m.
  Proof.
    intros L0 R0 s EL. destruct HMP as [HM HP]. split; [| constructor]. rewrite EL.
    apply stdio_files_initA.
    - apply (img_chunk V m _ 0xa9ab0 stdio_blob1 HM); [vm_compute; reflexivity| exact (proj1 stdio_blob1_wf)| exact stdio_blob1_img| lia| rewrite (proj2 stdio_blob1_wf); lia].
    - apply (img_chunk V m _ 0x601ca8 stdio_blob2 HM); [vm_compute; reflexivity| exact (proj1 stdio_blob2_wf)| exact stdio_blob2_img| lia| rewrite (proj2 stdio_blob2_wf); lia].
  Qed.

  (* [comment removed for export] *)
  #[using="rc U HU"] Lemma unp_of_run : forall (lo n A B : Z), (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)) ->
    0 < n -> 2147450880 <= lo -> lo + n <= 2147450880 + 2^44 ->
    lo <= 2147450880 + A / 8 -> 2147450880 + (B + 7) / 8 <= lo + n -> 0 <= A -> A <= B -> B <= 2^47 -> unpoisoned m A B.
  Proof.
    intros lo n A B Z1 Hn L0 L1 HA HB A0 AB B47. change (2^47) with 140737488355328 in B47.
    eapply (unpoisoned_of_zero m lo (lo + n) (fun _ => 0)).
    - apply shadow_bytes_of_pointwise; [exact Z1| lia| lia].
    - intros; reflexivity.
    - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. lia.
    - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. Z.div_mod_to_equations. lia.
    - exact A0.
    - lia.
  Qed.

  (* [comment removed for export] *)
  #[using="en inp lim w ms mo AM HAT HTLS U HU A0I HMP"] Lemma env_init : forall (L0 : alayout) (s : PS) (FB : list cblk), al_V L0 45%nat = V 45%nat -> env_P L0 RNG s FB m.
  Proof.
    intros L0 s FB E45. destruct HMP as [HM HP]. destruct HTLS as (_ & _ & _ & EAHM).
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    pf V HP (PVar 207 1 34359735410) P207.
    pose proof (ao_ahm_eq _ ALO) as EQ. (pose proof (ao_ahm _ ALO) as ndP__; nd_pre ndP__ 5%nat; intros AO1 AO2 AO3 AO4 AO5; nd_post). pose proof (ad_tls_ahm _ ALO) as TD.
    rewrite EQ in AO1, AO2, AO3, AO4, AO5, TD. pose proof atop_range as AR.
    split.
    - split; [| split; [| split; [| split]]].
      + (* [comment removed for export] *)
        aimg V m HM 0xa71e8 [C8 (Z_to_bv 64 0x9ebcc)] RC1. aimg V m HM 0xa71f0 [C8 (Z_to_bv 64 0x9f038)] RC2.
        aimg V m HM 0xa7218 [C8 (Z_to_bv 64 0x9a954)] RC3. aimg V m HM 0xa7248 [C8 (Z_to_bv 64 0x9e00c)] RC4.
        aimg V m HM 0xa7268 [C8 (Z_to_bv 64 0x944c4); C8 (Z_to_bv 64 0x9ed20)] RC5.
        aimg V m HM 0xa7290 [C8 (Z_to_bv 64 0x9a7c4); C8 (Z_to_bv 64 0x9a324); C8 (Z_to_bv 64 0x9a200)] RC6.
        exact (conj RC1 (conj RC2 (conj RC3 (conj RC4 (conj RC5 RC6))))).
      + (* [comment removed for export] *)
        mf V m HM (MCell (ZLit 6297080) 8 (ZV 45)) HCAN.
        aimg V m HM 0x601849 [C1 (Z_to_bv 8 0)] HTHR. aimg V m HM 0x60184b [C1 (Z_to_bv 8 0)] HNLK.
        split; [rewrite E45; exact HCAN|]. split; [exact HTHR | exact HNLK].
      + (* [comment removed for export] *)
        mf V m HM (MCell (ZLit 712256) 8 (ZLit 712264)) HA1. mf V m HM (MCell (ZLit 712264) 8 (ZMul (ZLit 4096) (ZV 207))) HA2.
        mf V m HM (MZero (ZMul (ZLit 4096) (ZV 207)) 3727360) HAZ. mwr V m HM (ZMul (ZLit 4096) (ZV 207)) 3727360 HAW.
        rewrite EAHM. unfold AHM_BYTES.
        split. { rw_join HA1 HA2 J. exact J. }
        split. { split; [exact HAW|]. intros i Hi. unfold AHM_BYTES in Hi. rewrite ref_mrd_overlay; [apply HAZ; lia|]. right. rewrite wa_unsigned; [| lia]. rewrite <- EAHM. unfold AIMG_HI in *. unfold iclr, AIMG_LO, AIMG_HI in AO5. lia. }
        split; [clear; Z.div_mod_to_equations; lia|]. split. { rewrite <- EAHM. unfold iclr, AIMG_LO, AIMG_HI in AO5. lia. }
        split; [rewrite <- EAHM; lia|].
        eapply (vis_rng lz AL V U A0I HU 10); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear - P207; lia.
      + (* [comment removed for export] *)
        mf V m HM (MZero (ZLit 2147459072) 8708) Z1. mf V m HM (MZero (ZLit 2147468692) 69154) Z2. mf V m HM (MZero (ZLit 2148221332) 17516) Z4.
        split; [eapply (unp_of_run 2147459072 8708); [exact Z1| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia]|].
        split; [eapply (unp_of_run 2147468692 69154); [exact Z2| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia]|].
        split; [eapply (unp_of_run 2147468692 69154); [exact Z2| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia]|].
        eapply (unp_of_run 2148221332 17516); [exact Z4| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia].
      + apply rng0_fp_ok.
    - split; [exact AO4|]. unfold adisj in TD. unfold ATP, AAHM_SZ. lia.
  Qed.
End Init.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.

  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  (* [comment removed for export] *)
  #[using="en inp lim w V ms mo AM U HU HMP"] Lemma files_init : forall (L0 : alayout) (R0 : footprint) (s : PS), ps_libc s = libc_init -> files_P L0 R0 s [] m.
  Proof.
    intros L0 R0 s EL. destruct HMP as [HM HP]. split; [| constructor]. rewrite EL.
    apply stdio_files_initA.
    - apply (img_chunk V m _ 0xa9e90 stdio_blob1 HM); [vm_compute; reflexivity| exact (proj1 stdio_blob1_wf)| exact stdio_blob1_img| lia| rewrite (proj2 stdio_blob1_wf); lia].
    - apply (img_chunk V m _ 0x6020a8 stdio_blob2 HM); [vm_compute; reflexivity| exact (proj1 stdio_blob2_wf)| exact stdio_blob2_img| lia| rewrite (proj2 stdio_blob2_wf); lia].
  Qed.

  (* [comment removed for export] *)
  #[using="rc U HU"] Lemma unp_of_run : forall (lo n A B : Z), (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)) ->
    0 < n -> 2147450880 <= lo -> lo + n <= 2147450880 + 2^44 ->
    lo <= 2147450880 + A / 8 -> 2147450880 + (B + 7) / 8 <= lo + n -> 0 <= A -> A <= B -> B <= 2^47 -> unpoisoned m A B.
  Proof.
    intros lo n A B Z1 Hn L0 L1 HA HB A0 AB B47. change (2^47) with 140737488355328 in B47.
    eapply (unpoisoned_of_zero m lo (lo + n) (fun _ => 0)).
    - apply shadow_bytes_of_pointwise; [exact Z1| lia| lia].
    - intros; reflexivity.
    - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. lia.
    - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. Z.div_mod_to_equations. lia.
    - exact A0.
    - lia.
  Qed.

  (* [comment removed for export] *)
  #[using="en inp lim w ms mo AM HAT HTLS U HU A0I HMP"] Lemma env_init : forall (L0 : alayout) (s : PS) (FB : list cblk), al_V L0 45%nat = V 45%nat -> env_P L0 RNG s FB m.
  Proof.
    intros L0 s FB E45. destruct HMP as [HM HP]. destruct HTLS as (_ & _ & _ & EAHM).
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    pf V HP (PVar 207 1 34359735410) P207.
    pose proof (ao_ahm_eq _ ALO) as EQ. (pose proof (ao_ahm _ ALO) as ndP__; nd_pre ndP__ 5%nat; intros AO1 AO2 AO3 AO4 AO5; nd_post). pose proof (ad_tls_ahm _ ALO) as TD.
    rewrite EQ in AO1, AO2, AO3, AO4, AO5, TD. pose proof atop_range as AR.
    split.
    - split; [| split; [| split; [| split]]].
      + (* [comment removed for export] *)
        aimg V m HM 0xa75c8 [C8 (Z_to_bv 64 0x9efb0)] RC1. aimg V m HM 0xa75d0 [C8 (Z_to_bv 64 0x9f41c)] RC2.
        aimg V m HM 0xa75f8 [C8 (Z_to_bv 64 0x9ad38)] RC3. aimg V m HM 0xa7628 [C8 (Z_to_bv 64 0x9e3f0)] RC4.
        aimg V m HM 0xa7648 [C8 (Z_to_bv 64 0x948a8); C8 (Z_to_bv 64 0x9f104)] RC5.
        aimg V m HM 0xa7670 [C8 (Z_to_bv 64 0x9aba8); C8 (Z_to_bv 64 0x9a708); C8 (Z_to_bv 64 0x9a5e4)] RC6.
        exact (conj RC1 (conj RC2 (conj RC3 (conj RC4 (conj RC5 RC6))))).
      + (* [comment removed for export] *)
        mf V m HM (MCell (ZLit 6298104) 8 (ZV 45)) HCAN.
        aimg V m HM 0x601c49 [C1 (Z_to_bv 8 0)] HTHR. aimg V m HM 0x601c4b [C1 (Z_to_bv 8 0)] HNLK.
        split; [rewrite E45; exact HCAN|]. split; [exact HTHR | exact HNLK].
      + (* [comment removed for export] *)
        mf V m HM (MCell (ZLit 713280) 8 (ZLit 713288)) HA1. mf V m HM (MCell (ZLit 713288) 8 (ZMul (ZLit 4096) (ZV 207))) HA2.
        mf V m HM (MZero (ZMul (ZLit 4096) (ZV 207)) 3727360) HAZ. mwr V m HM (ZMul (ZLit 4096) (ZV 207)) 3727360 HAW.
        rewrite EAHM. unfold AHM_BYTES.
        split. { rw_join HA1 HA2 J. exact J. }
        split. { split; [exact HAW|]. intros i Hi. unfold AHM_BYTES in Hi. rewrite ref_mrd_overlay; [apply HAZ; lia|]. right. rewrite wa_unsigned; [| lia]. rewrite <- EAHM. unfold AIMG_HI in *. unfold iclr, AIMG_LO, AIMG_HI in AO5. lia. }
        split; [clear; Z.div_mod_to_equations; lia|]. split. { rewrite <- EAHM. unfold iclr, AIMG_LO, AIMG_HI in AO5. lia. }
        split; [rewrite <- EAHM; lia|].
        eapply (vis_rng lz AL V U A0I HU 10); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; clear - P207; lia.
      + (* [comment removed for export] *)
        mf V m HM (MZero (ZLit 2147459072) 8708) Z1. mf V m HM (MZero (ZLit 2147468692) 69278) Z2. mf V m HM (MZero (ZLit 2148221460) 17900) Z4.
        split; [eapply (unp_of_run 2147459072 8708); [exact Z1| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia]|].
        split; [eapply (unp_of_run 2147468692 69278); [exact Z2| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia]|].
        split; [eapply (unp_of_run 2147468692 69278); [exact Z2| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia]|].
        eapply (unp_of_run 2148221460 17900); [exact Z4| lia| lia| lia| vm_compute; discriminate| vm_compute; discriminate| lia| lia| lia].
      + apply rng0_fp_ok.
    - split; [exact AO4|]. unfold adisj in TD. unfold ATP, AAHM_SZ. lia.
  Qed.
End Init.
End CANSEC1.
End TwB.
End StdioInitA.

(* [comment removed for export] *)
Module StrerrInitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells MonadF. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA I_ahm I_fflush StdioLawsA StdioCompA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_glue_foKitA__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strerrA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_main_AA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require MainEntryA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit StdioLawsInstA StrerrCompA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StrerrCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.

  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="en inp lim w V ms mo AM HTLS U HU HMP"] Lemma strerr_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), strerr_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. destruct HMP as [HM HP]. pose proof (tls_at_tp V HTLS) as HTP.
    unfold strerr_P, ATP. split; [| split].
    - mf V m HM (MCell (ZLit 6165896) 8 (ZLit 6297728)) HC.
      rewrite HTP. replace (0x5e15b8 + -48) with 6165896 by reflexivity. exact HC.
    - aimg V m HM 0x6018a8 [C8 (Z_to_bv 64 0)] HL. exact HL.
    - exists (zeros 256).
      aimg V m HM 6165964 [CB (Z.to_nat 256) (zeros 256)] K.
      replace (ATPv + 20) with 6165964 by (rewrite HTP; reflexivity). exact K.
  Qed.
End Init.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strerrA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StrerrCompA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.

  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Let HMP := me_facts en inp lim w V m ms mo AM.

  #[using="en inp lim w V ms mo AM HTLS U HU HMP"] Lemma strerr_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), strerr_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. destruct HMP as [HM HP]. pose proof (tls_at_tp V HTLS) as HTP.
    unfold strerr_P, ATP. split; [| split].
    - mf V m HM (MCell (ZLit 6166920) 8 (ZLit 6298752)) HC.
      rewrite HTP. replace (0x5e19b8 + -48) with 6166920 by reflexivity. exact HC.
    - aimg V m HM 0x601ca8 [C8 (Z_to_bv 64 0)] HL. exact HL.
    - exists (zeros 256).
      aimg V m HM 6166988 [CB (Z.to_nat 256) (zeros 256)] K.
      replace (ATPv + 20) with 6166988 by (rewrite HTP; reflexivity). exact K.
  Qed.
End Init.
End CANSEC1.
End TwB.
End StrerrInitA.
