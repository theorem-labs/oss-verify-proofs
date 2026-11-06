(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added fuzz_pcap_asan_srz and fuzz_pcap_both_srz, the srealizes facts of fuzz_pcap_asan_lim and fuzz_pcap_both_lim stated on their own, for the halting proofs. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes Decode Ceiling ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Stdio Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require EntryCeil Final_ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AcctCore ExecF ITreeA ModelX NodesA NodesAS NodesCov NodesSil ProtoS RunConst AdequacyA TopLevelA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanInv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface ATsafeX AIface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UMainX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require AtMainA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require AtMainB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Final_asan.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import A3Img.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode Ceiling ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Stdio Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivFinal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil Final_ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA ModelX NodesA NodesAS NodesCov NodesSil ProtoS RunConst AdequacyA TopLevelA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanInv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface ATsafeX AIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UMainX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require AtMainA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.HeapI_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UMainX__EquivA.TopX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AtMainA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rcA (en : ExecEntry) : runConstT :=
  rc_of_ceil (CE := ceil_of_sp (en_sp en)) (sec en) (ssp_canary (en_draw en)) (sec_range en).

Lemma rcA_ATOP : forall img en inp, valid_input inp -> valid_entry img en inp ->
  @ATOP (rcA en) = page_round_down_Z (bv_unsigned (en_sp en) - 8388608).
Proof.
  intros img en inp VI VE. unfold rcA. rewrite rc_of_ceil_ATOP, (alloc_ceiling_of_sp _ (valid_entry_sp _ _ _ VI VE)), stack_max_size_val. reflexivity.
Qed.

Lemma site_frameA_off : forall site f off, site_frameA site = Some (f, off) -> 0 <= off <= 65536.
Proof. intros site f off H. destruct site; cbn in H; try discriminate H; injection H as <- <-; lia. Qed.

(* [comment removed for export] *)
Definition sA0 (V : nat -> Z) : PState aheap HeapFull.hptr :=
  mkPS (aheap_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V)) libc_init None 6165744.

Section FinalAsan.
Variable stkA : stack_site -> Z.
Hypothesis STKA : UPcapXA.stk_ok stkA.

Definition treeA (en : ExecEntry) (inp : ProcInput) (V : nat -> Z) : itree node (ITree.Exc.exc unit) :=
  TREE_A (rc := rcA en) site_frameA inp stkA (sA0 V).

(* [comment removed for export] *)
Hypothesis IMPL_A : forall enT inp, valid_entry IMG enT inp -> valid_input inp ->
  forall w V m ms mo_, amain_open enT inp LIMIT w V m ms mo_ ->
  exists Q, implF SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) fstepS
              (RNGof (A0 V) (MX mo_ [])) (treeA enT inp V) Q ms.

(* [comment removed for export] *)
Inductive MainTreeA (inp : ProcInput) (enT : ExecEntry) : forall R : Type, itree node R -> Model -> Prop :=
| MTA : forall w V m ms mo_, amain_open enT inp LIMIT w V m ms mo_ -> MainTreeA inp enT _ (treeA enT inp V) (MX mo_ []).

#[local] Notation IMG_S := (mkImage ssegs SRCM.init_pc SRCM.phdrs).
#[local] Notation NSA := (nodesA_sound_closed SEGS NMAX_A ASHM0).
#[local] Notation SSA := (silA_sound SEGS NMAX_A ASHM0).

(* [comment removed for export] *)
Section Lim.
Variable limS : Z.
Hypothesis LIMS : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink.BLIVE + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink.RMAX <= limS.

(* [comment removed for export] *)
#[using="LIMS"] Lemma tree_ok_S : exists QS, tree_ok ssegs SRCM.init_pc SRCM.phdrs limS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec) QS.
Proof.
  apply (tree_ok_S_final ssegs SRCM.init_pc SRCM.phdrs tbS stkS sec sec_range limS (image_ok_src3_lim limS LIMS)).
  - intros en inp _. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.tls_in_image_ssegs.
  - intros en. destruct (spB_ok en) as [A B]. exact (sites_at_ok_S _ A B).
  - exact IMPL_S_final.
Qed.

(* [comment removed for export] *)
Section AtState.
Variables (enS enT : ExecEntry) (inp : ProcInput).
Hypothesis VES : valid_entry IMG_S enS inp.
Hypothesis VET : valid_entry IMG enT inp.
Hypothesis VI : valid_input inp.
Variables (w : bool) (V : nat -> Z) (m : word -> option byte) (ms : machine_state) (mo_ : Model).
Hypothesis HO : amain_open enT inp LIMIT w V m ms mo_.

#[local] Instance rc_here : runConstT := rcA enT.
#[local] Instance ces_here : CEIL := ceil_of_sp (en_sp enS).
Local Notation moA := (MX mo_ []).

#[using="w m ms HO"] Lemma HO_parts : amodel V enT inp LIMIT mo_ /\ Forall (pfact_ok V) asan_pure_facts /\ (forall n, 0 <= V n < 2 ^ 64)
  /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned (en_sp enT).
Proof.
  destruct HO as (_ & HVR & PIN & _ & HPF & _ & _ & _ & _ & AMOD & _).
  split; [exact AMOD|]. split; [apply Forall_app in HPF as [X _]; exact X|]. split; [exact HVR|].
  destruct PIN as (_ & _ & _ & E & _). exact E.
Qed.

Let HMd := proj1 HO_parts.
Let HPd := proj1 (proj2 HO_parts).
Let HVRd := proj1 (proj2 (proj2 HO_parts)).
Let HUSPd := proj2 (proj2 (proj2 HO_parts)).
Let HATd : ATOP = page_round_down_Z (bv_unsigned (en_sp enT) - 8388608) := rcA_ATOP IMG enT inp VI VET.

Definition AH_here : AHalves NMAX_A site_frameA :=
  AH_A NMAX_A (a_space_beg0 V) (a_ptr_array0 V) (A0 V) (resv_of V) site_frameA site_frameA_off
       (HLIM_A) (ABASE_SH_A V enT HPd HATd HUSPd HVRd) (HSB_A V enT HPd HATd HUSPd) (HPA_A V enT HPd HATd HUSPd).

#[using="HMd"] Lemma AHM_here : aG NMAX_A site_frameA AH_here ∅ 0%N 0 (A0 V) (sA0 V) moA.
Proof. exact (AJ_main V enT inp mo_ HMd HPd HATd HUSPd HVRd libc_init None 6165744). Qed.

#[using="enT w V m ms HO HMd"] Lemma AFDS_here : m_fds moA = m_fds (mo0 ssegs limS enS inp).
Proof. rewrite m_fds_MX, (am_fds _ _ _ _ _ HMd). reflexivity. Qed.
#[using="enT w V m ms HO HMd"] Lemma AFS_here : m_fs moA = m_fs (mo0 ssegs limS enS inp).
Proof. rewrite m_fs_MX, (am_fs _ _ _ _ _ HMd). reflexivity. Qed.
#[using="enT inp w V m ms HO HMd"] Lemma AHALT_here : m_halted moA = None.
Proof. rewrite m_halted_MX. exact (am_halted _ _ _ _ _ HMd). Qed.

Local Notation TS := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec inp enS).
Local Notation moS := (mo0 ssegs limS enS inp).
Local Notation TA := (treeA enT inp V).

#[using="Type"] Lemma STKS_here : UPcapXA.stk_ok (stkS enS).
Proof. destruct (spB_ok enS) as [A B]. exact (sites_at_ok_S _ A B). Qed.
#[using="Type"] Lemma TLSS_here : tls_in_image ssegs (tbS enS).
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.tls_in_image_ssegs. Qed.

#[using="LIMS VES VET VI w m ms HO HMd HPd HVRd HUSPd HATd"] Lemma sim_SA_here : forall full, texit nstep nexit TS moS full -> wexit (npeek SEGS) nstep nexit TA moA (eq full).
Proof.
  exact (sim_SA NMAX_A site_frameA AH_here ssegs limS enS inp (tbS enS) (stkS enS) (sec enS)
           (image_ok_src3_lim limS LIMS) (valid_entry_brk' _ _ _ _ _ VES) TLSS_here STKS_here (valid_input_argv inp VI) VI
           (mo0_ceil_valid _ _ _ _ _ _ VI VES) (sec_range enS) SEGS stkA (sA0 V) moA (A0 V)
           AHM_here eq_refl eq_refl AFDS_here AFS_here AHALT_here).
Qed.
#[using="LIMS STKA VES VET VI w m ms HO HMd HPd HVRd HUSPd HATd"] Lemma sim_AS_here : forall full, texit nstep nexit TA moA full -> wexit (npeek ssegs) nstep nexit TS moS (eq full).
Proof.
  exact (sim_AS NMAX_A site_frameA AH_here ssegs limS enS inp (tbS enS) (stkS enS) (sec enS)
           (image_ok_src3_lim limS LIMS) (valid_entry_brk' _ _ _ _ _ VES) TLSS_here (valid_input_argv inp VI) VI
           (mo0_ceil_valid _ _ _ _ _ _ VI VES) (sec_range enS) stkA (sA0 V) moA (A0 V) STKA
           AHM_here eq_refl eq_refl (minv_lf_main V enT inp mo_ HMd) AFDS_here AFS_here AHALT_here).
Qed.
#[using="LIMS STKA enS VES VET VI w m ms HO HMd HPd HVRd HUSPd HATd"] Lemma safe_A_here : leaves_unreachable_m nstep TA moA
  /\ tsafeA nstepA (nsafeA NMAX_A ASHM0) fstepS NMAX_A (RNGof (A0 V) moA) (A0 V) TA moA.
Proof.
  exact (safe_A NMAX_A site_frameA AH_here ssegs limS enS inp (tbS enS) (stkS enS) (sec enS)
           (image_ok_src3_lim limS LIMS) (valid_entry_brk' _ _ _ _ _ VES) TLSS_here (valid_input_argv inp VI) VI
           (mo0_ceil_valid _ _ _ _ _ _ VI VES) (sec_range enS) stkA (sA0 V) moA (A0 V) STKA
           AHM_here eq_refl eq_refl (minv_lf_main V enT inp mo_ HMd) AFDS_here AFS_here AHALT_here).
Qed.
End AtState.

(* The target run's srealizes fact that the error-free equivalence below is read from, stated on its own for the halting proof (lib/E2/Top/Halts_asan.v). *)
#[using="stkA STKA IMPL_A LIMS"] Theorem fuzz_pcap_asan_srz : forall enS enT inp,
  valid_entry IMG_S enS inp -> valid_entry IMG enT inp -> valid_input inp ->
  SpinAlg.srealizes SEGS (init_config SEGS PC0 PH (en_sp enT) (en_brk enT) (en_mmap_base enT) (en_draw enT) target_alloc_limit inp)
    ((fun tr => bh_traces (run_scfg CFG IMG_S limS enS inp) tr) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet).
Proof.
  destruct tree_ok_S as [QS HS]. intros enS enT inp HvS HvT Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (run_of_tree ssegs SRCM.init_pc SRCM.phdrs limS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & HcomplS & HerrS).
  set (K := (fun tr => bh_traces (run_scfg CFG IMG_S limS enS inp) tr) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet).
  apply (srealizes_boot_main_adq node SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) nstepA nexitA (minvA ASHM0) (nsafeA NMAX_A ASHM0) fstepS NMAX_A NSA SSA
           _ (amain_at enT inp LIMIT) K).
  - intros K' HK. destruct enT as [sp brk mbase draw]. cbn [en_sp en_brk en_mmap_base en_draw].
    apply (boot_main_ready sp brk mbase draw LIMIT inp Hvi HvT ltac:(unfold LIMIT; lia)). exact HK.
  - intros ms mo_ (w & V & m & HO).
    destruct (IMPL_A enT inp HvT Hvi w V m ms mo_ HO) as [Q HI].
    destruct (safe_A_here enS enT inp HvS HvT Hvi w V m ms mo_ HO) as [HL HT].
    pose proof (HO_parts enT inp w V m ms mo_ HO) as (HMd & _).
    exists _, (treeA enT inp V), (RNGof (A0 V) (MX mo_ [])), (A0 V), Q, (MX mo_ []).
    split.
    { split; [exact HI|]. split; [exact HL|]. split; [exact (AHALT_here enT inp w V m ms mo_ HO)|].
      split; [exact (minvA_main V enT inp mo_ HMd)|]. split; [exact HT| exact (mrel_main V enT inp mo_ HMd)]. }
    split.
    + intros tr Htr. apply HcomplS.
      apply (texit_wexit_wins ssegs _ _ _ _ (sim_AS_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
      apply tree_traces_exits; [exact HL| exact Htr].
    + intros tr Htr. apply (wins_npeekA SEGS SEGS).
      apply (texit_wexit_wins SEGS _ _ _ _ (sim_SA_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
      apply (tree_traces_exits _ _ _ HleavesS). apply HsoundS. exact Htr.
Qed.

(* [comment removed for export] *)
#[using="stkA STKA IMPL_A LIMS"] Theorem fuzz_pcap_asan_lim : forall enS enT inp,
  valid_entry IMG_S enS inp -> valid_entry IMG enT inp -> valid_input inp ->
  strong_equiv_error_free_budgets_scfg CFG limS target_alloc_limit IMG_S IMG enS enT inp.
Proof.
  destruct tree_ok_S as [QS HS]. intros enS enT inp HvS HvT Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (run_of_tree ssegs SRCM.init_pc SRCM.phdrs limS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & HcomplS & HerrS).
  set (K := (fun tr => bh_traces (run_scfg CFG IMG_S limS enS inp) tr) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet).
  assert (SRZ : SpinAlg.srealizes SEGS (init_config SEGS PC0 PH (en_sp enT) (en_brk enT) (en_mmap_base enT) (en_draw enT) target_alloc_limit inp) K).
  { apply (srealizes_boot_main_adq node SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) nstepA nexitA (minvA ASHM0) (nsafeA NMAX_A ASHM0) fstepS NMAX_A NSA SSA
             _ (amain_at enT inp LIMIT) K).
    - intros K' HK. destruct enT as [sp brk mbase draw]. cbn [en_sp en_brk en_mmap_base en_draw].
      apply (boot_main_ready sp brk mbase draw LIMIT inp Hvi HvT ltac:(unfold LIMIT; lia)). exact HK.
    - intros ms mo_ (w & V & m & HO).
      destruct (IMPL_A enT inp HvT Hvi w V m ms mo_ HO) as [Q HI].
      destruct (safe_A_here enS enT inp HvS HvT Hvi w V m ms mo_ HO) as [HL HT].
      pose proof (HO_parts enT inp w V m ms mo_ HO) as (HMd & _).
      exists _, (treeA enT inp V), (RNGof (A0 V) (MX mo_ [])), (A0 V), Q, (MX mo_ []).
      split.
      { split; [exact HI|]. split; [exact HL|]. split; [exact (AHALT_here enT inp w V m ms mo_ HO)|].
        split; [exact (minvA_main V enT inp mo_ HMd)|]. split; [exact HT| exact (mrel_main V enT inp mo_ HMd)]. }
      split.
      + intros tr Htr. apply HcomplS.
        apply (texit_wexit_wins ssegs _ _ _ _ (sim_AS_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
        apply tree_traces_exits; [exact HL| exact Htr].
      + intros tr Htr. apply (wins_npeekA SEGS SEGS).
        apply (texit_wexit_wins SEGS _ _ _ _ (sim_SA_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
        apply (tree_traces_exits _ _ _ HleavesS). apply HsoundS. exact Htr. }
  split; [exact HerrS|].
  rewrite (run_eq SEGS PC0 PH target_alloc_limit enT inp). cbv zeta. cbn [bh_traces bh_errors]. rewrite init_config_eq in SRZ. split.
  - exact (SpinAlg.srealizes_no_error SEGS _ _ SRZ).
  - intros tr. split.
    + intros H. apply (SpinAlg.srealizes_obs_iff SEGS _ _ SRZ tr). exact H.
    + intros H. apply (SpinAlg.srealizes_obs_iff SEGS _ _ SRZ tr) in H. exact H.
Qed.

End Lim.

(* [comment removed for export] *)
#[using="stkA STKA IMPL_A"] Theorem fuzz_pcap_asan_scfg : strong_universal_error_free_T_scfg CFG IMG_S IMG.
Proof.
  intros enS enT inp HvS HvT Hvi.
  exact (fuzz_pcap_asan_lim source_alloc_limit (proj1 budgets_ok) enS enT inp HvS HvT Hvi).
Qed.

(* [comment removed for export] *)
#[using="stkA STKA IMPL_A"] Theorem fuzz_pcap_asan_main :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target IMG_S IMG.
Proof.
  intros enS enT inp HvS HvT Hvi _.
  exact (fuzz_pcap_asan_lim sanitizer_source_limit budgets_ok_san enS enT inp HvS HvT Hvi).
Qed.
End FinalAsan.
End Final_asan.

(* [comment removed for export] *)
Module Final_both.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode Ceiling ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Stdio Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivFinal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil Final_ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA ModelX NodesA NodesAS NodesCov NodesSil ProtoS RunConst AdequacyA TopLevelA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanInv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require Import MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface ATsafeX AIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UMainX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require AtMainB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.HeapI_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UMainX__EquivA.TopX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AtMainB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rcA (en : ExecEntry) : runConstT :=
  rc_of_ceil (CE := ceil_of_sp (en_sp en)) (sec en) (ssp_canary (en_draw en)) (sec_range en).

Lemma rcA_ATOP : forall img en inp, valid_input inp -> valid_entry img en inp ->
  @ATOP (rcA en) = page_round_down_Z (bv_unsigned (en_sp en) - 8388608).
Proof.
  intros img en inp VI VE. unfold rcA. rewrite rc_of_ceil_ATOP, (alloc_ceiling_of_sp _ (valid_entry_sp _ _ _ VI VE)), stack_max_size_val. reflexivity.
Qed.

Lemma site_frameA_off : forall site f off, site_frameA site = Some (f, off) -> 0 <= off <= 65536.
Proof. intros site f off H. destruct site; cbn in H; try discriminate H; injection H as <- <-; lia. Qed.

(* [comment removed for export] *)
Definition sA0 (V : nat -> Z) : PState aheap HeapFull.hptr :=
  mkPS (aheap_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V)) libc_init None 6166768.

Section FinalAsan.
Variable stkA : stack_site -> Z.
Hypothesis STKA : UPcapXA.stk_ok stkA.

Definition treeA (en : ExecEntry) (inp : ProcInput) (V : nat -> Z) : itree node (ITree.Exc.exc unit) :=
  TREE_A (rc := rcA en) site_frameA inp stkA (sA0 V).

(* [comment removed for export] *)
Hypothesis IMPL_A : forall enT inp, valid_entry IMG enT inp -> valid_input inp ->
  forall w V m ms mo_, amain_open enT inp LIMIT w V m ms mo_ ->
  exists Q, implF SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) fstepS
              (RNGof (A0 V) (MX mo_ [])) (treeA enT inp V) Q ms.

(* [comment removed for export] *)
Inductive MainTreeA (inp : ProcInput) (enT : ExecEntry) : forall R : Type, itree node R -> Model -> Prop :=
| MTA : forall w V m ms mo_, amain_open enT inp LIMIT w V m ms mo_ -> MainTreeA inp enT _ (treeA enT inp V) (MX mo_ []).

#[local] Notation IMG_S := (mkImage ssegs SRCM.init_pc SRCM.phdrs).
#[local] Notation NSA := (nodesA_sound_closed SEGS NMAX_A ASHM0).
#[local] Notation SSA := (silA_sound SEGS NMAX_A ASHM0).

(* [comment removed for export] *)
Section Lim.
Variable limS : Z.
Hypothesis LIMS : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink.BLIVE + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink.RMAX <= limS.

(* [comment removed for export] *)
#[using="LIMS"] Lemma tree_ok_S : exists QS, tree_ok ssegs SRCM.init_pc SRCM.phdrs limS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec) QS.
Proof.
  apply (tree_ok_S_final ssegs SRCM.init_pc SRCM.phdrs tbS stkS sec sec_range limS (image_ok_src3_lim limS LIMS)).
  - intros en inp _. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.tls_in_image_ssegs.
  - intros en. destruct (spB_ok en) as [A B]. exact (sites_at_ok_S _ A B).
  - exact IMPL_S_final.
Qed.

(* [comment removed for export] *)
Section AtState.
Variables (enS enT : ExecEntry) (inp : ProcInput).
Hypothesis VES : valid_entry IMG_S enS inp.
Hypothesis VET : valid_entry IMG enT inp.
Hypothesis VI : valid_input inp.
Variables (w : bool) (V : nat -> Z) (m : word -> option byte) (ms : machine_state) (mo_ : Model).
Hypothesis HO : amain_open enT inp LIMIT w V m ms mo_.

#[local] Instance rc_here : runConstT := rcA enT.
#[local] Instance ces_here : CEIL := ceil_of_sp (en_sp enS).
Local Notation moA := (MX mo_ []).

#[using="w m ms HO"] Lemma HO_parts : amodel V enT inp LIMIT mo_ /\ Forall (pfact_ok V) asan_pure_facts /\ (forall n, 0 <= V n < 2 ^ 64)
  /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned (en_sp enT).
Proof.
  destruct HO as (_ & HVR & PIN & _ & HPF & _ & _ & _ & _ & AMOD & _).
  split; [exact AMOD|]. split; [apply Forall_app in HPF as [X _]; exact X|]. split; [exact HVR|].
  destruct PIN as (_ & _ & _ & E & _). exact E.
Qed.

Let HMd := proj1 HO_parts.
Let HPd := proj1 (proj2 HO_parts).
Let HVRd := proj1 (proj2 (proj2 HO_parts)).
Let HUSPd := proj2 (proj2 (proj2 HO_parts)).
Let HATd : ATOP = page_round_down_Z (bv_unsigned (en_sp enT) - 8388608) := rcA_ATOP IMG enT inp VI VET.

Definition AH_here : AHalves NMAX_A site_frameA :=
  AH_A NMAX_A (a_space_beg0 V) (a_ptr_array0 V) (A0 V) (resv_of V) site_frameA site_frameA_off
       (HLIM_A) (ABASE_SH_A V enT HPd HATd HUSPd HVRd) (HSB_A V enT HPd HATd HUSPd) (HPA_A V enT HPd HATd HUSPd).

#[using="HMd"] Lemma AHM_here : aG NMAX_A site_frameA AH_here ∅ 0%N 0 (A0 V) (sA0 V) moA.
Proof. exact (AJ_main V enT inp mo_ HMd HPd HATd HUSPd HVRd libc_init None 6166768). Qed.

#[using="enT w V m ms HO HMd"] Lemma AFDS_here : m_fds moA = m_fds (mo0 ssegs limS enS inp).
Proof. rewrite m_fds_MX, (am_fds _ _ _ _ _ HMd). reflexivity. Qed.
#[using="enT w V m ms HO HMd"] Lemma AFS_here : m_fs moA = m_fs (mo0 ssegs limS enS inp).
Proof. rewrite m_fs_MX, (am_fs _ _ _ _ _ HMd). reflexivity. Qed.
#[using="enT inp w V m ms HO HMd"] Lemma AHALT_here : m_halted moA = None.
Proof. rewrite m_halted_MX. exact (am_halted _ _ _ _ _ HMd). Qed.

Local Notation TS := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec inp enS).
Local Notation moS := (mo0 ssegs limS enS inp).
Local Notation TA := (treeA enT inp V).

#[using="Type"] Lemma STKS_here : UPcapXA.stk_ok (stkS enS).
Proof. destruct (spB_ok enS) as [A B]. exact (sites_at_ok_S _ A B). Qed.
#[using="Type"] Lemma TLSS_here : tls_in_image ssegs (tbS enS).
Proof. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.tls_in_image_ssegs. Qed.

#[using="LIMS VES VET VI w m ms HO HMd HPd HVRd HUSPd HATd"] Lemma sim_SA_here : forall full, texit nstep nexit TS moS full -> wexit (npeek SEGS) nstep nexit TA moA (eq full).
Proof.
  exact (sim_SA NMAX_A site_frameA AH_here ssegs limS enS inp (tbS enS) (stkS enS) (sec enS)
           (image_ok_src3_lim limS LIMS) (valid_entry_brk' _ _ _ _ _ VES) TLSS_here STKS_here (valid_input_argv inp VI) VI
           (mo0_ceil_valid _ _ _ _ _ _ VI VES) (sec_range enS) SEGS stkA (sA0 V) moA (A0 V)
           AHM_here eq_refl eq_refl AFDS_here AFS_here AHALT_here).
Qed.
#[using="LIMS STKA VES VET VI w m ms HO HMd HPd HVRd HUSPd HATd"] Lemma sim_AS_here : forall full, texit nstep nexit TA moA full -> wexit (npeek ssegs) nstep nexit TS moS (eq full).
Proof.
  exact (sim_AS NMAX_A site_frameA AH_here ssegs limS enS inp (tbS enS) (stkS enS) (sec enS)
           (image_ok_src3_lim limS LIMS) (valid_entry_brk' _ _ _ _ _ VES) TLSS_here (valid_input_argv inp VI) VI
           (mo0_ceil_valid _ _ _ _ _ _ VI VES) (sec_range enS) stkA (sA0 V) moA (A0 V) STKA
           AHM_here eq_refl eq_refl (minv_lf_main V enT inp mo_ HMd) AFDS_here AFS_here AHALT_here).
Qed.
#[using="LIMS STKA enS VES VET VI w m ms HO HMd HPd HVRd HUSPd HATd"] Lemma safe_A_here : leaves_unreachable_m nstep TA moA
  /\ tsafeA nstepA (nsafeA NMAX_A ASHM0) fstepS NMAX_A (RNGof (A0 V) moA) (A0 V) TA moA.
Proof.
  exact (safe_A NMAX_A site_frameA AH_here ssegs limS enS inp (tbS enS) (stkS enS) (sec enS)
           (image_ok_src3_lim limS LIMS) (valid_entry_brk' _ _ _ _ _ VES) TLSS_here (valid_input_argv inp VI) VI
           (mo0_ceil_valid _ _ _ _ _ _ VI VES) (sec_range enS) stkA (sA0 V) moA (A0 V) STKA
           AHM_here eq_refl eq_refl (minv_lf_main V enT inp mo_ HMd) AFDS_here AFS_here AHALT_here).
Qed.
End AtState.

(* The target run's srealizes fact that the error-free equivalence below is read from, stated on its own for the halting proof (lib/E2/Top/Halts_asan.v). *)
#[using="stkA STKA IMPL_A LIMS"] Theorem fuzz_pcap_both_srz : forall enS enT inp,
  valid_entry IMG_S enS inp -> valid_entry IMG enT inp -> valid_input inp ->
  SpinAlg.srealizes SEGS (init_config SEGS PC0 PH (en_sp enT) (en_brk enT) (en_mmap_base enT) (en_draw enT) target_alloc_limit inp)
    ((fun tr => bh_traces (run_scfg CFG IMG_S limS enS inp) tr) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet).
Proof.
  destruct tree_ok_S as [QS HS]. intros enS enT inp HvS HvT Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (run_of_tree ssegs SRCM.init_pc SRCM.phdrs limS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & HcomplS & HerrS).
  set (K := (fun tr => bh_traces (run_scfg CFG IMG_S limS enS inp) tr) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet).
  apply (srealizes_boot_main_adq node SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) nstepA nexitA (minvA ASHM0) (nsafeA NMAX_A ASHM0) fstepS NMAX_A NSA SSA
           _ (amain_at enT inp LIMIT) K).
  - intros K' HK. destruct enT as [sp brk mbase draw]. cbn [en_sp en_brk en_mmap_base en_draw].
    apply (boot_main_ready sp brk mbase draw LIMIT inp Hvi HvT ltac:(unfold LIMIT; lia)). exact HK.
  - intros ms mo_ (w & V & m & HO).
    destruct (IMPL_A enT inp HvT Hvi w V m ms mo_ HO) as [Q HI].
    destruct (safe_A_here enS enT inp HvS HvT Hvi w V m ms mo_ HO) as [HL HT].
    pose proof (HO_parts enT inp w V m ms mo_ HO) as (HMd & _).
    exists _, (treeA enT inp V), (RNGof (A0 V) (MX mo_ [])), (A0 V), Q, (MX mo_ []).
    split.
    { split; [exact HI|]. split; [exact HL|]. split; [exact (AHALT_here enT inp w V m ms mo_ HO)|].
      split; [exact (minvA_main V enT inp mo_ HMd)|]. split; [exact HT| exact (mrel_main V enT inp mo_ HMd)]. }
    split.
    + intros tr Htr. apply HcomplS.
      apply (texit_wexit_wins ssegs _ _ _ _ (sim_AS_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
      apply tree_traces_exits; [exact HL| exact Htr].
    + intros tr Htr. apply (wins_npeekA SEGS SEGS).
      apply (texit_wexit_wins SEGS _ _ _ _ (sim_SA_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
      apply (tree_traces_exits _ _ _ HleavesS). apply HsoundS. exact Htr.
Qed.

(* [comment removed for export] *)
#[using="stkA STKA IMPL_A LIMS"] Theorem fuzz_pcap_both_lim : forall enS enT inp,
  valid_entry IMG_S enS inp -> valid_entry IMG enT inp -> valid_input inp ->
  strong_equiv_error_free_budgets_scfg CFG limS target_alloc_limit IMG_S IMG enS enT inp.
Proof.
  destruct tree_ok_S as [QS HS]. intros enS enT inp HvS HvT Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (run_of_tree ssegs SRCM.init_pc SRCM.phdrs limS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS ssegs tbS stkS sec inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & HcomplS & HerrS).
  set (K := (fun tr => bh_traces (run_scfg CFG IMG_S limS enS inp) tr) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet).
  assert (SRZ : SpinAlg.srealizes SEGS (init_config SEGS PC0 PH (en_sp enT) (en_brk enT) (en_mmap_base enT) (en_draw enT) target_alloc_limit inp) K).
  { apply (srealizes_boot_main_adq node SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) nstepA nexitA (minvA ASHM0) (nsafeA NMAX_A ASHM0) fstepS NMAX_A NSA SSA
             _ (amain_at enT inp LIMIT) K).
    - intros K' HK. destruct enT as [sp brk mbase draw]. cbn [en_sp en_brk en_mmap_base en_draw].
      apply (boot_main_ready sp brk mbase draw LIMIT inp Hvi HvT ltac:(unfold LIMIT; lia)). exact HK.
    - intros ms mo_ (w & V & m & HO).
      destruct (IMPL_A enT inp HvT Hvi w V m ms mo_ HO) as [Q HI].
      destruct (safe_A_here enS enT inp HvS HvT Hvi w V m ms mo_ HO) as [HL HT].
      pose proof (HO_parts enT inp w V m ms mo_ HO) as (HMd & _).
      exists _, (treeA enT inp V), (RNGof (A0 V) (MX mo_ [])), (A0 V), Q, (MX mo_ []).
      split.
      { split; [exact HI|]. split; [exact HL|]. split; [exact (AHALT_here enT inp w V m ms mo_ HO)|].
        split; [exact (minvA_main V enT inp mo_ HMd)|]. split; [exact HT| exact (mrel_main V enT inp mo_ HMd)]. }
      split.
      + intros tr Htr. apply HcomplS.
        apply (texit_wexit_wins ssegs _ _ _ _ (sim_AS_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
        apply tree_traces_exits; [exact HL| exact Htr].
      + intros tr Htr. apply (wins_npeekA SEGS SEGS).
        apply (texit_wexit_wins SEGS _ _ _ _ (sim_SA_here enS enT inp HvS HvT Hvi w V m ms mo_ HO)).
        apply (tree_traces_exits _ _ _ HleavesS). apply HsoundS. exact Htr. }
  split; [exact HerrS|].
  rewrite (run_eq SEGS PC0 PH target_alloc_limit enT inp). cbv zeta. cbn [bh_traces bh_errors]. rewrite init_config_eq in SRZ. split.
  - exact (SpinAlg.srealizes_no_error SEGS _ _ SRZ).
  - intros tr. split.
    + intros H. apply (SpinAlg.srealizes_obs_iff SEGS _ _ SRZ tr). exact H.
    + intros H. apply (SpinAlg.srealizes_obs_iff SEGS _ _ SRZ tr) in H. exact H.
Qed.

End Lim.

(* [comment removed for export] *)
#[using="stkA STKA IMPL_A"] Theorem fuzz_pcap_both_scfg : strong_universal_error_free_T_scfg CFG IMG_S IMG.
Proof.
  intros enS enT inp HvS HvT Hvi.
  exact (fuzz_pcap_both_lim source_alloc_limit (proj1 budgets_ok) enS enT inp HvS HvT Hvi).
Qed.

(* [comment removed for export] *)
#[using="stkA STKA IMPL_A"] Theorem fuzz_pcap_both_main :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target IMG_S IMG.
Proof.
  intros enS enT inp HvS HvT Hvi _.
  exact (fuzz_pcap_both_lim sanitizer_source_limit budgets_ok_san enS enT inp HvS HvT Hvi).
Qed.
End FinalAsan.
End Final_both.
