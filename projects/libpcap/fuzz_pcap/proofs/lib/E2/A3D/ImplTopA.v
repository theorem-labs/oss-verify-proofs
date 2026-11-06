(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import A3Img.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Stdio Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA ModelX NodesA NodesAS NodesSil ProtoS RunConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed AsanInv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AInstanceF__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_S__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_S__A3W.AHandoffMain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Fuzz_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require ATsafeX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UMainX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require AtMainA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Final_asan__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UMainX__EquivA.TopX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AtMainA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.Final_asan__EquivA.Final_asan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ExitHeapA GStatKit StdioExitInstA ImplA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioExitInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ImplA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition stkA_real : stack_site -> Z := fun s => match s with SiteReadStage => 0x5d0c50 | _ => 0 end.
Lemma stkA_real_ok : UPcapXA.stk_ok stkA_real.
Proof. intros s. unfold stkA_real. destruct s; lia. Qed.
Lemma stkA_real_rs : stkA_real SiteReadStage = READ_STAGE.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition CI_real : list (Z * Z) :=
  [(0x10000, 0xa4000); (0xa7000, 0xa71d8); (0xa71e0, 0xa7200); (0xa7208, 0xa7210); (0xa7218, 0xa7220); (0xa7228, 0xa7238); (0xa7248, 0xa7288);
   (0xa7290, 0xa7308); (0xa7310, 0xa7358); (0xa7368, 0xa7398); (0xa73a0, 0xaaf98); (0xab378, 0xabdb8); (0xabdc5, 0xabdf8); (0xabe0c, 0xabe24);
   (0xabe30, 0xabe4d); (0xabe4e, 0xabe58); (0xabe59, 0xade5c); (0xade5d, 0xade60); (0xade61, 0xade64); (0xade68, 0xae5f8); (0xae604, 0xaf2d8);
   (0xaf2da, 0xaf2e0); (0xaf2f8, 0xaf2fc); (0xaf300, 0xaf800); (0x130830, 0x130860); (0x130863, 0x13e088); (0x13e08c, 0x13e098);
   (0x13e09c, 0x13e0a0); (0x13e0a8, 0x1400c0); (0x1400d0, 0x140148); (0x140150, 0x140178); (0x140180, 0x1401a0); (0x1401a8, 0x1401b1);
   (0x1401b2, 0x1401b8); (0x1401c0, 0x140200); (0x140208, 0x140218); (0x140228, 0x14022c); (0x14022d, 0x1804c8); (0x5d0510, 0x5e14f0); (0x5e16f0, 0x601878);
   (0x601880, 0x602960); (0x602968, 0x603000)].
Lemma CI_real_ok : ci_okb CI_real = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition ci_cov (lo hi : Z) : bool := existsb (fun iv => (fst iv <=? lo) && (hi <=? snd iv)) CI_real.
Lemma ci_cov_ok : forall lo hi, ci_cov lo hi = true -> exists iv, In iv CI_real /\ fst iv <= lo /\ hi <= snd iv.
Proof.
  intros lo hi H. unfold ci_cov in H. apply existsb_exists in H as (iv & Hin & K). apply andb_prop in K as [K1 K2].
  apply Z.leb_le in K1. apply Z.leb_le in K2. exists iv. auto.
Qed.
Lemma CI_real_rs : exists iv, In iv CI_real /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_harn : exists iv, In iv CI_real /\ fst iv <= OUTFILE_ADDR /\ OUTFILE_ADDR + 8 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_atx : Forall (fun k => exists iv, In iv CI_real /\ fst iv <= fst k /\ snd k <= snd iv) ATX_DOM.       (* [comment removed for export] *)
Proof.
  assert (C : forallb (fun k => ci_cov (fst k) (snd k)) ATX_DOM = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros k Hk. apply ci_cov_ok. exact (proj1 (forallb_forall _ _) C k Hk).
Qed.
Lemma CI_real_exit : Forall (fun k => exists iv, In iv CI_real /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP.
Proof.
  assert (C : forallb (fun k => ci_cov (fst k) (snd k)) EXIT_CI_KEEP = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros k Hk. apply ci_cov_ok. exact (proj1 (forallb_forall _ _) C k Hk).
Qed.

(* [comment removed for export] *)
Lemma CI_real_st1 : exists iv, In iv CI_real /\ fst iv <= 0xa9ab0 /\ 0xa9d80 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_st2 : exists iv, In iv CI_real /\ fst iv <= 0x601ca8 /\ 0x6024d0 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_loc : exists iv, In iv CI_real /\ fst iv <= 0x6018a8 /\ 0x6018b0 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_env : Forall (fun k => exists iv, In iv CI_real /\ fst iv <= fst k /\ snd k <= snd iv) StdioCompA.STDIO_ENV_CELLS.
Proof.
  assert (C : forallb (fun k => ci_cov (fst k) (snd k)) StdioCompA.STDIO_ENV_CELLS = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros k Hk. apply ci_cov_ok. exact (proj1 (forallb_forall _ _) C k Hk).
Qed.

(* [comment removed for export] *)
Lemma impl_A_shape : forall (enT : ExecEntry) (inp : ProcInput) (V : nat -> Z) (mo_ : Model) (ms : machine_state),
  (forall Q, implMG (RNGof (A0 V) (MX mo_ []))
               (prog_main (asan_ops (CE := @ceil_of_rc (rcA enT))) (asan_fo site_frameA) stkA_real (argv_Z (in_argv inp)))
               (mkPS (aheap_init (AHandoffDefs.a_space_beg0 V) (AHandoffDefs.a_ptr_array0 V) (AHandoffDefs.resv_of V)) libc_init None 6165744)
               Q ms) ->
  exists Q, implF SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) fstepS (RNGof (A0 V) (MX mo_ [])) (treeA stkA_real enT inp V) Q ms.
Proof.
  intros enT inp V mo_ ms H.
  exists (epostF (fun (_ : unit) (_ : footprint) (_ : machine_state) => True)).
  unfold treeA, TREE_A, prog_main_itree.
  eapply implF_ebind.
  - exact (H (fun _ _ _ _ => True)).
  - intros [e s'] RNG' ms' _. destruct e.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U_real : list (list Z) := drv_traces ++ fuzz_traces.
Lemma U_real_len : (length U_real <= 4096)%nat.
Proof. unfold U_real. rewrite length_app, fuzz_traces_length. cbn. lia. Qed.
Lemma U_real_short : Forall (fun u : list Z => (length u <= 254)%nat) U_real.
Proof.
  unfold U_real. apply Forall_app. split.
  - unfold drv_traces. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
  - eapply Forall_impl; [| exact fuzz_traces_short]. cbv beta. intros u Hu. lia.
Qed.
Lemma U_real_drv : incl drv_traces U_real.
Proof. intros tr H. unfold U_real. apply in_or_app. left. exact H. Qed.
Lemma U_real_fuzz : incl fuzz_traces U_real.
Proof. intros tr H. unfold U_real. apply in_or_app. right. exact H. Qed.

Lemma valid_entry_fits : forall img en inp, valid_input inp -> valid_entry img en inp -> entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).
Proof.
  intros [segs pc ph] [sp brk0 mbase rnd] inp Hvi Hve.
  apply (valid_entry_sv48 _ _ _ (valid_input_sv48 inp Hvi)) in Hve. cbn [en_sp]. exact (proj2 (proj2 (proj2 Hve))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GIOA_run {rc : runConstT} {tlsI : ABase.atlsT} (en : ExecEntry) (inp : ProcInput) :=
  GIOA_real (AI_of CI_real CI_real_ok) (GSTAT_of (cs_all en inp 0)).       (* [comment removed for export] *)

  Theorem IMPL_A_real : forall enT inp, valid_entry IMG enT inp -> valid_input inp ->
    forall w V m ms mo_, amain_open enT inp LIMIT w V m ms mo_ ->
    exists Q, implF SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) fstepS (RNGof (A0 V) (MX mo_ [])) (treeA stkA_real enT inp V) Q ms.
  Proof.
    intros enT inp VE VI w V m ms mo_ HO.
    pose (rcH := rcA enT).
    assert (HP : Forall (pfact_ok V) asan_pure_facts /\ (forall n, 0 <= V n < 2 ^ 64) /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned (en_sp enT)).
    { (nd_pre HO 6%nat; intros _ HVR PIN _ HPF _; nd_post). split; [apply Forall_app in HPF as [X _]; exact X|]. split; [exact HVR|].
      (nd_pre PIN 5%nat; intros _ _ _ E _; nd_post). exact E. }
    (nd_pre HP 3%nat; intros HPd HVRd HUSPd; nd_post).
    pose proof (rcA_ATOP IMG enT inp VI VE) as HATd.
    pose proof (@ATOP_digits rcH V enT HPd HATd HUSPd) as HAT. symmetry in HAT.
    destruct (@tls_at_exists rcH V HPd HAT) as [tlsH HTLS].
    assert (ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
              shad (al_space_beg (mkALayout (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.LV V) w U_real)) <= bv_unsigned p < shad (al_space_beg (mkALayout (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.LV V) w U_real)) + 17179869184 -> A0 V p).
    { intros p Hp Hr. apply (@A0_primary_shadow rcH V enT HPd HATd HUSPd HVRd p Hp).
      rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.LV_space_beg in Hr.
      replace (AtMainA.a_space_beg0 V) with (4096 * (V 208%nat - V 209%nat) + 0x10000) by (unfold AtMainA.a_space_beg0; lia).
      change (2^34) with 17179869184. exact Hr. }
    apply impl_A_shape. intros Q.
    exact (@impl_run rcH tlsH enT inp LIMIT w V m ms mo_ HO HAT HTLS U_real (m_vm_lazy (MX mo_ [])) (A0 V) U_real_len U_real_short
             (A0_init V) ASH0 VI (valid_entry_sp _ _ _ VI VE) (valid_entry_fits _ _ _ VI VE)
             CI_real CI_real_ok CI_real_rs CI_real_exit CI_real_harn CI_real_atx CI_real_st1 CI_real_st2 CI_real_env CI_real_loc stkA_real stkA_real_rs U_real_drv U_real_fuzz Q).
  Qed.

(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require AtMainB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Final_asan__EquivA.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.AcctCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ModelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesAS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesSil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ProtoS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunConst.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_S__A3W.AHandoffMain.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UMainX__EquivA.TopX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AtMainB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.Final_asan__EquivA.Final_both.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.EntryCeil.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioExitInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ImplA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition stkA_real : stack_site -> Z := fun s => match s with SiteReadStage => 0x5d1050 | _ => 0 end.
Lemma stkA_real_ok : UPcapXA.stk_ok stkA_real.
Proof. intros s. unfold stkA_real. destruct s; lia. Qed.
Lemma stkA_real_rs : stkA_real SiteReadStage = READ_STAGE.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition CI_real : list (Z * Z) :=
  [(0x10000, 0xa5000); (0xa7000, 0xa75b8); (0xa75c0, 0xa75e0); (0xa75e8, 0xa75f0); (0xa75f8, 0xa7600); (0xa7608, 0xa7618); (0xa7628, 0xa7668);
   (0xa7670, 0xa76e8); (0xa76f0, 0xa7738); (0xa7748, 0xa7778); (0xa7780, 0xab398); (0xab778, 0xac1b8); (0xac1c5, 0xac1f8); (0xac20c, 0xac224);
   (0xac230, 0xac24d); (0xac24e, 0xac258); (0xac259, 0xae25c); (0xae25d, 0xae260); (0xae261, 0xae264); (0xae268, 0xae9f8); (0xaea04, 0xaf6d8);
   (0xaf6da, 0xaf6e0); (0xaf6f8, 0xaf6fc); (0xaf700, 0xafc00); (0x130c30, 0x130c60); (0x130c63, 0x13e488); (0x13e48c, 0x13e498);
   (0x13e49c, 0x13e4a0); (0x13e4a8, 0x1404c0); (0x1404d0, 0x140548); (0x140550, 0x140578); (0x140580, 0x1405a0); (0x1405a8, 0x1405b1);
   (0x1405b2, 0x1405b8); (0x1405c0, 0x140600); (0x140608, 0x140618); (0x140628, 0x14062c); (0x14062d, 0x1808c8); (0x5d0910, 0x5e18f0); (0x5e1af0, 0x601c78);
   (0x601c80, 0x602d60); (0x602d68, 0x604000)].
Lemma CI_real_ok : ci_okb CI_real = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition ci_cov (lo hi : Z) : bool := existsb (fun iv => (fst iv <=? lo) && (hi <=? snd iv)) CI_real.
Lemma ci_cov_ok : forall lo hi, ci_cov lo hi = true -> exists iv, In iv CI_real /\ fst iv <= lo /\ hi <= snd iv.
Proof.
  intros lo hi H. unfold ci_cov in H. apply existsb_exists in H as (iv & Hin & K). apply andb_prop in K as [K1 K2].
  apply Z.leb_le in K1. apply Z.leb_le in K2. exists iv. auto.
Qed.
Lemma CI_real_rs : exists iv, In iv CI_real /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_harn : exists iv, In iv CI_real /\ fst iv <= OUTFILE_ADDR /\ OUTFILE_ADDR + 8 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_atx : Forall (fun k => exists iv, In iv CI_real /\ fst iv <= fst k /\ snd k <= snd iv) ATX_DOM.       (* [comment removed for export] *)
Proof.
  assert (C : forallb (fun k => ci_cov (fst k) (snd k)) ATX_DOM = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros k Hk. apply ci_cov_ok. exact (proj1 (forallb_forall _ _) C k Hk).
Qed.
Lemma CI_real_exit : Forall (fun k => exists iv, In iv CI_real /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP.
Proof.
  assert (C : forallb (fun k => ci_cov (fst k) (snd k)) EXIT_CI_KEEP = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros k Hk. apply ci_cov_ok. exact (proj1 (forallb_forall _ _) C k Hk).
Qed.

(* [comment removed for export] *)
Lemma CI_real_st1 : exists iv, In iv CI_real /\ fst iv <= 0xa9e90 /\ 0xaa160 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_st2 : exists iv, In iv CI_real /\ fst iv <= 0x6020a8 /\ 0x6028d0 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_loc : exists iv, In iv CI_real /\ fst iv <= 0x601ca8 /\ 0x601cb0 <= snd iv.
Proof. apply ci_cov_ok. vm_compute. reflexivity. Qed.
Lemma CI_real_env : Forall (fun k => exists iv, In iv CI_real /\ fst iv <= fst k /\ snd k <= snd iv) A3S.StdioCompA.TwB.STDIO_ENV_CELLS.
Proof.
  assert (C : forallb (fun k => ci_cov (fst k) (snd k)) A3S.StdioCompA.TwB.STDIO_ENV_CELLS = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros k Hk. apply ci_cov_ok. exact (proj1 (forallb_forall _ _) C k Hk).
Qed.

(* [comment removed for export] *)
Lemma impl_A_shape : forall (enT : ExecEntry) (inp : ProcInput) (V : nat -> Z) (mo_ : Model) (ms : machine_state),
  (forall Q, implMG (RNGof (A0 V) (MX mo_ []))
               (prog_main (asan_ops (CE := @ceil_of_rc (rcA enT))) (asan_fo site_frameA) stkA_real (argv_Z (in_argv inp)))
               (mkPS (aheap_init (A3W.AHandoffDefs.TwB.a_space_beg0 V) (A3W.AHandoffDefs.TwB.a_ptr_array0 V) (A3W.AHandoffDefs.TwB.resv_of V)) libc_init None 6166768)
               Q ms) ->
  exists Q, implF SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) fstepS (RNGof (A0 V) (MX mo_ [])) (treeA stkA_real enT inp V) Q ms.
Proof.
  intros enT inp V mo_ ms H.
  exists (epostF (fun (_ : unit) (_ : footprint) (_ : machine_state) => True)).
  unfold treeA, TREE_A, prog_main_itree.
  eapply implF_ebind.
  - exact (H (fun _ _ _ _ => True)).
  - intros [e s'] RNG' ms' _. destruct e.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U_real : list (list Z) := drv_traces ++ fuzz_traces.
Lemma U_real_len : (length U_real <= 4096)%nat.
Proof. unfold U_real. rewrite length_app, fuzz_traces_length. cbn. lia. Qed.
Lemma U_real_short : Forall (fun u : list Z => (length u <= 254)%nat) U_real.
Proof.
  unfold U_real. apply Forall_app. split.
  - unfold drv_traces. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
  - eapply Forall_impl; [| exact fuzz_traces_short]. cbv beta. intros u Hu. lia.
Qed.
Lemma U_real_drv : incl drv_traces U_real.
Proof. intros tr H. unfold U_real. apply in_or_app. left. exact H. Qed.
Lemma U_real_fuzz : incl fuzz_traces U_real.
Proof. intros tr H. unfold U_real. apply in_or_app. right. exact H. Qed.

Lemma valid_entry_fits : forall img en inp, valid_input inp -> valid_entry img en inp -> entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).
Proof.
  intros [segs pc ph] [sp brk0 mbase rnd] inp Hvi Hve.
  apply (valid_entry_sv48 _ _ _ (valid_input_sv48 inp Hvi)) in Hve. cbn [en_sp]. exact (proj2 (proj2 (proj2 Hve))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GIOA_run {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} (en : ExecEntry) (inp : ProcInput) :=
  GIOA_real (AI_of CI_real CI_real_ok) (GSTAT_of (cs_all en inp 0)).       (* [comment removed for export] *)

  Theorem IMPL_A_real : forall enT inp, valid_entry IMG enT inp -> valid_input inp ->
    forall w V m ms mo_, amain_open enT inp LIMIT w V m ms mo_ ->
    exists Q, implF SEGS (at_nodeA SEGS) (silA ASHM0) (npeekA SEGS) fstepS (RNGof (A0 V) (MX mo_ [])) (treeA stkA_real enT inp V) Q ms.
  Proof.
    intros enT inp VE VI w V m ms mo_ HO.
    pose (rcH := rcA enT).
    assert (HP : Forall (pfact_ok V) asan_pure_facts /\ (forall n, 0 <= V n < 2 ^ 64) /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned (en_sp enT)).
    { (nd_pre HO 6%nat; intros _ HVR PIN _ HPF _; nd_post). split; [apply Forall_app in HPF as [X _]; exact X|]. split; [exact HVR|].
      (nd_pre PIN 5%nat; intros _ _ _ E _; nd_post). exact E. }
    (nd_pre HP 3%nat; intros HPd HVRd HUSPd; nd_post).
    pose proof (rcA_ATOP IMG enT inp VI VE) as HATd.
    pose proof (@ATOP_digits rcH V enT HPd HATd HUSPd) as HAT. symmetry in HAT.
    destruct (@tls_at_exists rcH V HPd HAT) as [tlsH HTLS].
    assert (ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
              shad (al_space_beg (mkALayout (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.LV V) w U_real)) <= bv_unsigned p < shad (al_space_beg (mkALayout (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.LV V) w U_real)) + 17179869184 -> A0 V p).
    { intros p Hp Hr. apply (@A0_primary_shadow rcH V enT HPd HATd HUSPd HVRd p Hp).
      rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.LV_space_beg in Hr.
      replace (AtMainB.a_space_beg0 V) with (4096 * (V 208%nat - V 209%nat) + 0x10000) by (unfold AtMainB.a_space_beg0; lia).
      change (2^34) with 17179869184. exact Hr. }
    apply impl_A_shape. intros Q.
    exact (@impl_run rcH tlsH enT inp LIMIT w V m ms mo_ HO HAT HTLS U_real (m_vm_lazy (MX mo_ [])) (A0 V) U_real_len U_real_short
             (A0_init V) ASH0 VI (valid_entry_sp _ _ _ VI VE) (valid_entry_fits _ _ _ VI VE)
             CI_real CI_real_ok CI_real_rs CI_real_exit CI_real_harn CI_real_atx CI_real_st1 CI_real_st2 CI_real_env CI_real_loc stkA_real stkA_real_rs U_real_drv U_real_fuzz Q).
  Qed.
End TwB.
