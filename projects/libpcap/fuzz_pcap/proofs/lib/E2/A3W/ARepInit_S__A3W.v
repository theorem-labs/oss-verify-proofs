(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require PrimaryShadow0.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_init__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ARepInit_S.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require PrimaryShadow0. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.PrimaryShadow0.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lv_lit k := let b := eval lazy [Nat.eqb] in (Nat.eqb k k) in constr_eq b true.
Local Ltac lv_lits := repeat match goal with |- context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v end.
Local Ltac lv_lits_in H := repeat match type of H with context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v in H end.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Hypothesis SH1 : ashadow1 V m.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.

  #[using="rc V U HM HU"] Lemma premap_cells_init : premap_cells m.
  Proof.
    unfold premap_cells.
    aimg V m HM 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] I1.
    mf V m HM (MCell (ZLit 0x13e0a0) 8 (ZLit 4096)) F1.
    mf8 V m HM 0x1401b8 0 F2.
    mf8 V m HM 0x140200 1103823372544 F3.
    assert (F3' : rw_cells asegs m 1311232 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                                           C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F3.
    mf8 V m HM 0x140218 72339073309605888 F4.
    assert (F4' : rw_cells asegs m 1311256 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F4.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 0x601878) 8 (ZLit 4096)) F6.
    split; [exact I1|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3'|]. split; [exact F4'|]. split; [apply premap_canary_any| exact F6].   (* [comment removed for export] *)
  Qed.

  #[using="rc HM HU"] Lemma asec_inst_init : asec_inst L m.
  Proof.
    unfold asec_inst.
    mf V m HM (MCell (ZLit 0xaafe8) 8 (ZMul (ZLit 4096) (ZV 226))) F1.
    aimg V m HM 0xab018 [C1 (Z_to_bv 8 0)] I2.
    aimg V m HM 0xab020 [CB 32 (repeat (Z_to_bv 8 0) 32)] I3.
    aimg V m HM 0xab040 [CB 512 (repeat (Z_to_bv 8 0) 512)] I4.
    mf V m HM (MZeroC (ZLit 700993) 3) F5.
    assert (F5' : rw_cells asegs m 700993 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F5.
    aimg V m HM 0xab258 [CB 16 (repeat (Z_to_bv 8 0) 16)] I6.
    split; [exact F1|]. split; [exists (Z_to_bv 8 0); exact I2|]. split; [exists (repeat (Z_to_bv 8 0) 32); exact I3|].
    split; [exists (repeat (Z_to_bv 8 0) 512); exact I4|]. split; [exact F5'|]. exists (repeat (Z_to_bv 8 0) 16); exact I6.
  Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Lemma asec_arr_init : asec_arr L (ST0 V) [] m.
  Proof.
    (pose proof (ao_ptr _ (alayout_ok_init V w U HP HU HAT HTLS)) as ndP__; nd_pre ndP__ 3%nat; intros _ P1 P2; nd_post). atop_facts. change (mkALayout (LV V) w U) with L in P1, P2.
    exists []. split; [apply Permutation_refl|]. cbn [map a_nsec a_nres ST0 ainit].
    split; [apply u64arr_nil; lia|]. split; [| intros i ch Hi; destruct i; discriminate].
    exists []. rewrite Z.add_0_r. change (Z.to_nat (8 * (0 - 0))) with 0%nat. apply rw_cells_CB0; lia.
  Qed.

  #[using="HP HU HAT HTLS"] Lemma asec_wf_init : asec_wf L (ST0 V) [].
  Proof.
    unfold asec_wf. split; [exact (alayout_ok_init V w U HP HU HAT HTLS)|]. cbn. split; [reflexivity|]. split; [split; [reflexivity| lia]|]. split; [reflexivity|]. split; [lia|].
    split; [constructor| exact sec_disjoint_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="rc HP HU SH0"] Lemma aprim0_init : aprim0 L m.
  Proof.
    unfold aprim0. destruct (primary_shadow0 V m SH0 HP) as [Z0 W0]. rewrite (sb_eq' V w U HU) in Z0, W0. change (mkALayout (LV V) w U) with L in Z0, W0.
    unfold K_REGION. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.shlen_div. change (2 ^ 32 / 8) with 536870912. change (2^34) with 17179869184 in Z0, W0.
    split; [intros i Hi; apply Z0; lia|].
    (nd_pre W0 3%nat; intros W1 W2 W3; nd_post). split; [exact W1|]. split; [lia|]. intros i Hi. apply W3. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HM HP HU HAT SH0 SH1"] Lemma ashz_init : ashz L [] m.
  Proof.
    intros x Hx HF _. pose proof SH0 as SZ. unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.
    pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
    pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 6 0 255) P6.
    unfold astartup_hulls in HF. cbn [al_V L] in HF; lv_lits_in HF.
    unfold al_store, al_nodes, al_fake, al_dtls, al_ctx, al_t, al_res, al_ptr_array in HF. cbn [al_V L] in HF; lv_lits_in HF.
    repeat lazymatch type of HF with
           | Forall _ (_ :: _) => let H1 := fresh "NH" in pose proof (Forall_inv HF) as H1; cbn [fst snd] in H1; apply Forall_inv_tail in HF
           | _ => clear HF
           end.
    assert (SX : shad x = ASHOFF + x / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity). unfold ASHOFF in SX.
    (* [comment removed for export] *)
    destruct (Z.lt_ge_cases x (32768 * V 0%nat + 4096 * V 10%nat - 8388608)) as [LOW|WIN].
    - (* [comment removed for export] *)
      apply (shadow_zero_pt V m (shad x) SH1 HM HP).
      + unfold ashadow. rewrite SX. clear -Hx HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
      + rewrite SX. clear -Hx. unfold AIMG_HI, KLS, K_HIGH_MEM in Hx. Z.div_mod_to_equations. lia.
      + rewrite SX. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.ASHOFF. intros X.
        match goal with NHk : ~ _ |- _ => solve [clear -X NHk P208 P209; Z.div_mod_to_equations; lia] end.
      + rewrite SX. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.ASHOFF. intros X.
        match goal with NHk : ~ _ |- _ => solve [clear -X NHk P208 P209; Z.div_mod_to_equations; lia] end.
    - mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
                        (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
      rewrite SX.
      replace (2147450880 + x / 8) with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (x / 8 - 4096 * V 0%nat - 512 * V 10%nat + 1048576))
        by (clear; lia).
      apply ZW. clear -Hx WIN HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  #[using="HM HP HU HAT HTLS SH0 SH1"] Theorem ASECc_init : ASECc [] L (ST0 V) X0 m.
  Proof.
    split; [exact asec_wf_init|]. split; [exact asec_arr_init|]. split; [exact asec_inst_init|]. split; [exact aprim0_init| exact ashz_init].
  Qed.

  #[using="Type"] Lemma sec_chunks_of_ST0 : sec_chunks_of (ST0 V) = [].
  Proof. unfold sec_chunks_of, achunks, ST0, ainit. cbn. rewrite ?map_to_list_empty. reflexivity. Qed.

  #[using="HM HP HU HAT HTLS SH0 SH1"] Theorem ASEC_of_init : ASEC_of L (ST0 V) X0 m.
  Proof. unfold ASEC_of. rewrite sec_chunks_of_ST0. exact ASECc_init. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.PrimaryShadow0.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_D.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lv_lit k := let b := eval lazy [Nat.eqb] in (Nat.eqb k k) in constr_eq b true.
Local Ltac lv_lits := repeat match goal with |- context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v end.
Local Ltac lv_lits_in H := repeat match type of H with context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v in H end.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Hypothesis SH1 : ashadow1 V m.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.

  #[using="rc V U HM HU"] Lemma premap_cells_init : premap_cells m.
  Proof.
    unfold premap_cells.
    aimg V m HM 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] I1.
    mf V m HM (MCell (ZLit 0x13e4a0) 8 (ZLit 4096)) F1.
    mf8 V m HM 0x1405b8 0 F2.
    mf8 V m HM 0x140600 1103823372544 F3.
    assert (F3' : rw_cells asegs m 1312256 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                                           C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F3.
    mf8 V m HM 0x140618 72339073309605888 F4.
    assert (F4' : rw_cells asegs m 1312280 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F4.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 0x601c78) 8 (ZLit 4096)) F6.
    split; [exact I1|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3'|]. split; [exact F4'|]. split; [apply premap_canary_any| exact F6].   (* [comment removed for export] *)
  Qed.

  #[using="rc HM HU"] Lemma asec_inst_init : asec_inst L m.
  Proof.
    unfold asec_inst.
    mf V m HM (MCell (ZLit 0xab3e8) 8 (ZMul (ZLit 4096) (ZV 226))) F1.
    aimg V m HM 0xab418 [C1 (Z_to_bv 8 0)] I2.
    aimg V m HM 0xab420 [CB 32 (repeat (Z_to_bv 8 0) 32)] I3.
    aimg V m HM 0xab440 [CB 512 (repeat (Z_to_bv 8 0) 512)] I4.
    mf V m HM (MZeroC (ZLit 702017) 3) F5.
    assert (F5' : rw_cells asegs m 702017 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F5.
    aimg V m HM 0xab658 [CB 16 (repeat (Z_to_bv 8 0) 16)] I6.
    split; [exact F1|]. split; [exists (Z_to_bv 8 0); exact I2|]. split; [exists (repeat (Z_to_bv 8 0) 32); exact I3|].
    split; [exists (repeat (Z_to_bv 8 0) 512); exact I4|]. split; [exact F5'|]. exists (repeat (Z_to_bv 8 0) 16); exact I6.
  Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Lemma asec_arr_init : asec_arr L (ST0 V) [] m.
  Proof.
    (pose proof (ao_ptr _ (alayout_ok_init V w U HP HU HAT HTLS)) as ndP__; nd_pre ndP__ 3%nat; intros _ P1 P2; nd_post). atop_facts. change (mkALayout (LV V) w U) with L in P1, P2.
    exists []. split; [apply Permutation_refl|]. cbn [map a_nsec a_nres ST0 ainit].
    split; [apply u64arr_nil; lia|]. split; [| intros i ch Hi; destruct i; discriminate].
    exists []. rewrite Z.add_0_r. change (Z.to_nat (8 * (0 - 0))) with 0%nat. apply rw_cells_CB0; lia.
  Qed.

  #[using="HP HU HAT HTLS"] Lemma asec_wf_init : asec_wf L (ST0 V) [].
  Proof.
    unfold asec_wf. split; [exact (alayout_ok_init V w U HP HU HAT HTLS)|]. cbn. split; [reflexivity|]. split; [split; [reflexivity| lia]|]. split; [reflexivity|]. split; [lia|].
    split; [constructor| exact sec_disjoint_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="rc HP HU SH0"] Lemma aprim0_init : aprim0 L m.
  Proof.
    unfold aprim0. destruct (primary_shadow0 V m SH0 HP) as [Z0 W0]. rewrite (sb_eq' V w U HU) in Z0, W0. change (mkALayout (LV V) w U) with L in Z0, W0.
    unfold K_REGION. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB.shlen_div. change (2 ^ 32 / 8) with 536870912. change (2^34) with 17179869184 in Z0, W0.
    split; [intros i Hi; apply Z0; lia|].
    (nd_pre W0 3%nat; intros W1 W2 W3; nd_post). split; [exact W1|]. split; [lia|]. intros i Hi. apply W3. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HM HP HU HAT SH0 SH1"] Lemma ashz_init : ashz L [] m.
  Proof.
    intros x Hx HF _. pose proof SH0 as SZ. unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.
    pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
    pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 6 0 255) P6.
    unfold astartup_hulls in HF. cbn [al_V L] in HF; lv_lits_in HF.
    unfold al_store, al_nodes, al_fake, al_dtls, al_ctx, al_t, al_res, al_ptr_array in HF. cbn [al_V L] in HF; lv_lits_in HF.
    repeat lazymatch type of HF with
           | Forall _ (_ :: _) => let H1 := fresh "NH" in pose proof (Forall_inv HF) as H1; cbn [fst snd] in H1; apply Forall_inv_tail in HF
           | _ => clear HF
           end.
    assert (SX : shad x = ASHOFF + x / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity). unfold ASHOFF in SX.
    (* [comment removed for export] *)
    destruct (Z.lt_ge_cases x (32768 * V 0%nat + 4096 * V 10%nat - 8388608)) as [LOW|WIN].
    - (* [comment removed for export] *)
      apply (shadow_zero_pt V m (shad x) SH1 HM HP).
      + unfold ashadow. rewrite SX. clear -Hx HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
      + rewrite SX. clear -Hx. unfold AIMG_HI, KLS, K_HIGH_MEM in Hx. Z.div_mod_to_equations. lia.
      + rewrite SX. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.ASHOFF. intros X.
        match goal with NHk : ~ _ |- _ => solve [clear -X NHk P208 P209; Z.div_mod_to_equations; lia] end.
      + rewrite SX. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.ASHOFF. intros X.
        match goal with NHk : ~ _ |- _ => solve [clear -X NHk P208 P209; Z.div_mod_to_equations; lia] end.
    - mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
                        (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
      rewrite SX.
      replace (2147450880 + x / 8) with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (x / 8 - 4096 * V 0%nat - 512 * V 10%nat + 1048576))
        by (clear; lia).
      apply ZW. clear -Hx WIN HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  #[using="HM HP HU HAT HTLS SH0 SH1"] Theorem ASECc_init : ASECc [] L (ST0 V) X0 m.
  Proof.
    split; [exact asec_wf_init|]. split; [exact asec_arr_init|]. split; [exact asec_inst_init|]. split; [exact aprim0_init| exact ashz_init].
  Qed.

  #[using="Type"] Lemma sec_chunks_of_ST0 : sec_chunks_of (ST0 V) = [].
  Proof. unfold sec_chunks_of, achunks, ST0, ainit. cbn. rewrite ?map_to_list_empty. reflexivity. Qed.

  #[using="HM HP HU HAT HTLS SH0 SH1"] Theorem ASEC_of_init : ASEC_of L (ST0 V) X0 m.
  Proof. unfold ASEC_of. rewrite sec_chunks_of_ST0. exact ASECc_init. Qed.
End S.
End CANSEC1.
End TwB.
End ARepInit_S.

(* [comment removed for export] *)
Module AHandoffMain.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_init__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_init. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_S__A3W.ARepInit_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ADepot_init OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_init OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ARepInit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma tls_at_exists : forall V : nat -> Z,
  Forall (pfact_ok V) asan_pure_facts ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  exists tlsI : ABase.atlsT, @tls_at rc tlsI V.
Proof.
  intros V HP HAT.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10.
  assert (B01 : forall b : bool, 0 <= (if b then 1 else 0) <= 1) by (intros [|]; clear; Stdlib.micromega.Lia.lia).
  unshelve eexists (@ABase.ATls rc 0x5e15b8 0 0
                      (if 6165744 <? 4096 * V 208%nat then 1 else 0) (if 6165744 <? 4096 * V 227%nat then 1 else 0)
                      (4096 * V 207%nat) _ _ _ _ _ _).
  - reflexivity.
  - clear. lia.
  - clear - P0 P10 HAT. lia.
  - split; [split; clear; lia | split; apply B01].
  - split; reflexivity.
  - clear. lia.
  - unfold tls_at. cbn [ABase.ATPv ABase.kt_res ABase.kt_t ABase.AAHMv]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem aheap_at_main : forall (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model)
    (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop),
  amain_open en inp lim w V m ms mo ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
  (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
  (forall p : word, bv_unsigned p mod 4096 = 0 ->
     shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
  exists tlsI : ABase.atlsT,
    @tls_at rc tlsI V
    /\ AHEAP_P (AHQ adepot_iface ASEC_of AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros en inp lim w V m ms mo U lz AL AM HAT LU FU A0I ASH0.
  (nd_pre AM 11%nat; intros _ _ _ HMall HPall _ _ _ SH0 _ SH1; nd_post).
  apply Forall_app in HMall as [HM HMW]. apply Forall_app in HPall as [HP _].
  destruct (tls_at_exists V HP HAT) as [tlsI HTLS]. exists tlsI. split; [exact HTLS|].
  assert (HU : (length U <= Z.to_nat AUMAX)%nat) by (unfold AUMAX; lia).
  apply (AHEAP_P_init_qdf ASEC_of V w U m lz AL); try assumption.
  apply (ASEC_of_init V w U m HM HP HU HAT HTLS SH0 SH1).
Qed.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_S__A3W.ARepInit_S.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ADepot_init.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_init.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ARepInit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma tls_at_exists : forall V : nat -> Z,
  Forall (pfact_ok V) asan_pure_facts ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  exists tlsI : A3W.ABase.TwB.atlsT, @tls_at rc tlsI V.
Proof.
  intros V HP HAT.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10.
  assert (B01 : forall b : bool, 0 <= (if b then 1 else 0) <= 1) by (intros [|]; clear; Stdlib.micromega.Lia.lia).
  unshelve eexists (@A3W.ABase.TwB.ATls rc 0x5e19b8 0 0
                      (if 6166768 <? 4096 * V 208%nat then 1 else 0) (if 6166768 <? 4096 * V 227%nat then 1 else 0)
                      (4096 * V 207%nat) _ _ _ _ _ _).
  - reflexivity.
  - clear. lia.
  - clear - P0 P10 HAT. lia.
  - split; [split; clear; lia | split; apply B01].
  - split; reflexivity.
  - clear. lia.
  - unfold tls_at. cbn [A3W.ABase.TwB.ATPv A3W.ABase.TwB.kt_res A3W.ABase.TwB.kt_t A3W.ABase.TwB.AAHMv]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem aheap_at_main : forall (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model)
    (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop),
  amain_open en inp lim w V m ms mo ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
  (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
  (forall p : word, bv_unsigned p mod 4096 = 0 ->
     shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
  exists tlsI : A3W.ABase.TwB.atlsT,
    @tls_at rc tlsI V
    /\ AHEAP_P (AHQ adepot_iface ASEC_of AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros en inp lim w V m ms mo U lz AL AM HAT LU FU A0I ASH0.
  (nd_pre AM 11%nat; intros _ _ _ HMall HPall _ _ _ SH0 _ SH1; nd_post).
  apply Forall_app in HMall as [HM HMW]. apply Forall_app in HPall as [HP _].
  destruct (tls_at_exists V HP HAT) as [tlsI HTLS]. exists tlsI. split; [exact HTLS|].
  assert (HU : (length U <= Z.to_nat AUMAX)%nat) by (unfold AUMAX; lia).
  apply (AHEAP_P_init_qdf ASEC_of V w U m lz AL); try assumption.
  apply (ASEC_of_init V w U m HM HP HU HAT HTLS SH0 SH1).
Qed.
End CANSEC1.
End TwB.
End AHandoffMain.
