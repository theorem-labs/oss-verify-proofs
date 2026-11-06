(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsSetShIface OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoIcptSetShI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsSetShIface OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Definition SF5_ENTRY_B : Z := 0x70e54.

(* [comment removed for export] *)
Definition both_setsh_cells : list (Z * nat * Z) := [(0x105f38, 8%nat, 0x107e58); (0x107e58, 8%nat, 0xfc38c)].
Lemma both_setsh_cells_eq : setsh_cellsL both_g_rms both_p_rms both_memset_entry = both_setsh_cells.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wd_in_nat i := lazymatch i with O => idtac | S ?j => wd_in_nat j end.
Ltac wd_in_fast :=
  let G := match goal with |- ?G => eval cbv beta in G end in
  lazymatch G with In (?a, ?n, ?v) ?L =>
    let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                              if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
    wd_in_nat i; exact (nth_error_In L i eq_refl)
  end.


Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) both_setsh_cells.

  Theorem C_setshadow_B : SETSHADOW_AT BSEGS FXOK both_addrs AAINVH SF5_ENTRY_B.
  Proof using CELLS FSB0 HP fsbase.
    apply (C_setshadow BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 SF5_ENTRY_B both_g_rms both_p_rms both_memset_entry).
    - intros fx mem rom addr ra n H regs R1 R2 Hn Hnw Hok Hret Hh1 Hh2 Hh3 H10 H11 H1.
      replace (Z_to_bv 64 SF5_ENTRY_B) with (0x70e54%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact (@both_set_shadow_f5_fp fx mem rom addr ra n H regs (BOTH_SETSHH mem addr ra n R1 R2 Hn Hnw Hok Hret) Hh1 Hh2 Hh3 H10 H11 H1).
    - rewrite both_setsh_cells_eq. exact CELLS.
    - rewrite both_setsh_cells_eq. (lazymatch goal with |- ?G => let G' := eval unfold both_setsh_cells in G in change_no_check G' end).
      repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = both_addrs.
  Hypothesis BT_SEGS : bt_segs bt = BSEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.
  Hypothesis K_setsh : Forall (fun c => In c (bt_consts bt)) both_setsh_cells.

  Lemma HP_setsh_B_bts : forall h, AAINV_props both_addrs (AAINV_HS bt h) (bt_fs bt) BSEGS.
  Proof using BT_SEGS BT_IA. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_props_all bt (holes_lsopt h)). Qed.

  Lemma CELLS_setsh_B_bts : forall h Lc FF B C K M mdl, AAINV_HS bt h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) both_setsh_cells.
  Proof using K_setsh BT_SEGS.
    intros h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in K_setsh, CH |- *. intros c Hc. exact (CH c (K_setsh c Hc)).
  Qed.

  Theorem C_setshadow_bts_B : SETSHADOW_AT BSEGS FXOK both_addrs (AAINV_HS bt) 0x70e54.
  Proof using K_setsh BT_FS BT_SEGS BT_IA. exact (C_setshadow_B FXOK (AAINV_HS bt) (bt_fs bt) HP_setsh_B_bts BT_FS CELLS_setsh_B_bts). Qed.
End BT.
End BoIcptSetShI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstB OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstBE OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZC OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvFZA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstB OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstBE OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsContractsAtB OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.BoRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.BoIcptInstBtS BoIcptSetShI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BoFZP OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZC OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvInstFactsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AzImageBoth.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes BSEGS).

Section FZA.
Context {RC : run_ceil}.
Variable hv : AsAinvOomCell3.BoAinvBoot3.bvars.
#[local] Notation bt := (both_bt hv).
Hypothesis BF : AsKSys10.AsAinvBootF3.boot_facts bt.
Hypothesis ASCN : AsIfaceNM3.as_contracts_n BSEGS fx_ok (bt_ia bt) (AAINV_HS bt) (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) (bt_fs bt).

Ltac in_consts_old := rewrite both_bt_consts; unfold both_consts; cbv zeta; repeat (first [left; reflexivity | right]).
(* [comment removed for export] *)
Ltac in_consts_nat i := lazymatch i with O => idtac | S ?j => in_consts_nat j end.
Ltac in_consts_fast :=
  let G := match goal with |- ?G => eval cbv beta in G end in
  lazymatch G with In (?a, ?n, ?v) ?L =>
    let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                              if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
    in_consts_nat i; exact (nth_error_In L i eq_refl)
  end.
Ltac in_consts := first [in_consts_fast | in_consts_old].
Ltac k_rows :=
  match goal with |- Forall _ ?L => let L' := eval vm_compute in L in change (Forall (fun c => In c (bt_consts bt)) L') end;
  repeat (constructor; [in_consts|]); constructor.
Lemma K_annotate_at : Forall (fun c => In c (bt_consts bt))
  (ann_cellsL both_poison_tab both_m2s_tab_6fac4 both_ann_g_flags both_ann_p_flags both_ann_g_verb both_ann_p_verb both_ann_g_shoff both_ann_p_shoff).
Proof. k_rows. Qed.
Lemma K_setsh_at : Forall (fun c => In c (bt_consts bt)) both_setsh_cells.
Proof. k_rows. Qed.

Lemma wins_nil_ok : AsVocab.as_wins_ok (bt_ia bt) [].
Proof. intros z (lo & hi & Hin & _). destruct Hin. Qed.
Lemma wins_nil_img : forall lo hi, In (lo, hi) (@nil (Z * Z)) ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Proof. intros lo hi Hin. destruct Hin. Qed.

Lemma HP_nil : hprops [] GBOTH (AzBridgeH.SHC_bt bt) (AzBridgeH.AINVH_bt bt).
Proof. exact (AzBridgeH.hprops_bt bt [] GBOTH eq_refl eq_refl both_G_ro_img2 drvA_G_img_al GBOTH_errno wins_nil_ok drvA_G_img_shlo). Qed.

Lemma GC_nil : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 (AzBridgeH.SHC_bt bt) (VSHf HID HIDF) (AINV_f [] GBOTH (AzBridgeH.AINVH_bt bt) PERMf TOPf HID HIDF M0 B0 C0) GKCAP FTOPf fx_ok UINV RZ GBOTH bc cc.
Proof.
  intros IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HIT HB HC Hbc Hcc HF HU.
  exact (gcontracts_both_all_f bt eq_refl (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) ASCN [] wins_nil_ok wins_nil_img PERMf TOPf HID HIDF B0 C0 HB HC bc cc Hbc Hcc FTOPf HF GKCAP (Z.le_refl _)
           IT HIT NXF FS0 UINV HU M0).
Qed.

Lemma HANN_at : h_annot_at BSEGS GBOTH fx_ok (AzBridgeH.AINVH_bt bt) RZ BoFZCertE.BoFZP.ANNOT.
Proof.
  pose proof (AsContractsNB.BoIcptInstBtS.C_annotate_bts_B fx_ok bt eq_refl eq_refl K_annotate_at) as AN.
  pose proof (AzBridgeH.annotate_HL bt BSEGS fx_ok _ AN) as ANW.
  exact (AzBridgeAnn.h_annot_f BSEGS (bt_ia bt) fx_ok (AzBridgeH.AAINV_HL bt) GBOTH both_G_ro_img2 eq_refl (AsVocab.AsCells.as_annot AsVocab.AsCells.both_addrs) ANW).
Qed.
Lemma HSF5_at : h_setsh_at BSEGS GBOTH fx_ok (AzBridgeH.AINVH_bt bt) RZ BoFZCertE.BoFZP.SF5_ENTRY.
Proof.
  pose proof (BoIcptSetShI.C_setshadow_bts_B fx_ok bt eq_refl eq_refl (AsContractsNB.AsContractsAtB.BT_FS_at hv BF) K_setsh_at) as ST.
  exact (AzBridgeSf5.h_setsh_bt_f bt BSEGS fx_ok GBOTH eq_refl BoFZCertE.BoFZP.SF5_ENTRY ST).
Qed.

(* [comment removed for export] *)
Theorem FZ_at :
  callee_contract BSEGS PERM_A_lit GBOTH fx_ok RZ (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) BoDrvHooksA.BoFZ.ceN
  /\ callee_contract BSEGS PERM_A_lit GBOTH fx_ok RZ (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) BoDrvHooksA.BoFZ.ceE.
Proof.
  split.
  - exact (BoFZC.fz_both_callee_N RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) HP_nil GC_nil HANN_at HSF5_at).
  - exact (BoFZC.fz_both_callee_E RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) HP_nil GC_nil HANN_at HSF5_at).
Qed.
End FZA.
End BoDrvFZA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.BoImages OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartup OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvMainA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.BoImages OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartup.BoStartupSound OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartup OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.RunLim OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsContractsAtB OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvInstFactsA BoDrvFZA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvMainA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition main_obl (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (inp : ProcInput) (ch : AP.acs) : Prop :=
  BoStartup.BoStartupSound.hole_obl_f ph sp rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp)
                          (spec (in_argv inp) (in_fs inp)) ch.

(* [comment removed for export] *)
Definition WALK_ROWS {RC : run_ceil} (hv : AsAinvOomCell3.BoAinvBoot3.bvars) : Prop :=
  let bt := both_bt hv in
  MALLOC_KATW BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) MSTK_A (ia_malloc both_addrs) true
  /\ MALLOC_KATW BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk both_addrs) true
  /\ MALLOC_ALT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc both_addrs) true
  /\ MALLOC_ALT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk both_addrs) true
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs)
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_free_thunk both_addrs)
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_opdel both_addrs)
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz both_addrs)
  /\ MALLOC_ALT_SEC BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc both_addrs) true
  /\ MALLOC_ALT_SEC BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk both_addrs) true
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs)
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs)
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs)
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).

Section RootA.
#[local] Notation u := bv_unsigned.
(* [comment removed for export] *)
Hypothesis WALK_all : forall (RC : run_ceil) (hv : AsAinvOomCell3.BoAinvBoot3.bvars),
  AsKSys10.AsAinvBootF3.boot_facts (both_bt hv) -> AsKSys10.AsKSys11.boot_totals (both_bt hv) -> @WALK_ROWS RC hv.
(* [comment removed for export] *)
#[local] Notation KCAP := AzIface.GKCAP.
Lemma HKCAP : 0 <= KCAP. Proof. unfold AzIface.GKCAP. lia. Qed.
Lemma EXT : forall (RC : run_ceil) (hv : AsAinvOomCell3.BoAinvBoot3.bvars),
  AsKSys10.AsAinvBootF3.boot_facts (both_bt hv) -> AsKSys10.AsKSys11.boot_totals (both_bt hv) -> @DRV_EXT RC hv KCAP.
Proof.
  intros RC hv BF BT. destruct (WALK_all RC hv BF BT) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14).
  pose proof (AsContractsNB.ASCN_B_at AzSymStepR.fx_ok hv BF W1 W2 W3 W4 W5 W6 W7 W8) as ASCN.
  destruct (BoDrvFZA.FZ_at hv BF ASCN) as (FZN & FZE).
  split; [exact ASCN|].
  split; [exact (AsContractsNB.ASCNM_B_at AzSymStepR.fx_ok hv BF W5 W6 W7 W8)|].
  split; [exact (AsContractsNB.AsContractsAtB.ASCD_B_at AzSymStepR.fx_ok hv BF W9 W10 W11 W12 W13 W14)|].
  split; [exact FZN | exact FZE].
Qed.

Lemma MAIN_h : forall hs, hs = HS_1 \/ hs = HS_2 -> forall ph sp rdraw brk0 mb inp,
  img_facts BSEGS AT_B ph -> valid_entry BIMG (mkEntry sp brk0 mb rdraw) inp -> valid_input_core inp -> main_obl ph sp rdraw brk0 inp hs.
Proof.
  intros hs Hhs ph sp rdraw brk0 mb inp _ He Hc.
  pose proof (proj1 (valid_entry_unfold _ _ _ _ _ _ _ _ Hc) He) as (Hsp & Hbrk & Hmb & Hfits).
  pose proof Hc as (Hva & Hve & _).
  unfold main_obl, BoStartup.BoStartupSound.hole_obl_f. intros E fx R M model HC Hfx.
  exact (main_sound_A ph sp rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (in_fs inp) Hsp Hva Hve Hfits KCAP HKCAP (Z.le_refl _) EXT hs Hhs E fx R M model HC Hfx).
Qed.
Lemma MAIN_1 : forall ph sp rdraw brk0 mb inp,
  img_facts BSEGS AT_B ph -> valid_entry BIMG (mkEntry sp brk0 mb rdraw) inp -> valid_input_core inp -> main_obl ph sp rdraw brk0 inp BoStartupTabs.BoStartupHSc.HS_1.
Proof. exact (MAIN_h HS_1 (or_introl eq_refl)). Qed.
Lemma MAIN_2 : forall ph sp rdraw brk0 mb inp,
  img_facts BSEGS AT_B ph -> valid_entry BIMG (mkEntry sp brk0 mb rdraw) inp -> valid_input_core inp -> main_obl ph sp rdraw brk0 inp BoStartupTabs.BoStartupHSc.HS_2.
Proof. exact (MAIN_h HS_2 (or_intror eq_refl)). Qed.


(* [comment removed for export] *)
Section StartupAt.
  Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream).
  Variables (uid gid hw : word) (groups : list word) (net : NetQueue).
  Hypotheses (IMG : img_facts BSEGS AT_B ph) (Hsp : valid_sp sp) (Hbrk : valid_brk BSEGS brk0) (Hva : valid_argv argv) (Hve : valid_envp envp).
  Hypotheses (Hfit : entry_stack_fits sp argv envp) (Huid : valid_id uid) (Hhw : valid_hwcap hw).
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis O1 : BoStartup.BoStartupSound.hole_obl_f ph sp rdraw brk0 argv envp fs uid hw T BoStartupTabs.BoStartupHSc.HS_1.
  Hypothesis O2 : BoStartup.BoStartupSound.hole_obl_f ph sp rdraw brk0 argv envp fs uid hw T BoStartupTabs.BoStartupHSc.HS_2.

  Lemma STARTUP_AT_w : forall LIM : Z, LIMIT_S <= LIM ->
    forall (nofile sigmask : word) (abort : bool) (va : VaSize) (urnd : InputStream) (apc : N), Z.of_N apc = AP.a_entry AT_B ->
    realizes BSEGS (init_config BSEGS apc ph sp brk0 mbase rdraw LIM (AsSInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abort va urnd)) T.
  Proof.
    intros LIM HLIM nofile sigmask abort va urnd apc Hpc.
    (* [comment removed for export] *)
    assert (OB : BoStartup.BoStartupSound.hole_obl_f ph sp rdraw brk0 argv envp fs uid hw T both_init_S)
      by (exact (BoStartup.ob_init (SR_realizes BSEGS) ph sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T T_nil O1 O2)).
    rewrite (AsSInit.init_cfg_eqF_at BSEGS AT_B ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abort va urnd LIM apc Hpc).
    change (AP.a_entry AT_B) with (AP.pc both_init_S).
    apply (OB (AsSInit.E0 ph sp rdraw brk0 argv envp uid hw) PropExec.fx0). 2: exact AzSymStepR.fx_ok_fx0.
    exact (AsSInit.init_cs_ok_at BSEGS AT_B ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abort va urnd
             IMG Hsp Hbrk Hva Hve Hfit Huid Hhw LIM HLIM).
  Qed.
End StartupAt.

(* [comment removed for export] *)
Lemma STARTUP_AT : forall LIM : Z, LIMIT_S <= LIM -> forall ph sp rdraw brk0 mbase (inp : ProcInput),
  img_facts BSEGS AT_B ph -> valid_sp sp -> valid_brk BSEGS brk0 ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) -> valid_nofile (in_nofile inp) -> valid_sigmask inp -> in_va_size inp = Sv48 ->
  forall T : TSet, T [] ->
  BoStartup.BoStartupSound.hole_obl_f ph sp rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) T BoStartupTabs.BoStartupHSc.HS_1 ->
  BoStartup.BoStartupSound.hole_obl_f ph sp rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) T BoStartupTabs.BoStartupHSc.HS_2 ->
  forall apc : N, Z.of_N apc = AP.a_entry AT_B ->
  realizes BSEGS (init_config BSEGS apc ph sp brk0 mbase rdraw LIM inp) T.
Proof.
  intros LIM HLIM ph sp rdraw brk0 mbase inp IMG Hsp Hbrk Hva Hve Hfit Huid Hhw _ _ _ T T_nil O1 O2.
  (* [comment removed for export] *)
  exact (STARTUP_AT_w ph sp rdraw brk0 mbase (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
           (in_groups inp) (in_net inp) IMG Hsp Hbrk Hva Hve Hfit Huid Hhw T T_nil O1 O2 LIM HLIM
           (in_nofile inp) (in_sigmask inp) (in_abort_terminal inp) (in_va_size inp) (in_urandom inp)).
Qed.

(* [comment removed for export] *)
Theorem B_root_f_gen : forall LIM : Z, StoreOk.RunLim.LMIN <= LIM -> root_obligation_core_f BIMG LIM spec_of.
Proof.
  intros LIM HLIM. unfold root_obligation_core_f, spec_of. cbn [img_segments img_init_pc img_phdrs BIMG].
  intros sp brk0 mb rnd inp He Hc.
  pose proof (proj1 (valid_entry_unfold _ _ _ _ _ _ _ _ Hc) He) as (Hsp & Hbrk & Hmb & Hfits).
  pose proof Hc as (Hva & Hve & Hvfs & [Huid Hgid] & Hnof & Hsig & Hhw & Hva48).
  change AsanUbsan.M.loaded_segments with BSEGS in *.
  change AsanUbsan.M.phdrs with BPH.
  apply (STARTUP_AT LIM HLIM BPH sp rnd brk0 mb inp both_img_facts Hsp Hbrk Hva Hve Hfits Huid Hhw Hnof Hsig Hva48
           (spec (in_argv inp) (in_fs inp)) (spec_has_nil (in_argv inp) (in_fs inp))).
  - exact (MAIN_1 BPH sp rnd brk0 mb inp both_img_facts He Hc).
  - exact (MAIN_2 BPH sp rnd brk0 mb inp both_img_facts He Hc).
  - reflexivity.
Qed.

(* [comment removed for export] *)
Theorem B_root_gen : forall LIM : Z, StoreOk.RunLim.LMIN <= LIM -> root_obligation_core BIMG LIM spec_of.
Proof. intros LIM HLIM. apply root_obligation_core_of_f. exact (B_root_f_gen LIM HLIM). Qed.

(* [comment removed for export] *)
Theorem B_root_holds : B_root.
Proof. exact (B_root_gen target_alloc_limit StoreOk.RunLim.LMIN_le_target). Qed.
End RootA.
