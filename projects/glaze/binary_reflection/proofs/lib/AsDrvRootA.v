(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: the start-up obligations read inp, with the ELF entry apc and the mmap base; the CONFIG_RSEQ flag of the handoff states; valid_launch, the channel reader and entry_launch_ok_va taken from valid_input_core and valid_entry; A_root_f_gen lifted to the run's segment list by RomStable.run_init). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsSetShIface OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RomStable.
Module AsIcptSetShI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsSetShIface OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Definition SF5_ENTRY_A : Z := 0x703e4.

(* [comment removed for export] *)
Definition asan_setsh_cells : list (Z * nat * Z) := [(0xff290, 8%nat, 0x1011b0); (0x1011b0, 8%nat, 0xf56e4)].
Lemma asan_setsh_cells_eq : setsh_cellsL asan_g_rms asan_p_rms asan_memset_entry = asan_setsh_cells.
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
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) asan_setsh_cells.

  Theorem C_setshadow_A : SETSHADOW_AT ASEGS FXOK asan_addrs AAINVH SF5_ENTRY_A.
  Proof using CELLS FSB0 HP fsbase.
    apply (C_setshadow ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 SF5_ENTRY_A asan_g_rms asan_p_rms asan_memset_entry).
    - intros fx mem rom addr ra n H regs R1 R2 Hn Hnw Hok Hret Hh1 Hh2 Hh3 H10 H11 H1.
      replace (Z_to_bv 64 SF5_ENTRY_A) with (0x703e4%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact (@asan_set_shadow_f5_fp fx mem rom addr ra n H regs (SETSHH mem addr ra n R1 R2 Hn Hnw Hok Hret) Hh1 Hh2 Hh3 H10 H11 H1).
    - rewrite asan_setsh_cells_eq. exact CELLS.
    - rewrite asan_setsh_cells_eq. (lazymatch goal with |- ?G => let G' := eval unfold asan_setsh_cells in G in change_no_check G' end).
      repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = asan_addrs.
  Hypothesis BT_SEGS : bt_segs bt = ASEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.
  Hypothesis K_setsh : Forall (fun c => In c (bt_consts bt)) asan_setsh_cells.

  Lemma HP_setsh_bts : forall h, AAINV_props asan_addrs (AAINV_HS bt h) (bt_fs bt) ASEGS.
  Proof using BT_SEGS BT_IA. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_props_all bt (holes_lsopt h)). Qed.

  Lemma CELLS_setsh_bts : forall h Lc FF B C K M mdl, AAINV_HS bt h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) asan_setsh_cells.
  Proof using K_setsh BT_SEGS.
    intros h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in K_setsh, CH |- *. intros c Hc. exact (CH c (K_setsh c Hc)).
  Qed.

  Theorem C_setshadow_bts : SETSHADOW_AT ASEGS FXOK asan_addrs (AAINV_HS bt) 0x703e4.
  Proof using K_setsh BT_FS BT_SEGS BT_IA. exact (C_setshadow_A FXOK (AAINV_HS bt) (bt_fs bt) HP_setsh_bts BT_FS CELLS_setsh_bts). Qed.
End BT.
End AsIcptSetShI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstA OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAE OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsFZC OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvFZA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstA OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAE OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsContractsAtA OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsIcptInstBtS AsIcptSetShI OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsFZC.AsFZP OSSVerify.Proofs.glaze.binary_reflection.lib.AsFZC OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AzImageAsan.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes ASEGS).

Section FZA.
Context {RC : run_ceil}.
Variable hv : AsAinvBoot3.bvars.
#[local] Notation bt := (asan_bt hv).
Hypothesis BF : AsKSys10.AsAinvBootF3.boot_facts bt.
Hypothesis ASCN : AsIfaceNM3.as_contracts_n ASEGS fx_ok (bt_ia bt) (AAINV_HS bt) (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) (bt_fs bt).

Ltac in_consts_old := rewrite asan_bt_consts; unfold asan_consts; cbv zeta; repeat (first [left; reflexivity | right]).
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
  (ann_cellsL asan_poison_tab asan_m2s_tab_6fb04 asan_ann_g_flags asan_ann_p_flags asan_ann_g_verb asan_ann_p_verb asan_ann_g_shoff asan_ann_p_shoff).
Proof. k_rows. Qed.
Lemma K_setsh_at : Forall (fun c => In c (bt_consts bt)) asan_setsh_cells.
Proof. k_rows. Qed.

Lemma wins_nil_ok : AsVocab.as_wins_ok (bt_ia bt) [].
Proof. intros z (lo & hi & Hin & _). destruct Hin. Qed.
Lemma wins_nil_img : forall lo hi, In (lo, hi) (@nil (Z * Z)) ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Proof. intros lo hi Hin. destruct Hin. Qed.

Lemma HP_nil : hprops [] GASAN (AzBridgeH.SHC_bt bt) (AzBridgeH.AINVH_bt bt).
Proof. exact (AzBridgeH.hprops_bt bt [] GASAN eq_refl eq_refl asan_G_ro_img2 drvA_G_img_al GASAN_errno wins_nil_ok drvA_G_img_shlo). Qed.

Lemma GC_nil : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 (AzBridgeH.SHC_bt bt) (VSHf HID HIDF) (AINV_f [] GASAN (AzBridgeH.AINVH_bt bt) PERMf TOPf HID HIDF M0 B0 C0) GKCAP FTOPf fx_ok UINV RZ GASAN bc cc.
Proof.
  intros IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HIT HB HC Hbc Hcc HF HU.
  exact (gcontracts_asan_all_f bt eq_refl (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) ASCN [] wins_nil_ok wins_nil_img PERMf TOPf HID HIDF B0 C0 HB HC bc cc Hbc Hcc FTOPf HF GKCAP (Z.le_refl _)
           IT HIT NXF FS0 UINV HU M0).
Qed.

Lemma HANN_at : h_annot_at ASEGS GASAN fx_ok (AzBridgeH.AINVH_bt bt) RZ AsFZC.AsFZP.ANNOT.
Proof.
  pose proof (AsContractsNB.AsIcptInstBtS.C_annotate_bts fx_ok bt eq_refl eq_refl K_annotate_at) as AN.
  pose proof (AzBridgeH.annotate_HL bt ASEGS fx_ok _ AN) as ANW.
  exact (AzBridgeAnn.h_annot_f ASEGS (bt_ia bt) fx_ok (AzBridgeH.AAINV_HL bt) GASAN asan_G_ro_img2 eq_refl (AsVocab.AsCells.as_annot AsVocab.AsCells.asan_addrs) ANW).
Qed.
Lemma HSF5_at : h_setsh_at ASEGS GASAN fx_ok (AzBridgeH.AINVH_bt bt) RZ AsFZC.AsFZP.SF5_ENTRY.
Proof.
  pose proof (AsIcptSetShI.C_setshadow_bts fx_ok bt eq_refl eq_refl (AsContractsNB.AsContractsAtA.BT_FS_at hv BF) K_setsh_at) as ST.
  exact (AzBridgeSf5.h_setsh_bt_f bt ASEGS fx_ok GASAN eq_refl AsFZC.AsFZP.SF5_ENTRY ST).
Qed.

(* [comment removed for export] *)
Theorem FZ_at :
  callee_contract ASEGS PERM_A_lit GASAN fx_ok RZ (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) AsDrvHooksA.AsFZ.ceN
  /\ callee_contract ASEGS PERM_A_lit GASAN fx_ok RZ (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) AsDrvHooksA.AsFZ.ceE.
Proof.
  split.
  - exact (AsFZC.fz_asan_callee_N RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) HP_nil GC_nil HANN_at HSF5_at).
  - exact (AsFZC.fz_asan_callee_E RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (AzBridgeH.SHC_bt bt) GKCAP (AzBridgeH.AINVH_bt bt) HP_nil GC_nil HANN_at HSF5_at).
Qed.
End FZA.
End AsDrvFZA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartup OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartup.AsStartupSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartup OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.RunLim OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsContractsAtA OSSVerify.Proofs.glaze.binary_reflection.lib.AsContractsNB.AsContractsNA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA AsDrvFZA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* Old beside new.  [AsStartup.AsStartupSound]'s Section Startup moved onto
   the whole [ProcInput] and gained the ELF entry [apc] and the mmap base
   [mbase], so the discharged prefix of [hole_obl_f] moved with it:
     hole_obl_f ph sp rdraw brk0 argv envp fs uid hw T ch
  -> hole_obl_f ph apc sp rdraw brk0 mbase inp T ch
   [argv envp fs uid hw] are gone from the prefix because they are now
   projections of [inp] read inside AsSInit.  [hole_obl_f] is a Definition,
   not a Section lemma, so its prefix is exactly the Section variables its
   BODY mentions -- [ph apc sp rdraw brk0 mbase inp], through [SINV] and
   [argH], and [T] -- and spelling it positionally is sound. *)
Definition main_obl (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput) (ch : AP.acs) : Prop :=
  AsStartup.AsStartupSound.hole_obl_f ph apc sp rdraw brk0 mbase inp (spec (in_argv inp) (in_fs inp)) ch.

(* [comment removed for export] *)
Definition WALK_ROWS {RC : run_ceil} (hv : AsAinvBoot3.bvars) : Prop :=
  let bt := asan_bt hv in
  MALLOC_KATW ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc asan_addrs) true
  /\ MALLOC_KATW ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk asan_addrs) true
  /\ MALLOC_ALT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc asan_addrs) true
  /\ MALLOC_ALT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk asan_addrs) true
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_free asan_addrs)
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_free_thunk asan_addrs)
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_opdel asan_addrs)
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz asan_addrs)
  /\ MALLOC_ALT_SEC ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc asan_addrs) true
  /\ MALLOC_ALT_SEC ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk asan_addrs) true
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_free asan_addrs)
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk asan_addrs)
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel asan_addrs)
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz asan_addrs).

Section RootA.
#[local] Notation u := bv_unsigned.
(* [comment removed for export] *)
Hypothesis WALK_all : forall (RC : run_ceil) (hv : AsAinvBoot3.bvars),
  AsKSys10.AsAinvBootF3.boot_facts (asan_bt hv) -> AsKSys10.AsKSys11.boot_totals (asan_bt hv) -> @WALK_ROWS RC hv.
(* [comment removed for export] *)
#[local] Notation KCAP := AzIface.GKCAP.
Lemma HKCAP : 0 <= KCAP. Proof. unfold AzIface.GKCAP. lia. Qed.
Lemma EXT : forall (RC : run_ceil) (hv : AsAinvBoot3.bvars),
  AsKSys10.AsAinvBootF3.boot_facts (asan_bt hv) -> AsKSys10.AsKSys11.boot_totals (asan_bt hv) -> @DRV_EXT RC hv KCAP.
Proof.
  intros RC hv BF BT. destruct (WALK_all RC hv BF BT) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14).
  pose proof (AsContractsNB.AsContractsNA.ASCN_A_at AzSymStepR.fx_ok hv BF W1 W2 W3 W4 W5 W6 W7 W8) as ASCN.
  destruct (AsDrvFZA.FZ_at hv BF ASCN) as (FZN & FZE).
  split; [exact ASCN|].
  split; [exact (AsContractsNB.AsContractsNA.ASCNM_A_at AzSymStepR.fx_ok hv BF W5 W6 W7 W8)|].
  split; [exact (AsContractsNB.AsContractsAtA.ASCD_A_at AzSymStepR.fx_ok hv BF W9 W10 W11 W12 W13 W14)|].
  split; [exact FZN | exact FZE].
Qed.

Lemma MAIN_h : forall ph (apc : N) sp rdraw brk0 mb inp hs,
  hs = HS_1 (AP.rseq_z (kb_rseq (in_kernel inp))) \/ hs = HS_2 (AP.rseq_z (kb_rseq (in_kernel inp))) ->
  img_facts ASEGS AT_A ph -> Z.of_N apc = AP.a_entry AT_A ->
  valid_entry AIMG (mkEntry sp brk0 mb rdraw) inp -> valid_input_core inp ->
  main_obl ph apc sp rdraw brk0 mb inp hs.
Proof.
  intros ph apc sp rdraw brk0 mb inp hs Hhs _ Hapc He Hc.
  pose proof (proj1 (valid_entry_unfold _ _ _ _ _ _ _ _ Hc) He) as (Hsp & Hbrk & Hmb & Hfits & Hlau).
  (* Taken by ACCESSOR where one exists, by the ten-conjunct shape otherwise:
     [valid_input_core] gained [valid_launch inp] and
     [in_channel_reader inp = true] after [in_va_size inp = Sv48]
     (Common/AsanAcctShape.v:2638-2675), the two clauses AsSInit's Section
     now carries as [Hvl] and [Hrdr]. *)
  pose proof Hc as (Hva & Hve & Hvfs & [Huid Hgid] & Hnof & Hsig & Hhw & _).
  pose proof (valid_input_core_launch inp Hc) as Hvl.
  pose proof (valid_input_core_channel_reader inp Hc) as Hrdr.
  unfold main_obl, AsStartup.AsStartupSound.hole_obl_f. intros E fx R M model HC Hfx.
  (* [main_sound_A] is a Section theorem of AsDrvMainA, whose Section moved
     onto [inp] with everything else; its discharged argument list is
     whatever its PROOF uses and no positional list for it can be checked
     here.  So: unify the conclusion, let [exact HC] pin ph, apc, sp, rdraw,
     brk0, mb and inp -- none of which the conclusion mentions -- and name
     KCAP rather than counting to it.  [HKCAP], [Z.le_refl] and [EXT] are
     the same three witnesses the old positional call passed. *)
  eapply main_sound_A with (KCAP := KCAP).
  all: try exact HC.
  all: solve [ assumption | exact HKCAP | exact (Z.le_refl _) | exact EXT ].
Qed.
Lemma MAIN_1 : forall ph (apc : N) sp rdraw brk0 mb inp,
  img_facts ASEGS AT_A ph -> Z.of_N apc = AP.a_entry AT_A ->
  valid_entry AIMG (mkEntry sp brk0 mb rdraw) inp -> valid_input_core inp ->
  main_obl ph apc sp rdraw brk0 mb inp (AsStartupTabs.AsStartupHSc.HS_1 (AP.rseq_z (kb_rseq (in_kernel inp)))).
Proof. intros ph apc sp rdraw brk0 mb inp. exact (MAIN_h ph apc sp rdraw brk0 mb inp _ (or_introl eq_refl)). Qed.
Lemma MAIN_2 : forall ph (apc : N) sp rdraw brk0 mb inp,
  img_facts ASEGS AT_A ph -> Z.of_N apc = AP.a_entry AT_A ->
  valid_entry AIMG (mkEntry sp brk0 mb rdraw) inp -> valid_input_core inp ->
  main_obl ph apc sp rdraw brk0 mb inp (AsStartupTabs.AsStartupHSc.HS_2 (AP.rseq_z (kb_rseq (in_kernel inp)))).
Proof. intros ph apc sp rdraw brk0 mb inp. exact (MAIN_h ph apc sp rdraw brk0 mb inp _ (or_intror eq_refl)). Qed.


(* [comment removed for export] *)
Section StartupAt.
  (* The section header is AsStartup.v's Section StartupA header, with the
     two clauses AsSInit's Section Init carries and AsStartup's does not
     ([Hapc], [Hmb], [Hrdr]) added, because the lemmas applied below are
     AsSInit's and not AsStartup's.  Old beside new:
       ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
    -> ph apc sp rdraw brk0 mbase inp
     The fourteen component variables are gone with [AsSInit.inp], the
     function that used to BUILD a ProcInput out of them; [inp] is a Section
     variable of AsSInit.Init now and the components are projections. *)
  Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word).
  Variable inp : ProcInput.
  (* The plan's free CONFIG_RSEQ flag, at THIS run's value.  [init_acs3] and
     [asan_init_S] took an [r : Z] at this revision (AsStartupTabs.v:111-115)
     and AsSInit's own [cs0] is [init_acs3 RS A] (AsSInit.v:610) with exactly
     this [RS], so the control state the obligation below is about is
     [asan_init_S RS] and not [asan_init_S]. *)
  #[local] Notation RS := (AP.rseq_z (kb_rseq (in_kernel inp))) (only parsing).
  Hypotheses (IMG : img_facts ASEGS AT_A ph) (Hapc : Z.of_N apc = AP.a_entry AT_A).
  Hypotheses (Hsp : valid_sp sp) (Hbrk : valid_brk ASEGS brk0) (Hmb : valid_mmap_base mbase).
  Hypotheses (Hva : valid_argv (in_argv inp)) (Hve : valid_envp (in_envp inp)).
  Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
  Hypotheses (Huid : valid_id (in_uid inp)) (Hhw : valid_hwcap (in_hwcap inp)).
  (* [Run.valid_input]'s last conjunct, AsSInit.v:111. *)
  Hypothesis Hvl : valid_launch inp.
  (* [valid_input_core]'s reader clause, AsSInit.v:117; it is what discharges
     [cs_ok]'s [co_rdr] by conversion there. *)
  Hypothesis Hrdr : in_channel_reader inp = true.
  (* [Run.valid_entry]'s fifth conjunct, AsSInit.v:120: it pins the stack
     VMA's end and so the image's length. *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis O1 : AsStartup.AsStartupSound.hole_obl_f ph apc sp rdraw brk0 mbase inp T (AsStartupTabs.AsStartupHSc.HS_1 (AP.rseq_z (kb_rseq (in_kernel inp)))).
  Hypothesis O2 : AsStartup.AsStartupSound.hole_obl_f ph apc sp rdraw brk0 mbase inp T (AsStartupTabs.AsStartupHSc.HS_2 (AP.rseq_z (kb_rseq (in_kernel inp)))).

  (* Old beside new.  The [apc] and the five input components this lemma
     used to quantify over existed only to feed [AsSInit.inp]; [apc] moved
     into the section because AsSInit's Section carries it, and the five are
     fields of the section's [inp]:
       forall LIM, LIMIT_S <= LIM -> forall nofile sigmask abort va urnd apc,
         Z.of_N apc = a_entry AT_A ->
         realizes ASEGS (init_config ASEGS apc ph sp brk0 mbase rdraw LIM
                           (AsSInit.inp argv envp fs stdin uid gid hw groups
                                        net nofile sigmask abort va urnd)) T
    -> forall LIM, LIMIT_S <= LIM ->
         realizes ASEGS (init_config ASEGS apc ph sp brk0 mbase rdraw LIM inp) T *)
  Lemma STARTUP_AT_w : forall LIM : Z, LIMIT_S <= LIM ->
    realizes ASEGS (init_config ASEGS apc ph sp brk0 mbase rdraw LIM inp) T.
  Proof.
    intros LIM HLIM.
    (* [AsStartup.ob_init] is a Section lemma of AsStartup's Section StartupA,
       which moved onto [inp] too, so its argument list is given by a tactic
       and only [RR] -- which the conclusion cannot determine, since
       [shape_rel] is not a function type -- is named.  [red] exposes
       [hole_obl_f]'s body so that [hole_oblR (SR_realizes ASEGS) ...] meets
       it by conversion, exactly as the old [exact] relied on. *)
    assert (OB : AsStartup.AsStartupSound.hole_obl_f ph apc sp rdraw brk0 mbase inp T (asan_init_S RS))
      by (red; eapply AsStartup.ob_init with (RR := SR_realizes ASEGS); eassumption).
    (* [A] is named because it does not occur in the equation's left-hand
       side ([init_config] takes no atable), so the rewrite cannot infer it;
       the remaining arguments are AsSInit's discharged hypotheses and are
       left to [assumption]. *)
    rewrite AsSInit.init_cfg_eqF_at with (A := AT_A) by assumption.
    change (AP.a_entry AT_A) with (AP.pc (asan_init_S RS)).
    apply (OB (AsSInit.E0 sp rdraw brk0 inp) PropExec.fx0). 2: exact AzSymStepR.fx_ok_fx0.
    eapply AsSInit.init_cs_ok_at; eassumption.
  Qed.
End StartupAt.

(* [comment removed for export] *)
(* Old beside new.  [apc] moved from a trailing quantifier to a leading one
   because the obligations O1 and O2 now mention it; the three hypotheses
   that were accepted and discarded ([valid_nofile], [valid_sigmask],
   [in_va_size inp = Sv48]) are replaced by the three AsSInit's Section
   actually asks for ([valid_mmap_base], [valid_launch],
   [in_channel_reader inp = true]) plus [entry_launch_ok_va]. *)
Lemma STARTUP_AT : forall LIM : Z, LIMIT_S <= LIM ->
  forall ph (apc : N) sp rdraw brk0 mbase (inp : ProcInput),
  img_facts ASEGS AT_A ph -> Z.of_N apc = AP.a_entry AT_A ->
  valid_sp sp -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
  valid_launch inp -> in_channel_reader inp = true ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
  forall T : TSet, T [] ->
  AsStartup.AsStartupSound.hole_obl_f ph apc sp rdraw brk0 mbase inp T (AsStartupTabs.AsStartupHSc.HS_1 (AP.rseq_z (kb_rseq (in_kernel inp)))) ->
  AsStartup.AsStartupSound.hole_obl_f ph apc sp rdraw brk0 mbase inp T (AsStartupTabs.AsStartupHSc.HS_2 (AP.rseq_z (kb_rseq (in_kernel inp)))) ->
  realizes ASEGS (init_config ASEGS apc ph sp brk0 mbase rdraw LIM inp) T.
Proof.
  intros LIM HLIM ph apc sp rdraw brk0 mbase inp IMG Hapc Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hvl Hrdr Hlau T T_nil O1 O2.
  (* [STARTUP_AT_w] is a Section lemma, so its discharged argument list is
     whatever its proof uses and it is applied rather than spelled. *)
  eapply STARTUP_AT_w; eassumption.
Qed.

(* [comment removed for export] *)
Theorem A_root_f_gen : forall LIM : Z, StoreOk.RunLim.LMIN <= LIM -> root_obligation_core_f AIMG LIM spec_of.
Proof.
  intros LIM HLIM. unfold root_obligation_core_f, spec_of. cbn [img_segments img_init_pc img_phdrs AIMG].
  intros sp brk0 mb rnd inp He Hc.
  pose proof (proj1 (valid_entry_unfold _ _ _ _ _ _ _ _ Hc) He) as (Hsp & Hbrk & Hmb & Hfits & Hlau).
  (* [valid_input_core] has TEN conjuncts (Common/AsanAcctShape.v:2638-2653):
     the repair appended [valid_launch inp] and [in_channel_reader inp = true]
     after [in_va_size inp = Sv48].  An eight-name positional pattern bound
     [Hva48] to the three-way TAIL conjunction instead of the equation, which
     is why the application below was ill-typed.  Taken by ACCESSOR now, the
     shape AsanAcctShape.v:2655-2656 asks for "so that a caller never counts
     conjuncts", and which no further insertion can move. *)
  pose proof Hc as (Hva & Hve & Hvfs & [Huid Hgid] & Hnof & Hsig & Hhw & _).
  pose proof (valid_input_core_launch inp Hc) as Hvl.
  pose proof (valid_input_core_channel_reader inp Hc) as Hrdr.
  change Asan.M.loaded_segments with ASEGS in *.
  change Asan.M.phdrs with APH.
  (* [apc] is left to unification rather than named: the goal's own
     [init_config] carries it, and [reflexivity] below is the same proof of
     [Z.of_N apc = a_entry AT_A] the trailing quantifier used to take. *)
  (* LPS 727298f3: the run reads [run_segments ASEGS ..] from [init_config (run_segments ..) ..];
     the walk over the binary's own segments is lifted there (the image carries no vDSO text). *)
  apply RomStable.run_init; [RomStable.vdso_none |].
  apply (STARTUP_AT LIM HLIM).
  - exact asan_img_facts.
  - reflexivity.
  - exact Hsp.
  - exact Hbrk.
  - exact Hmb.
  - exact Hva.
  - exact Hve.
  - exact Hfits.
  - exact Huid.
  - exact Hhw.
  - exact Hvl.
  - exact Hrdr.
  - exact Hlau.
  - exact (spec_has_nil (in_argv inp) (in_fs inp)).
  (* [apc] is fixed by the goal: [eapply] meets it before the entry equation, which is the
     same [reflexivity] as the second bullet; an [eq_refl] argument met it first. *)
  - eapply (MAIN_1 APH _ sp rnd brk0 mb inp asan_img_facts); [reflexivity | exact He | exact Hc].
  - eapply (MAIN_2 APH _ sp rnd brk0 mb inp asan_img_facts); [reflexivity | exact He | exact Hc].
Qed.

(* [comment removed for export] *)
Theorem A_root_gen : forall LIM : Z, StoreOk.RunLim.LMIN <= LIM -> root_obligation_core AIMG LIM spec_of.
Proof. intros LIM HLIM. apply root_obligation_core_of_f. exact (A_root_f_gen LIM HLIM). Qed.

(* [comment removed for export] *)
Theorem A_root_holds : A_root.
Proof. exact (A_root_gen target_alloc_limit StoreOk.RunLim.LMIN_le_target). Qed.
End RootA.
