(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvGSoundA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma drvA_G_img_al : 0 <= g_img_lo GASAN /\ g_img_lo GASAN mod 8 = 0 /\ g_img_hi GASAN mod 8 = 0.
Proof. cbn. repeat split; reflexivity || lia. Qed.
Lemma drvA_G_img_shlo : g_img_hi GASAN <= SHMAPLO.
Proof. cbn. unfold SHMAPLO. lia. Qed.

Section GSoundA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
(* [comment removed for export] *)
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).          (* [comment removed for export] *)
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).

(* [comment removed for export] *)
Hypothesis XNa_sound : GPS.ext_stmt ASEGS NXD XNa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Hypothesis XEa_sound : GPS.emit_stmt ASEGS NXD XEa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Hypothesis XAa_sound : GPS.alt2_stmt ASEGS NXD XAa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Hypothesis XTa_sound : GPS.term_stmt ASEGS XTa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.

Lemma XB0_sound : GPS.ext2_stmt ASEGS NXD XB0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof. intros id args cs csa csb E fx R M model T _ Hn. discriminate Hn. Qed.

(* [comment removed for export] *)
Variable D : env -> Fs.Fs -> TSet.
Hypothesis D_agree : forall E E' fs, env_agree NXD E E' -> D E fs = D E' fs.
Hypothesis D_nil : forall E fs, D E fs [].
#[local] Notation HOLES := (fun (_ : nat) E fs => D E fs).

Theorem drvA_cert_sound : forall hs bf fuel p cs s,
  gplan_ok p = true ->
  CHKa hs bf fuel cs p = COk s ->
  GPS.holes_stmt ASEGS hs PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV HOLES RZ ->
  forall E fx R M model, cs_okA E cs fx R M model ->
  RZ (cfgF ASEGS fx R (pc cs) M model) (sd HOLES (D E (m_fs model)) E (m_fs model) s).
Proof.
  intros hs bf fuel p cs s Hgp Hc HSs E fx R M model HC.
  exact (GPS.check_soundA ASEGS ITA ITA_ok AASAN NXD LIMIT hs XNa XEa XB0 XAa XTa 0%nat SWIN PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc
           (AINV_f_frame SWIN GASAN SHC AINVH HP asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c)
           (AINV_f_lazy SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c)
           ltac:(intros; rewrite asan_A_img_hi, asan_A_img_lo; eapply (AINV_f_facts SWIN GASAN SHC AINVH HP); eassumption)
           fx_ok UINV UINV_agree HOLES (fun _ E1 E2 fs Hag => D_agree E1 E2 fs Hag) (fun _ => D_nil) (fun _ _ _ => eq_refl)
           RZ RZ_silent1 RZ_exit RZ_conseq (RUN_sound_fx ASEGS) asan_in_hull asan_hull_ok asan_segs_wx
           XNa_sound XEa_sound XB0_sound XAa_sound XTa_sound HSs fuel bf None p cs s Hgp Hc E fx R M model (D E (m_fs model)) HC
           ltac:(exact I) (D_nil E (m_fs model))).
Qed.
End GSoundA.
End AsDrvGSoundA.
Require LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvNodesSoundA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA AsDrvGSoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Section NodesSoundA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + BCAP <= GBUDGET.
Hypothesis ccap_ok : C0c + CCAP <= GCOUNT.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation N1 := (fun nd => GPS.node1_stmtN ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ always nd).

(* [comment removed for export] *)
Hypothesis GC : gcontracts ASEGS ITA AASAN NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ GASAN BCAP CCAP.

(* [comment removed for export] *)
Hypothesis S61 : N1 (DNA.node_read ASEGS GASAN).
Hypothesis S62 : N1 (DNA.node_close ASEGS).
Hypothesis S63 : N1 (DNA.node_ioctl ASEGS).
Hypothesis S67 : N1 (DNA.node_blobmemchr NXD).
Hypothesis S68 : N1 (DNA.node_blobstrlen ASEGS NXD).
Hypothesis S69 : N1 (DNA.node_region ASEGS NXD GASAN).
Hypothesis S71 : N1 (DNA.node_qctail ASEGS NXD DNA.QC_PRINTF false).
Hypothesis S72 : N1 (DNA.node_qctail ASEGS NXD DNA.QC_STRNLEN true).
Hypothesis S73 : N1 (DNA.node_qctail ASEGS NXD DNA.QC_MEMCHR true).
(* [comment removed for export] *)
Hypothesis FZN_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceN.
Hypothesis FZE_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceE.
#[local] Notation NCS ce args := (node_call_sound ASEGS AASAN asan_in_hull asan_hull_ok asan_segs_wx SWIN GASAN fx_ok RZ RZ_silent1 SHC KCAP AINVH HP
            asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo
            NXD PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg FTOPc FTOPc_ok BCAP CCAP bcap_ok ccap_ok UINV UINV_agree ce args).
(* [comment removed for export] *)
Lemma meter_fix_ok : forall old E cs fx R M model,
  GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E cs fx R M model ->
  GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E (meter_fix old cs) fx R M model.
Proof.
  intros old E cs fx R M model HC. unfold meter_fix.
  destruct (xlo (kn cs) old) as [ol|] eqn:Hol; [|exact HC].
  destruct (xhi (kn cs) old) as [oh|] eqn:Hoh; [|exact HC].
  destruct (xlo (kn cs) (esub (a_meter cs) old)) as [dl|] eqn:Hdl; [|exact HC].
  destruct (xhi (kn cs) (esub (a_meter cs) old)) as [dh|] eqn:Hdh; [|exact HC].
  destruct (Z.leb 0 ol && Z.leb 0 dl && Z.ltb (oh + dh) two64)%bool eqn:Hc; [|exact HC].
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  pose proof (xlo_sound ASEGS E _ (kn cs) old ol (co_know HC) Hol) as L1.
  pose proof (xhi_sound ASEGS E _ (kn cs) old oh (co_know HC) Hoh) as L2.
  pose proof (xlo_sound ASEGS E _ (kn cs) _ dl (co_know HC) Hdl) as L3.
  pose proof (xhi_sound ASEGS E _ (kn cs) _ dh (co_know HC) Hdh) as L4.
  unfold esub in L3, L4. rewrite mkAlu_denot in L3, L4. unfold Sem.alu64, Sem.alu in L3, L4.
  unfold add_kn. apply (GPS.cs_ok_set_kn ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV); [exact HC|].
  constructor; [|exact (co_know HC)].
  cbn [kentry_ok].
  pose proof (u64_range (edenot E (a_meter cs))) as Rn. pose proof (u64_range (edenot E old)) as Ro.
  rewrite bv_sub_unsigned in L3, L4. unfold bv_wrap, two64 in *.
  change (bv_modulus 64) with (2 ^ 64) in L3, L4.
  assert (CASES : bv_unsigned (edenot E (a_meter cs)) - bv_unsigned (edenot E old) >= 0 \/ bv_unsigned (edenot E (a_meter cs)) - bv_unsigned (edenot E old) < 0) by lia.
  destruct CASES as [P|N].
  - rewrite Z.mod_small in L3, L4 by lia. lia.
  - replace ((bv_unsigned (edenot E (a_meter cs)) - bv_unsigned (edenot E old)) mod 2 ^ 64)
      with (bv_unsigned (edenot E (a_meter cs)) - bv_unsigned (edenot E old) + 2 ^ 64) in L3, L4
      by (symmetry; rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
    lia.
Qed.
Lemma meter_fix_fields : forall old cs, pc (meter_fix old cs) = pc cs /\ nxt (meter_fix old cs) = nxt cs.
Proof.
  intros old cs. unfold meter_fix.
  destruct (xlo _ _); [|split; reflexivity]. destruct (xhi _ _); [|split; reflexivity].
  destruct (xlo _ _); [|split; reflexivity]. destruct (xhi _ _); [|split; reflexivity].
  destruct (_ && _)%bool; split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kn_undup_incl : forall l seen K, In K (kn_undup seen l) -> In K l.
Proof.
  induction l as [|K' r IH]; intros seen K Hin; cbn [kn_undup] in Hin; [exact Hin|].
  destruct (existsb (kentry_eqb K') seen).
  - right. exact (IH _ _ Hin).
  - destruct Hin as [<-|Hin]; [left; reflexivity|right; exact (IH _ _ Hin)].
Qed.
Lemma kn_dedup_ok : forall E cs fx R M model,
  GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E cs fx R M model ->
  GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E (kn_dedup cs) fx R M model.
Proof.
  intros E cs fx R M model HC. unfold kn_dedup.
  apply (GPS.cs_ok_set_kn ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV); [exact HC|].
  unfold know_ok. apply Forall_forall. intros K Hin. apply kn_undup_incl in Hin.
  exact (proj1 (Forall_forall _ _) (co_know HC) K Hin).
Qed.
Lemma N1_meter_fix_dd : forall f (g : acs -> expr), N1 f -> N1 (fun cs => option_map (fun c => kn_dedup (meter_fix (g cs) c)) (f cs)).
Proof.
  intros f g Hf cs cs' E fx R M model T HT HC Hp Hn Hk.
  destruct (f cs) as [c|] eqn:Hfc; [|discriminate Hn]. cbn [option_map] in Hn. injection Hn as <-.
  apply (Hf cs c E fx R M model T HT HC Hp Hfc).
  intros E' fx' R' M' model' Hag HC' Hfs.
  destruct (meter_fix_fields (g cs) c) as [Hpc Hnx].
  specialize (Hk E' fx' R' M' model' Hag (kn_dedup_ok E' _ fx' R' M' model' (meter_fix_ok (g cs) E' c fx' R' M' model' HC')) Hfs).
  change (pc (kn_dedup (meter_fix (g cs) c))) with (pc (meter_fix (g cs) c)) in Hk.
  rewrite Hpc in Hk. exact Hk.
Qed.
Lemma S120 : N1 FZN.
Proof. exact (N1_meter_fix_dd _ a_meter (fun cs => NCS AsDrvHooksA.AsFZ.ceN [ELit 0; a_meter cs; a_fbud cs] FZN_contract cs)). Qed.
Lemma S121 : N1 FZE.
Proof. exact (N1_meter_fix_dd _ a_meter (fun cs => NCS AsDrvHooksA.AsFZ.ceE [ELit 0; ELit 0; a_meter cs; a_fbud cs] FZE_contract cs)). Qed.
Hypothesis S604 : forall args, N1 (DNA.node_openat_toolong ASEGS args).
Hypothesis S606 : forall args, N1 (DNA.node_openat_absent ASEGS args).

Theorem XNa_sound : GPS.ext_stmt ASEGS NXD XNa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros id args. unfold XNa, DNA.XNP.
  repeat match goal with |- context [Nat.eqb id ?n] => destruct (Nat.eqb_spec id n); [cbn [orb]; first [assumption | apply S120 | apply S121 | apply S604 | apply S606] | cbn [orb]] end.
  exact (XNc_sound ASEGS ITA AASAN asan_in_hull asan_hull_ok ITA_ok NXD SWIN GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok FTOPc FTOPc_ok UINV UINV_agree
            RZ RZ_silent1 CT0 ltac:(intros id' ce' H; discriminate H) GC id args).
Qed.

(* [comment removed for export] *)
Hypothesis S64 : forall cs fd ps cs' E fx R M model T,
    GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E cs fx R M model ->
    DNA.node_stdio_write ASEGS NXD cs = Some (fd, ps, cs') -> T [] ->
    (forall E' fx' R' M' model',
        env_agree NXD E E' /\ env_agree (nxt cs) E E' -> GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E' cs' fx' R' M' model' ->
        m_fs model' = m_fs model -> RZ (cfgF ASEGS fx' R' (pc cs') M' model') T) ->
    RZ (cfgF ASEGS fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Theorem XEa_sound : GPS.emit_stmt ASEGS NXD XEa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros id args cs fd ps cs' E fx R M model T HC Hn. unfold XEa, DNA.XEP in Hn.
  destruct (Nat.eqb_spec id 64); [|discriminate Hn]. exact (S64 cs fd ps cs' E fx R M model T HC Hn).
Qed.

(* [comment removed for export] *)
#[local] Notation A2 := (fun nd Ta Tb => forall cs csa csb E fx R M model,
    GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E cs fx R M model -> nd cs = Some (csa, csb) -> Ta [] -> Tb [] ->
    (forall E' fx' R' M' model',
        env_agree NXD E E' /\ env_agree (nxt cs) E E' -> GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E' csa fx' R' M' model' ->
        m_fs model' = m_fs model -> RZ (cfgF ASEGS fx' R' (pc csa) M' model') Ta) ->
    (forall E' fx' R' M' model',
        env_agree NXD E E' /\ env_agree (nxt cs) E E' -> GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E' csb fx' R' M' model' ->
        m_fs model' = m_fs model -> RZ (cfgF ASEGS fx' R' (pc csb) M' model') Tb) ->
    RZ (cfgF ASEGS fx R (pc cs) M model) (t_alt2 Ta Tb)).
Hypothesis S602 : forall args Ta Tb, A2 (DNA.node_openat_file2 ASEGS NXD args) Ta Tb.
Hypothesis S603 : forall args Ta Tb, A2 (DNA.node_openat_dir2 ASEGS NXD args) Ta Tb.
Theorem XAa_sound : GPS.alt2_stmt ASEGS NXD XAa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros id args cs csa csb E fx R M model Ta Tb HC Hn. unfold XAa, DNA.XAP in Hn.
  destruct (Nat.eqb_spec id 602); [exact (S602 args Ta Tb cs csa csb E fx R M model HC Hn)|].
  destruct (Nat.eqb_spec id 603); [exact (S603 args Ta Tb cs csa csb E fx R M model HC Hn)|].
  discriminate Hn.
Qed.
End NodesSoundA.
End AsDrvNodesSoundA.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvNodesSoundA2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA AsDrvGSoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.

Section NodesSoundA2.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation N1 := (fun nd => GPS.node1_stmtN ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ always nd).
#[local] Notation AF := (AINV_f_frame SWIN GASAN SHC AINVH HP asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c).

(* [comment removed for export] *)
Lemma at_sys_sound : forall E cs fx R M model nr,
  cs_okA E cs fx R M model -> DNA.at_sys ASEGS cs nr = true ->
  is_ecall_at ASEGS cs = true /\ getr R (Z_to_bv 5 17) = Z_to_bv 64 nr /\ 0 <= nr < two64.
Proof.
  intros E cs fx R M model nr HC H. unfold DNA.at_sys in H. apply andb_prop in H as [He Hr].
  destruct (reg_lit cs 17) as [z|] eqn:H17; [|discriminate]. apply Z.eqb_eq in Hr. subst z.
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 17 nr HC ltac:(lia) H17) as [G Hz].
  split; [exact He|]. split; [exact G | exact Hz].
Qed.

Lemma reg_is_sound : forall E cs fx R M model r z,
  cs_okA E cs fx R M model -> (0 < r < 32)%nat -> DNA.reg_is cs r z = true ->
  getr R (Z_to_bv 5 (Z.of_nat r)) = Z_to_bv 64 z /\ 0 <= z < two64.
Proof.
  intros E cs fx R M model r z HC Hr H. unfold DNA.reg_is in H.
  destruct (reg_lit cs r) as [z'|] eqn:Hl; [|discriminate]. apply Z.eqb_eq in H. subst z'.
  exact (GPS.reg_lit_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model r z HC Hr Hl).
Qed.

(* [comment removed for export] *)
Lemma fds_ok_lookup12 : forall E f model fd,
  APS.fds_ok E f model -> fd = 1 \/ fd = 2 -> exists e, fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel e).
Proof.
  intros E f model fd H [-> | ->]; destruct f as [|k len off|]; cbn [APS.fds_ok] in H;
    first [rewrite H | destruct H as (p & c & Hm & _); rewrite Hm]; eexists; reflexivity.
Qed.

Lemma set_pc_set_reg_eq : forall cs n e p,
  set_pc (set_reg cs n e) p = with_ss cs (mk_ss p (sr_upd (s_regs (a_ss cs)) n e) (s_know (a_ss cs)) (s_next (a_ss cs))).
Proof. intros cs n e p. destruct cs; reflexivity. Qed.

Lemma errno_ENOTTY : errno_ret ENOTTY = Z_to_bv 64 (two64 - 25).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Theorem node_ioctl_sound : N1 (DNA.node_ioctl ASEGS).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_ioctl in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hg as [Hg H11]. apply andb_prop in Hg as [H29 H10].
  destruct (at_sys_sound E cs fx R M model 29 HC H29) as (Hec & G17 & _).
  destruct (reg_is_sound E cs fx R M model 10 1 HC ltac:(lia) H10) as [G10 _].
  destruct (reg_is_sound E cs fx R M model 11 0x5413 HC ltac:(lia) H11) as [G11 _].
  destruct (GPS.is_ecall_at_sound ASEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  destruct (fds_ok_lookup12 E (a_fd cs) model 1 (co_fds HC) (or_introl eq_refl)) as [e1 Hlk1].
  assert (E17 : Z_to_bv 5 17 = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11.
  (* [comment removed for export] *)
  unfold cfgF.
  eapply (GPS.rz_step_ecall ASEGS RZ RZ_silent1); [exact (co_halt HC) | eapply GPS.step_ecallF; eassumption | reflexivity | cbn; discriminate |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
  (* [comment removed for export] *)
  eapply RZ_silent1.
  { apply (node_det_noacc ASEGS _ model (getr R 17) (mkEffect (errno_ret ENOTTY) [] []) model []).
    - exact (co_halt HC).
    - reflexivity.
    - intros eff m' evs.
      rewrite (check_syscall_ioctl _ eff model) by (rewrite in_sysno_si, G17; apply u64_lit; unfold two64; lia).
      rewrite in_arg0_si, in_arg1_si, ms_gpr_epend0, ms_gpr_epend1, G10, G11.
      rewrite fd32_small by (rewrite u64_lit; lia).
      unfold check_ioctl. rewrite Hlk1. replace (tty_only_request (cmd32 (Z_to_bv 64 21523))) with true by (vm_compute; reflexivity).
      rewrite check_ret_only_ok_iff. tauto.
    - intros eff.
      rewrite (check_syscall_ioctl _ eff model) by (rewrite in_sysno_si, G17; apply u64_lit; unfold two64; lia).
      rewrite in_arg0_si, in_arg1_si, ms_gpr_epend0, ms_gpr_epend1, G10, G11.
      rewrite fd32_small by (rewrite u64_lit; lia).
      unfold check_ioctl. rewrite Hlk1. replace (tty_only_request (cmd32 (Z_to_bv 64 21523))) with true by (vm_compute; reflexivity).
      apply check_ret_only_no_unmodeled.
    - exact (co_halt HC).
    - reflexivity. }
  (* [comment removed for export] *)
  cbn beta. rewrite apply_effect_no_write, adv_set_epend, (v_addi_pc (pc cs) Hpc0 Hpc4).
  specialize (Hk E fx (regupd R 10 (errno_ret ENOTTY)) M model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
  rewrite set_pc_set_reg_eq in Hk. unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc.
  apply Hk; [|reflexivity].
  eapply (GPS.cs_ok_frame ASEGS SWIN PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc AF fx_ok UINV);
    [exact HC | | reflexivity | exact (co_know HC) | exact (co_fx HC) | intros a Ha; exfalso; exact (Ha eq_refl)].
  cbn [mk_ss s_regs].
  rewrite errno_ENOTTY, <- E10.
  apply (APS.regs_ok_set_n E (s_regs (a_ss cs)) R 10 (ELit (two64 - 25)) (Z_to_bv 64 (two64 - 25)) (co_regs HC) ltac:(lia)).
  cbn [edenot]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma materialize_not_lazy : forall m accs,
  (forall p, In p (accesses_pages accs []) -> page_in_ranges p (m_vm_lazy m) = false) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs Hn. unfold materialize_model_accesses, materialize_accesses.
  assert (E0 : newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs = []).
  { unfold newly_materialized_pages.
    assert (G : forall l, (forall p, In p l -> page_in_ranges p (m_vm_lazy m) = false) ->
               List.filter (fun p => page_in_ranges p (m_vm_lazy m) && negb (page_mem p (m_vm_materialized m)))%bool l = []).
    { induction l as [|q l IH]; intros Hl; [reflexivity|]. cbn [List.filter]. rewrite (Hl q (or_introl eq_refl)). cbn [andb].
      apply IH. intros p' Hp'. apply Hl. right. exact Hp'. }
    apply G. exact Hn. }
  rewrite E0. rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pages_above_ceil_not_lazy : forall Lc Lf B C K M mdl accs,
  AINVc Lc Lf B C K M mdl ->
  (forall a n, In (a, n) accs -> CEIL_run + 4096 <= u a /\ u a + Z.of_nat n < two64) ->
  forall p, In p (accesses_pages accs []) -> page_in_ranges p (m_vm_lazy mdl) = false.
Proof.
  intros Lc Lf B C K M mdl accs HA Hb p Hin.
  destruct (accesses_pages_in accs [] p Hin) as [[] | (a & n & k & Hin' & Hk & ->)].
  destruct (Hb a n Hin') as [Ha Hn].
  destruct (page_in_ranges (page_base_of (u a + Z.of_nat k)) (m_vm_lazy mdl)) eqn:Hp; [|reflexivity]. exfalso.
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hiv Hc]].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AINV_f_facts SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c _ _ _ _ _ _ _ HA) iv Hiv) as (L0 & L1 & L2).
  unfold page_base_of in H1, H2. unfold page_size in *.
  set (z := u a + Z.of_nat k) in *.
  pose proof (Z.mul_div_le z 4096 ltac:(lia)) as D1.
  pose proof (Z.mul_succ_div_gt z 4096 ltac:(lia)) as D2.
  pose proof (u64_range a) as Ra. unfold two64 in Hn.
  assert (Hq : 0 <= z / 4096 * 4096 < 2 ^ 64) by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia] | nia]).
  rewrite u64_lit in H1, H2 by exact Hq.
  nia.
Qed.

Lemma node_chk_ev_nl : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  CfgStep.alloc_no_b (bv_unsigned x8) = false ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input ASEGS ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input ASEGS ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input ASEGS ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i p, In p (accesses_pages (syscall_effect_accesses (effs i)) []) -> page_in_ranges p (m_vm_lazy (ms' i)) = false) ->
  AsVocab.AsanAcct.node_ok ASEGS (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hna Hh Hsvc Hok Hinv Hnu Hh' Hacc.
  apply (CfgStep.node_transfer_on ASEGS CfgStep.kit_cfg); [exact (CfgStep.kit_pending_on_sysno ASEGS ms model x8 _ Hsvc eq_refl Hna) |].
  split.
  - intros i. apply (sstep_syscall ASEGS ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. exact (Hok i).
    + exact (Hh' i).
    + apply materialize_not_lazy. exact (Hacc i).
  - intros e st Hss.
    destruct (sstep_svc_inv ASEGS ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_not_lazy _ _ (Hacc i)) in Hmat. injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_not_lazy _ _ (Hacc i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma Mr_ret_with : forall E cs r k nx f model model' M,
  m_vm model' = m_vm model ->
  GPS.Mr SHC VSHc E (DNA.ret_with cs r k nx f) model' M = GPS.Mr SHC VSHc E cs model M.
Proof.
  intros E cs r k nx f model model' M Hvm. unfold GPS.Mr, GPS.hid, GPS.lz, GPS.vlz, m_vm_lazy. rewrite Hvm. reflexivity.
Qed.

Lemma cs_ok_sys_ret : forall E cs fx R M model r v f model',
  cs_okA E cs fx R M model ->
  edenot E r = v ->
  m_vm model' = m_vm model -> m_halted model' = m_halted model -> m_fs model' = m_fs model ->
  APS.fds_ok E f model' ->
  cs_okA E (DNA.ret_with cs r (kn cs) (nxt cs) f) fx (regupd R 10 v) M model'.
Proof.
  intros E cs fx R M model r v f model' HC Hr Hvm Hh Hfs Hfd.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL].
  constructor; cbn [DNA.ret_with a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_meter a_fake a_fbud mk_ss nxt pc];
    try assumption.
  - replace (10%bv : Prelude.reg) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
    apply APS.regs_ok_set_n; [exact CR | lia | exact Hr].
  - reflexivity.
  - rewrite (Mr_ret_with E cs r (kn cs) (nxt cs) f model model' M Hvm). exact CK.
  - rewrite Hh. exact CH.
  - rewrite Hfs. exact CF.
  - eapply (AINV_f_vm SWIN GASAN SHC AINVH HP); [exact CA | exact Hvm].
Qed.

(* [comment removed for export] *)
Lemma fds_ok_fd3 : forall E f model,
  APS.fds_ok E f model -> DNA.is_std f = false -> exists e, m_fds model = APS.fds3 e.
Proof.
  intros E f model H Hs. destruct f as [|k len off|]; cbn [APS.fds_ok DNA.is_std] in H, Hs; try discriminate.
  - destruct H as (p & c & Hm & _). rewrite Hm. eexists. reflexivity.
  - rewrite H. eexists. reflexivity.
Qed.

Theorem node_close_sound : N1 (DNA.node_close ASEGS).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_close in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hg as [Hg Hstd]. apply andb_prop in Hg as [H57 H10]. apply negb_true_iff in Hstd.
  destruct (at_sys_sound E cs fx R M model 57 HC H57) as (Hec & G17 & _).
  destruct (reg_is_sound E cs fx R M model 10 3 HC ltac:(lia) H10) as [G10 _].
  destruct (GPS.is_ecall_at_sound ASEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  destruct (fds_ok_fd3 E (a_fd cs) model (co_fds HC) Hstd) as [e3 Hfds].
  assert (Hlk3 : fd_lookup (m_fds model) (Z_to_bv 64 3) = Some e3) by (rewrite Hfds; reflexivity).
  assert (E17 : Z_to_bv 5 17 = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10.
  unfold cfgF.
  eapply (GPS.rz_step_ecall ASEGS RZ RZ_silent1); [exact (co_halt HC) | eapply GPS.step_ecallF; eassumption | reflexivity | cbn; discriminate |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
  set (model' := with_fds (fd_remove (m_fds model) (Z_to_bv 64 3)) model).
  eapply RZ_silent1.
  { apply (node_det_noacc ASEGS _ model (getr R 17) (mkEffect (Z_to_bv 64 0) [] []) model' []).
    - exact (co_halt HC).
    - reflexivity.
    - intros eff m' evs.
      rewrite (check_syscall_close _ eff model) by (rewrite in_sysno_si, G17; apply u64_lit; unfold two64; lia).
      rewrite in_arg0_si, ms_gpr_epend0, G10. rewrite fd32_small by (rewrite u64_lit; lia).
      unfold check_close. rewrite Hlk3. rewrite check_ret_only_ok_iff. subst model'. tauto.
    - intros eff.
      rewrite (check_syscall_close _ eff model) by (rewrite in_sysno_si, G17; apply u64_lit; unfold two64; lia).
      rewrite in_arg0_si, ms_gpr_epend0, G10. rewrite fd32_small by (rewrite u64_lit; lia).
      unfold check_close. rewrite Hlk3. apply check_ret_only_no_unmodeled.
    - subst model'. rewrite with_fds_halted. exact (co_halt HC).
    - reflexivity. }
  cbn beta. rewrite apply_effect_no_write, adv_set_epend, (v_addi_pc (pc cs) Hpc0 Hpc4).
  refine (Hk E fx (regupd R 10 (Z_to_bv 64 0)) M model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) _ _).
  2:{ subst model'. apply with_fds_fs. }
  apply (cs_ok_sys_ret E cs fx R M model (ELit 0) (Z_to_bv 64 0) FdStd model' HC).
  - cbn [edenot]. reflexivity.
  - reflexivity.
  - apply with_fds_halted.
  - apply with_fds_fs.
  - cbn [APS.fds_ok]. subst model'. rewrite with_fds_fds, Hfds. reflexivity.
Qed.
End NodesSoundA2.
End AsDrvNodesSoundA2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import Open.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA AsDrvGSoundA AsDrvNodesSoundA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.

Section NodesSoundA3.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation N1 := (fun nd => GPS.node1_stmtN ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ always nd).
#[local] Notation Mr := (GPS.Mr SHC VSHc).

(* [comment removed for export] *)
Hypothesis NONUL2 : forall E, UINV E -> ~ In (Z_to_bv 8 0) (eb E 2%nat).

(* [comment removed for export] *)
Lemma hid_above_false : forall E cs B C K M mdl (a : word),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  CEIL_run + 4096 <= u a -> GPS.hid SHC VSHc E cs mdl a = false.
Proof.
  intros E cs B C K M mdl a HA Ha. unfold GPS.hid, GPS.lz.
  destruct (page_in_ranges (page_base a) (m_vm_lazy mdl)) eqn:Hp; [|reflexivity]. exfalso.
  assert (HF : Forall (fun iv => 0 <= u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run) (m_vm_lazy mdl)).
  { eapply Forall_impl; [|exact (AINV_f_facts SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c _ _ _ _ _ _ _ HA)].
    intros iv (X1 & X2 & X3). lia. }
  pose proof (GPS.page_in_ranges_bounds' a _ _ _ HF Hp) as [_ Hb]. lia.
Qed.
Lemma Mr_above : forall E cs B C K M mdl (a : word),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  CEIL_run + 4096 <= u a -> Mr E cs mdl M a = M a.
Proof.
  intros E cs B C K M mdl a HA Ha. unfold GPS.Mr, mrestrict. rewrite (hid_above_false E cs B C K M mdl a HA Ha). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_mem : forall (mem : word -> option byte) bs (a : Z),
  (forall i, (i < length bs)%nat -> mrb ASEGS mem (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0))) ->
  rdn ASEGS mem (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros mem bs. induction bs as [|b bs IH]; intros a Hm; [reflexivity|].
  cbn [rdn length]. pose proof (Hm 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. unfold mrb in H0. rewrite H0. cbn [nth].
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ apply bv_eq. rewrite bv_add_unsigned. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_unsigned (1%bv : word)) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity. }
  rewrite (IH (a + 1)); [reflexivity|].
  intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact (Hm (S i) ltac:(cbn; lia)).
Qed.

Lemma has_fact_sound : forall E M k K, know_ok ASEGS E M k -> DNA.has_fact k K = true -> kentry_ok ASEGS E M K.
Proof.
  intros E M k K HK H. unfold DNA.has_fact in H. apply existsb_exists in H as [K' [Hin Heq]].
  apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.
Lemma mrb_of_mem : forall (mem : word -> option byte) a b, mem a = Some b -> mrb ASEGS mem a = Some b.
Proof. intros mem a b H. unfold mrb. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cstring_at (E : env) (M : word -> option byte) (pa : Z) (bs : list byte) : Prop :=
  (forall i, (i < length bs)%nat -> mrb ASEGS M (Z_to_bv 64 (pa + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)))
  /\ mrb ASEGS M (Z_to_bv 64 (pa + Z.of_nat (length bs))) = Some (Z_to_bv 8 0)
  /\ (bs = [] \/ bs = eb E 2%nat).

#[local] Notation at_sys_soundI := (at_sys_sound SHC KCAP AINVH SWIN PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).
#[local] Notation reg_is_soundI := (reg_is_sound SHC KCAP AINVH SWIN PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).
#[local] Notation cs_ok_sys_retI := (cs_ok_sys_ret SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).
#[local] Notation pages_above_ceil_not_lazyI := (pages_above_ceil_not_lazy SHC AINVH SWIN HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).

Lemma openat_ok_sound : forall E cs fx R M model args L,
  cs_okA E cs fx R M model -> DNA.openat_ok ASEGS args cs = Some L ->
  exists path rest bs, args = path :: rest
  /\ is_ecall_at ASEGS cs = true /\ getr R (Z_to_bv 5 17) = Z_to_bv 64 56
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 DNA.AT_FDCWD64
  /\ getr R (Z_to_bv 5 (Z.of_nat 11)) = edenot E path
  /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 DNA.O_FLAGS
  /\ a_fd cs = FdStd
  /\ Z.of_nat (length bs) = u (edenot E L)
  /\ CEIL_run + 4096 <= u (edenot E path)
  /\ u (edenot E path) + u (edenot E L) + 4104 < two64
  /\ cstring_at E M (u (edenot E path)) bs.
Proof.
  intros E cs fx R M model args L HC H. unfold DNA.openat_ok in H.
  destruct args as [|path rest]; [discriminate H|].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate H] end.
  apply andb_prop in Hg as [Hg Hge]. apply andb_prop in Hg as [Hg Hbrk]. apply andb_prop in Hg as [Hg Hylo]. apply andb_prop in Hg as [Hg Hfl].
  apply andb_prop in Hg as [Hg Hstd]. apply andb_prop in Hg as [Hg H12]. apply andb_prop in Hg as [Hg H11]. apply andb_prop in Hg as [H56 H10].
  destruct (at_sys_soundI E cs fx R M model 56 HC H56) as (Hec & G17 & _).
  destruct (reg_is_soundI E cs fx R M model 10 DNA.AT_FDCWD64 HC ltac:(lia) H10) as [G10 _].
  destruct (reg_is_soundI E cs fx R M model 12 DNA.O_FLAGS HC ltac:(lia) H12) as [G12 _].
  apply expr_eqb_eq in H11.
  assert (G11 : getr R (Z_to_bv 5 (Z.of_nat 11)) = edenot E path).
  { rewrite (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)). rewrite H11. reflexivity. }
  assert (Hfd : a_fd cs = FdStd) by (destruct (a_fd cs); [reflexivity | discriminate Hstd | discriminate Hstd]).
  (* [comment removed for export] *)
  destruct (acs_floor (a_maps cs)) eqn:Hfloor; [discriminate Hfl|].
  apply Z.leb_le in Hylo.
  destruct (xlo (kn cs) (a_brk cs)) as [bl|] eqn:Hbl; [|discriminate Hbrk]. apply Z.ltb_lt in Hbrk.
  pose proof (xlo_sound ASEGS E _ (kn cs) (a_brk cs) bl (co_know HC) Hbl) as Lbrk.
  pose proof (lin_ge0_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hge) as Lge. cbn [xt_den] in Lge.
  pose proof (co_floor HC) as FL. rewrite Hfloor in FL. cbn [GPS.floor_sem] in FL. unfold GPS.sptop_den, GPS.uE in FL.
  destruct (Z.eqb_spec (u (edenot E (a_brk cs))) 0) as [Z0|NZ]; [lia|].
  pose proof sfloor_ge as SFG.
  assert (Hceil : CEIL_run + 4096 <= u (edenot E path)) by lia.
  (* [comment removed for export] *)
  destruct (DNA.blob_at (kn cs) path) as [[L' j]|] eqn:Hba; [|discriminate H].
  destruct ((Nat.eqb j 2 || Nat.eqb j 0)%bool) eqn:Hj; [|discriminate H]. cbn [andb] in H.
  destruct (xhi (kn cs) path) as [hp|] eqn:Hhp; [|discriminate H].
  destruct (xhi (kn cs) L') as [hl|] eqn:Hhl; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hnw; [|discriminate H] end. apply Z.ltb_lt in Hnw.
  change DNA.two64 with two64 in Hnw.
  injection H as <-.
  pose proof (xhi_sound ASEGS E _ (kn cs) path hp (co_know HC) Hhp) as Bp.
  pose proof (xhi_sound ASEGS E _ (kn cs) L' hl (co_know HC) Hhl) as Bl.
  pose proof (u64_range (edenot E path)) as Rp. pose proof (u64_range (edenot E L')) as Rl.
  unfold DNA.blob_at in Hba. destruct (split_lit path) as [sb sk] eqn:Hsl.
  pose proof (APS.split_lit_denot E path sb sk Hsl) as SD.
  assert (AINVcs := co_ainv HC).
  match type of Hba with (match ?f with _ => _ end) = _ => destruct f as [K|] eqn:Hfind end.
  - (* [comment removed for export] *)
    apply List.find_some in Hfind as [Hin HK].
    destruct K as [ | |[b o] L2 j2| | | | | | | | | ]; try discriminate HK.
    apply andb_prop in HK as [HKb HKo]. apply expr_eqb_eq in HKb. apply Z.eqb_eq in HKo. subst b o.
    match type of Hba with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hba] end.
    injection Hba as E1 E2. subst L2 j2.
    apply andb_prop in Hc as [Hab Hnul].
    assert (Hj2 : j = 2%nat).
    { unfold DNA.argv_blob in Hab. apply orb_prop in Hj. apply orb_prop in Hab.
      destruct Hab as [H1|H2]; [apply Nat.eqb_eq in H1 | apply Nat.eqb_eq in H2; exact H2].
      destruct Hj as [H3|H4]; [apply Nat.eqb_eq in H3 | apply Nat.eqb_eq in H4]; lia. }
    subst j.
    pose proof (proj1 (Forall_forall _ _) (co_know HC) _ Hin) as KB. cbn [kentry_ok] in KB. destruct KB as (Hflat & Hlen & Hbytes).
    unfold flat, elenZ, estart in Hflat, Hlen, Hbytes. cbn [a_base a_off] in Hflat, Hlen, Hbytes. destruct Hflat as (F1 & F2 & F3 & F4).
    assert (Hpa : u (edenot E path) = u (edenot E sb) + sk) by (rewrite SD; rewrite u64_lit by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (split_lit (eadd path L')) as [b' o'] eqn:Hsl'.
    pose proof (has_fact_sound E _ (kn cs) _ (co_know HC) Hnul) as KW. cbn [kentry_ok] in KW. destruct KW as (_ & Hflat1 & Hrd1).
    pose proof (flat_u E (SA b' o') 1 Hflat1) as U1. unfold flat, estart in U1, Hflat1. cbn [a_base a_off] in U1, Hflat1.
    pose proof (APS.split_lit_denot E (eadd path L') b' o' Hsl') as SD'.
    assert (EADD : u (edenot E (eadd path L')) = u (edenot E path) + u (edenot E L')).
    { unfold eadd. rewrite mkAlu_denot. unfold Sem.alu64, Sem.alu. rewrite bv_add_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). unfold two64 in Hnw. rewrite Z.mod_small by lia. reflexivity. }
    assert (Hnuladdr : u (adenot E (SA b' o')) = u (edenot E path) + u (edenot E L')).
    { rewrite U1, <- EADD, SD'. destruct Hflat1 as (G1 & G2 & _). rewrite u64_lit by lia. reflexivity. }
    exists path, rest, (eb E 2%nat).
    split; [reflexivity|]. split; [exact Hec|]. split; [exact G17|]. split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
    split; [exact Hfd|]. split; [exact Hlen|]. split; [exact Hceil|]. split; [lia|].
    split; [|split].
    + intros i Hi. apply mrb_of_mem.
      assert (Ha : u (Z_to_bv 64 (u (edenot E path) + Z.of_nat i)) = u (edenot E path) + Z.of_nat i).
      { rewrite u64_lit; [reflexivity|]. unfold two64 in Hnw. apply Nat2Z.inj_lt in Hi. lia. }
      rewrite <- (Mr_above E cs _ _ _ M model _ AINVcs) by (rewrite Ha; lia).
      rewrite Hpa. specialize (Hbytes (Z.of_nat i) ltac:(apply Nat2Z.inj_lt in Hi; lia)). rewrite Nat2Z.id in Hbytes. exact Hbytes.
    + replace (Z_to_bv 64 (u (edenot E path) + Z.of_nat (length (eb E 2%nat)))) with (adenot E (SA b' o')) by (apply bv_eq; rewrite Hnuladdr, u64_lit; [lia | unfold two64 in Hnw; lia]).
      cbn [rdn] in Hrd1.
      rewrite (Mr_above E cs _ _ _ M model _ AINVcs) in Hrd1 by (rewrite Hnuladdr; lia).
      unfold mrb. cbn [edenot word_to_le_bytes] in Hrd1.
      destruct (M (adenot E (SA b' o'))) as [b0|]; [|destruct (seg_rom ASEGS (adenot E (SA b' o'))) as [b0|]; [|discriminate Hrd1]];
        injection Hrd1 as Hb0; rewrite Hb0; reflexivity.
    + right. reflexivity.
  - (* [comment removed for export] *)
    match type of Hba with (if ?c then _ else _) = _ => destruct c eqn:Hnul; [|discriminate Hba] end.
    injection Hba as E1 E2. subst L' j.
    pose proof (has_fact_sound E _ (kn cs) _ (co_know HC) Hnul) as KW. cbn [kentry_ok] in KW. destruct KW as (_ & Hflat1 & Hrd1).
    pose proof (flat_u E (SA sb sk) 1 Hflat1) as U1. unfold flat, estart in U1, Hflat1. cbn [a_base a_off] in U1, Hflat1.
    destruct Hflat1 as (G1 & G2 & _).
    assert (Hpa : u (edenot E path) = u (edenot E sb) + sk) by (rewrite SD; rewrite u64_lit by lia; reflexivity).
    exists path, rest, (@nil byte).
    split; [reflexivity|]. split; [exact Hec|]. split; [exact G17|]. split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
    split; [exact Hfd|]. split; [cbn [edenot length]; rewrite u64_lit; [reflexivity | unfold two64; lia]|]. split; [exact Hceil|]. split; [lia|].
    split; [|split].
    + intros i Hi. cbn in Hi. lia.
    + cbn [length]. rewrite Z.add_0_r.
      replace (Z_to_bv 64 (u (edenot E path))) with (adenot E (SA sb sk)) by (apply bv_eq; rewrite U1, u64_lit; lia).
      cbn [rdn] in Hrd1.
      rewrite (Mr_above E cs _ _ _ M model _ AINVcs) in Hrd1 by (rewrite U1; lia).
      unfold mrb. cbn [edenot word_to_le_bytes] in Hrd1.
      destruct (M (adenot E (SA sb sk))) as [b0|]; [|destruct (seg_rom ASEGS (adenot E (SA sb sk))) as [b0|]; [|discriminate Hrd1]];
        injection Hrd1 as Hb0; rewrite Hb0; reflexivity.
    + left. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma cstr_access_len_le : forall mp fuel a, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp fuel. induction fuel as [|f IH]; intros a; cbn; [lia|].
  destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)%bv). lia.
Qed.
Lemma sea_copyins_ret : forall Rd r, syscall_effect_accesses (with_copyins Rd (mkEffect r [] [])) = Rd.
Proof. intros Rd r. unfold with_copyins, syscall_effect_accesses. cbn. now rewrite app_nil_r. Qed.
Lemma errno_lit : forall e, 0 < e < 4096 -> errno_ret e = Z_to_bv 64 (two64 - e).
Proof.
  intros e He. unfold errno_ret. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, two64.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- (Z.mod_add (- e) 1 (2 ^ 64)) by lia. f_equal. lia.
Qed.
Lemma O_FLAGS_modeled : modeled_open_flags (Z_to_bv 64 DNA.O_FLAGS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma O_FLAGS_rd : Z.ldiff (u (Z_to_bv 64 DNA.O_FLAGS)) open_ignored_flags = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ATFDCWD_eq : Z_to_bv 64 DNA.AT_FDCWD64 = AT_FDCWD.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ms_read_byte_ependA : forall fx regs pc mem x8, ms_read_byte (@epend fx regs pc mem (seg_rom ASEGS) x8) = mrb ASEGS mem.
Proof. reflexivity. Qed.
Lemma adv_eff_ret_copyins_ependA : forall fx regs pc mem rom x8 r reads,
  advance_past_svc (apply_effect (@epend fx regs pc mem rom x8) (with_copyins reads (mkEffect r [] []))) = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. rewrite apply_effect_copyins_no_write. apply adv_set_epend. Qed.

(* [comment removed for export] *)
Lemma openat_enoent_check : forall segs ms x8 model p,
  u x8 = 56 -> ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  Z.ldiff (u (ms_gpr ms 2)) open_ignored_flags = 0 ->
  (path_eqb p [] = false -> openat_plain_name p = true /\ fs_lookup (m_fs model) p = None) ->
  forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [].
Proof.
  intros segs ms x8 model p Hno Hdirfd Hpath Hfl Hcls eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
  - apply check_copyins_after_ret_only.
  - destruct (Hcls eq_refl) as [Hplain Hfs].
    pose proof (openat_plain_name_noslash _ Hplain) as Hunw. pose proof (openat_plain_name_nodirref _ Hplain) as Hdot.
    rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved. rewrite Hunw. cbv beta iota.
    rewrite Hfl, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read. rewrite Hdot, Hfs.
    apply check_copyins_after_ret_only.
Qed.

(* [comment removed for export] *)
Lemma rz_openat_err : forall args L cs E fx R M model (e : Z) T,
  cs_okA E cs fx R M model -> DNA.openat_ok ASEGS args cs = Some L -> 0 < e < 4096 ->
  (forall path rest bs, args = path :: rest -> cstring_at E M (u (edenot E path)) bs -> Z.of_nat (length bs) = u (edenot E L) ->
     read_cstr (mrb ASEGS M) (edenot E path) = CstrTooLong /\ e = ENAMETOOLONG
     \/ (exists p, read_cstr (mrb ASEGS M) (edenot E path) = CstrOk p /\ (path_eqb p [] = false -> openat_plain_name p = true /\ fs_lookup (m_fs model) p = None) /\ e = ENOENT)) ->
  (forall E' fx' R' M' model',
      env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' (DNA.ret_simple cs (ELit (DNA.two64 - e))) fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF ASEGS fx' R' (pc (DNA.ret_simple cs (ELit (DNA.two64 - e)))) M' model') T) ->
  RZ (cfgF ASEGS fx R (pc cs) M model) T.
Proof.
  intros args L cs E fx R M model e T HC Hok He Hspec Hk.
  destruct (openat_ok_sound E cs fx R M model args L HC Hok) as (path & rest & bs & Hargs & Hec & G17 & G10 & G11 & G12 & Hfd & Hlen & Hceil & Hnw & Hstr).
  destruct (GPS.is_ecall_at_sound ASEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  assert (E17 : Z_to_bv 5 17 = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  pose proof (u64_range (edenot E path)) as Rp. pose proof (u64_range (edenot E L)) as Rl.
  unfold cfgF.
  eapply (GPS.rz_step_ecall ASEGS RZ RZ_silent1); [exact (co_halt HC) | eapply GPS.step_ecallF; eassumption | reflexivity | cbn; discriminate |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
  set (ms := @epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
  set (eff := with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] [])).
  assert (Hx8 : u (getr R 17) = 56) by (rewrite G17; apply u64_lit; unfold two64; lia).
  assert (Hchk : forall ef, check_syscall (sys_input ASEGS ms (getr R 17)) ef model = check_ret_only_copyins (open_copyins ms) ef (errno_ret e) model []).
  { assert (Hrb : ms_read_byte ms = mrb ASEGS M) by (subst ms; apply ms_read_byte_ependA).
    assert (Ha1 : ms_gpr ms 1 = edenot E path) by (subst ms; rewrite ms_gpr_epend1; exact G11).
    assert (Ha0 : ms_gpr ms 0 = AT_FDCWD) by (subst ms; rewrite ms_gpr_epend0, G10; exact ATFDCWD_eq).
    assert (Ha2 : ms_gpr ms 2 = Z_to_bv 64 DNA.O_FLAGS) by (subst ms; rewrite ms_gpr_epend2; exact G12).
    clearbody ms.
    intros ef. destruct (Hspec path rest bs Hargs Hstr Hlen) as [[Hcs ->] | (p & Hcs & Hcls & ->)].
    - apply (openat_toolong_check ASEGS ms (getr R 17) model Hx8); [rewrite Ha2; exact O_FLAGS_modeled | rewrite Hrb, Ha1; exact Hcs].
    - apply (openat_enoent_check ASEGS ms (getr R 17) model p Hx8 Ha0); [rewrite Hrb, Ha1; exact Hcs | rewrite Ha2; exact O_FLAGS_rd | exact Hcls]. }
  eapply RZ_silent1.
  { apply (node_chk_ev_nl ms model (getr R 17) unit (fun _ => eff) (fun _ => model) (fun _ => [])).
    - rewrite G17. reflexivity.
    - exact (co_halt HC).
    - reflexivity.
    - intros []. rewrite Hchk. apply (proj2 (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _)). subst eff. auto.
    - intros ef m' ev Hs. rewrite Hchk in Hs. apply (proj1 (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _)) in Hs as (-> & -> & ->). exists tt. auto.
    - intros ef Hs. rewrite Hchk in Hs. exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
    - intros []. exact (co_halt HC).
    - intros [] p Hp. subst eff. rewrite sea_copyins_ret in Hp.
      eapply (pages_above_ceil_not_lazyI _ _ _ _ _ M model _ (co_ainv HC)); [|exact Hp].
      intros a n Hin. unfold open_copyins in Hin. destruct Hin as [Hin|[]].
      pose proof (f_equal fst Hin) as Ea. cbn [fst] in Ea. pose proof (proj2 (proj1 (pair_equal_spec _ _ _ _) Hin)) as En.   (* [comment removed for export] *)
      assert (Hn : (n <= 4096)%nat) by (rewrite <- En; apply (cstr_access_len_le _ 4096%nat)).
      subst a ms. rewrite ms_gpr_epend1, G11. split; [exact Hceil |]. clear - Hn Hnw Rp Rl. unfold two64 in *. lia. }
  cbn beta. subst eff ms. rewrite adv_eff_ret_copyins_ependA, (v_addi_pc (pc cs) Hpc0 Hpc4).
  refine (Hk E fx (regupd R 10 (errno_ret e)) M model (conj (env_agree_refl _ _) (env_agree_refl _ _)) _ eq_refl).
  unfold DNA.ret_simple. apply (cs_ok_sys_retI E cs fx R M model (ELit (DNA.two64 - e)) (errno_ret e) (a_fd cs) model HC).
  - cbn [edenot]. rewrite (errno_lit e He). change DNA.two64 with two64. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact (co_fds HC).
Qed.
(* [comment removed for export] *)
Lemma cstring_rdn : forall E M pa bs,
  cstring_at E M pa bs -> 0 <= pa -> pa + Z.of_nat (length bs) + 1 < two64 ->
  rdn ASEGS M (Z_to_bv 64 pa) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]).
Proof.
  intros E M pa bs (Sb & Sn & _) H0 Hnw.
  replace (length bs + 1)%nat with (length (bs ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia).
  apply rdn_of_mem. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hl|Hg].
  - rewrite app_nth1 by exact Hl. exact (Sb i Hl).
  - assert (Hi' : i = length bs) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. exact Sn.
Qed.

Theorem node_openat_toolong_sound : forall args, N1 (DNA.node_openat_toolong ASEGS args).
Proof.
  intros args cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_openat_toolong in Hn.
  destruct (DNA.openat_ok ASEGS args cs) as [L|] eqn:Hok; [|discriminate Hn].
  destruct (xlo (kn cs) L) as [lo|] eqn:Hlo; [|discriminate Hn].
  destruct (Z.leb 4096 lo) eqn:H4k; [|discriminate Hn]. apply Z.leb_le in H4k. injection Hn as <-.
  pose proof (xlo_sound ASEGS E _ (kn cs) L lo (co_know HC) Hlo) as BL.
  change (DNA.two64 - 36) with (DNA.two64 - ENAMETOOLONG).
  apply (rz_openat_err args L cs E fx R M model ENAMETOOLONG T HC Hok ltac:(unfold ENAMETOOLONG; lia)); [|exact Hk].
  intros path rest bs Hargs Hstr Hlen. left. split; [|reflexivity].
  destruct Hstr as (Sb & Sn & Sbs).
  assert (Hbs : bs = eb E 2%nat) by (destruct Sbs as [-> | ->]; [cbn in Hlen; lia | reflexivity]).
  assert (Hl4 : (4096 <= length bs)%nat) by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E path)).
  apply (read_cstr_toolong_of_rdn ASEGS M _ (firstn 4096 bs)).
  - rewrite length_firstn. lia.
  - intros Hin. apply (NONUL2 E (co_uinv HC)). rewrite <- Hbs, <- (firstn_skipn 4096 bs). apply in_app_iff. left. exact Hin.
  - replace 4096%nat with (length (firstn 4096 bs)) at 1 by (rewrite length_firstn; lia).
    apply rdn_of_mem. intros i Hi. rewrite length_firstn in Hi.
    rewrite nth_firstn. replace (i <? 4096)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    apply Sb. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cls_is_sound : forall E M k c, know_ok ASEGS E M k -> DNA.cls_is k c = true -> u (ev E 4%nat) = c.
Proof.
  intros E M k c HK H. unfold DNA.cls_is in H.
  destruct (xlo k (EVar 4)) as [lo|] eqn:Hlo; [|discriminate H]. destruct (xhi k (EVar 4)) as [hi|] eqn:Hhi; [|discriminate H].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  pose proof (xlo_sound ASEGS E M k _ _ HK Hlo) as X1. pose proof (xhi_sound ASEGS E M k _ _ HK Hhi) as X2. cbn [edenot] in X1, X2. lia.
Qed.
Hypothesis ABSENT2 : forall E, UINV E -> u (ev E 4%nat) = DNA.CLS_ABSENT ->
  eb E 2%nat <> [] -> openat_plain_name (eb E 2%nat) = true /\ fs_lookup FS0 (eb E 2%nat) = None.

Theorem node_openat_absent_sound : forall args, N1 (DNA.node_openat_absent ASEGS args).
Proof.
  intros args cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_openat_absent in Hn.
  destruct (DNA.openat_ok ASEGS args cs) as [L|] eqn:Hok; [|discriminate Hn].
  unfold DNA.path_len_ok0 in Hn.
  destruct (xlo (kn cs) L) as [lo|] eqn:Hlo; [|discriminate Hn].
  destruct (xhi (kn cs) L) as [hi|] eqn:Hhi; [|discriminate Hn].
  destruct ((Z.leb 0 lo && Z.leb hi 4095) && DNA.cls_is (kn cs) DNA.CLS_ABSENT)%bool eqn:Hr; [|discriminate Hn]. injection Hn as <-.
  apply andb_prop in Hr as [Hr Hcls]. apply andb_prop in Hr as [_ Hr]. apply Z.leb_le in Hr.
  pose proof (cls_is_sound E _ (kn cs) _ (co_know HC) Hcls) as Hclsv.
  pose proof (xhi_sound ASEGS E _ (kn cs) L hi (co_know HC) Hhi) as BH.
  change (DNA.two64 - 2) with (DNA.two64 - ENOENT).
  apply (rz_openat_err args L cs E fx R M model ENOENT T HC Hok ltac:(unfold ENOENT; lia)); [|exact Hk].
  intros path rest bs Hargs Hstr Hlen. right. exists bs.
  pose proof Hstr as (Sb & Sn & Sbs).
  pose proof (u64_range (edenot E path)) as Rp.
  split; [|split; [|reflexivity]].
  - rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E path)).
    apply (read_cstr_of_rdn ASEGS M _ bs).
    + lia.
    + destruct Sbs as [-> | ->]; [intros [] | exact (NONUL2 E (co_uinv HC))].
    + apply (cstring_rdn E M _ bs Hstr); [lia|].
      destruct (openat_ok_sound E cs fx R M model args L HC Hok) as (path' & rest' & bs' & Hargs' & _ & _ & _ & _ & _ & _ & Hlen' & _ & Hnw' & _).
      rewrite Hargs in Hargs'. injection Hargs' as <- <-. unfold two64 in *. lia.
  - intros Hne. destruct Sbs as [-> | ->]; [discriminate Hne|].
    rewrite (co_fs HC). apply (ABSENT2 E (co_uinv HC) Hclsv). intros He. rewrite He in Hne. discriminate Hne.
Qed.
End NodesSoundA3.
