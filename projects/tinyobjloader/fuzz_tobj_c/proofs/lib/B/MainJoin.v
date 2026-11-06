(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "pow"; "sub"; "of_nat"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "@Corelib.Init.Datatypes"; "prod"; "nil"; "list"; "app"; "bool"; "cons"; "true"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_fs"; "ExitEv"; "FdEntry"; "VmState"; "WriteEv"; "with_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.MainJoin"; "MDfs"; "P0U"; "SLK0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM"; "S_U"; "S_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "erase_mat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "tcons"; "etriple"; "triple"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "KU"; "bsumK"; "bsumV"; "bd_nn"; "bd_wpos"; "bitem"; "LARGE_MIN"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.MainJoin.MAINJOIN"; "argv0"; "argv1"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "Uv"; "std_fds"; "CST_drv2"; "KcG"; "SHR"; "SHR2"; "ZARG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.SpineA"; "SpecT"; "PAx"; "JMx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "BX0"; "CST_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "VMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "K_T"; "V_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states"; "bd_M0"; "nd_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_geom"; "aa_live"; "ag_tp"; "topG"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM"; "P0M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.op.FpsSite"; "nd_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "PRE_U"; "SUF_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA"; "MSGb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "ok_halted"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "with_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "die"; "msg_usage"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSummary SymEntail SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT DrvIfaceR DrvIfaceM DrvTLXa DrvJ DrvM_states DrvM DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require op.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require SpineA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.op.FpsSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.SpineA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import TAddr MAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition MDfs (FS0 : Fs) (md : Model) : Prop := m_fs md = FS0.
Lemma MDfs_vm : ltac2:(tb__ "0|0|
S3bS15S19S1fR3R2A2S1fR4S69R2R3A2A2F_;Fv;Fmd;FFS0;").
Proof. intros FS0 md v H. unfold MDfs in *. rewrite m_fs_with_vm. exact H. Qed.
Lemma MDfs_fds : ltac2:(tb__ "0|0|
S3bS15ScSaS36Q40A1S18A2A1S1fR3R2A2S1fR4S1bR2R3A2A2F_;Ff;Fmd;FFS0;").
Proof. intros FS0 md f H. unfold MDfs in *. rewrite m_fs_with_fds. exact H. Qed.
Lemma MDfs_fs : ltac2:(tb__ "0|0|
S3bS15S1fR2R1A2S7S3bS16R2A1R3A3F_;Fmd;FFS0;").
Proof. intros FS0 md H. exact H. Qed.

Definition SLK0 (r : valuation) : Prop := ltac2:(tb__ "0|0|
S1S2S3cVr;P5A2Z11A2S3cVr;PcA2A2").
Definition P0U (argv0 : list byte) (r : valuation) : Prop := ltac2:(tb__ "0|5|
S8S7S0S3cVr;P18A2S5fA3S8S40Vr;A1S8S7ScS36Q8M0A1M1A1M2S5cG1S5bS11G1Vargv0;A2M3U1A2S24Vr;P2A2M4A3SdG1Vargv0;SfG1S37G0Z0A2SbG1A1A3A3A3S8S7S0S3cVr;P5A2S6G3A1A3S8S8S42Vr;A1S41Vr;A1A2S8S7G2S24Vr;P3A2G4A3S21Vr;A1A2A2A2A2A2A2").

Section MAINJOIN.
Variable AInv : ltac2:(tb__ "0|0|
S53S23ScS36Q40A1A1S15OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Variables (argv : list (list byte)) (FS0 : Fs).
Variables (Mmain : Model) (B : Z) (rhoM : valuation) (tpM : list word) (A0 : AA).

Hypothesis HMfds : m_fds Mmain = std_fds.
Hypothesis HMfs : m_fs Mmain = FS0.

Hypothesis HAInv : ltac2:(tb__ "0|0|
S15S7S15S29R1A1S29VMmain;A1A3S1S68R2VtpM;A2VB;A2VAInv;VA0;VrhoM;VtpM;R3A4F_;F_;Fmd;").
Hypothesis Htp : ltac2:(tb__ "0|0|
S7S0S38Q40S25VrhoM;P18A2A2S59S57VA0;A1A1A3").
Hypothesis HtopG : ltac2:(tb__ "0|0|
S7S0S5aS57VA0;A1A1S38Q40S25VrhoM;P1eA2A2A3").
Hypothesis Hframes : aa_frames A0 = [].
Hypothesis HV : ltac2:(tb__ "0|2|
S8S8S1Z0M0S56VA0;A1M1A2S1G1Z10000A2A2S8S7S0S55VA0;A1G0A3S7S0S54VA0;A1G0A3A2A2").
Hypothesis Hfresh : classes_fresh A0.
Hypothesis Hnl : large_live A0 = 0.
Hypothesis Hns : small_live A0 = 0.

Lemma no_large_A0 : ltac2:(tb__ "0|1|
SaS0S0A2M0S6cG0R1S58VA0;A1A3S1S35S12S0S0R2A3A2S9F_;F_;Fbn;").
Proof.
  intros bn Hin Hl. unfold large_live in Hnl.
  assert (Hf : In bn (List.filter is_large (aa_live A0))) by (apply filter_In; split; [exact Hin | unfold is_large; apply Z.leb_le; unfold LARGE_MIN in Hl; exact Hl]).
  destruct (List.filter is_large (aa_live A0)); [contradiction | cbn [length] in Hnl; lia].
Qed.

Let Kc0 : KcA := ltac2:(tb__ "0|1|
S3fSbS14A1M0S1fVFS0;A1S3dG0A4").

Lemma ja_init : ltac2:(tb__ "0|2|
S23OF_;S53OF_;ScS34A1S66S2aR5VrhoM;A1R5VA0;A1S7SeS33R5A1S10A3S32R6VrhoM;A2S1Z0M0S31R7VrhoM;A2A2S1G0S30R8VrhoM;A2A2S1S2S56VA0;A1S31R9VrhoM;A2A2S4eA2S1S2S3S2fS2S55VA0;A1S54VA0;A1A2A2S30RaVrhoM;A2A2S3S2fS4dA2A2S1cS13S28VMmain;VB;A2RaVrhoM;VtpM;R9A6S1cS13S4aVAInv;VCST;VXGL;S49VKc0;VrhoM;ReSbSaS0S0A2M1A1SbSaG1S0A2A1S47RdS4cSbSaS22S22A2A1SbSaSaS22S0A2S22A2A1RcS4bA4AcRbVrhoM;VtpM;RaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;FS;Fbd;FPA;FP0;").
Proof.
  intros P0 PA bd S w HP0 HPA Hwp Hnn HsV HsK HBV HBK [Hsm HK]. split; [exact Hsm|].
  destruct HK as (Htr & Hem & Hpaid). destruct (erase_mat_eq_fields _ _ Hem) as (_ & _ & Hfds & _ & _ & Hfs & _).
  exists A0, 0. unfold JAi. cbn [nd_tv nd_fr nd_bd nd_am].
  split; [split; intros; reflexivity|].
  split; [split; [rewrite Htr; reflexivity | split; [rewrite Hfds; exact HMfds | unfold MDfs; rewrite Hfs; exact HMfs]]|].
  split; [exact (HAInv _ Hem Hpaid)|].
  split; [split; [exact Htp | unfold TobjJV.T0; rewrite HtopG; reflexivity]|].
  split; [intros bn []|].
  split; [intros f s fl []|].
  split; [split; [constructor|]; split; [exact I | constructor]|].
  split; [split; [constructor|]; split; [intros x Hx; rewrite Hframes in Hx; destruct Hx | constructor]|].
  split; [apply keptFA_refl|].
  split; [exact HP0|].
  split; [split; [reflexivity | intros bn Hin Hl _ _; exact (no_large_A0 bn Hin Hl)]|].
  split; [|split; [exact HPA | split; [unfold capK, BX0; cbn [bxS]; rewrite Hnl; pose proof (proj1 HV); lia | unfold capN, BX0; cbn [bxN]; rewrite Hns; reflexivity]]].
  unfold BUD, bxa, BX0. cbn [fst snd bx2 apot apotz am_eval]. destruct HV as (HV1 & HV2 & HV3). rewrite HV2, HV3 in HBK |- *.
  repeat split; try lia; assumption.
Qed.

Lemma bd_M0_sums : ltac2:(tb__ "0|0|
S23S8S7S0S31S51R1A2S5S2S50S4Z2Z1bA2A2Z10000A2A3S7S0S30S51R1A2S3S2fS2S4fZ15A2A2A3A2Fr;").
Proof. intros r. unfold bd_M0. cbn [bsumV bsumK]. unfold bival, BIc. cbn [lfval bi_f bi_c bi_v bi_k]. lia. Qed.
Lemma bd_M0_fits : ltac2:(tb__ "0|4|
S8S1S2S5S2S50S4Z2Z1bA2A2Z10000M0A2M1G0A2S4eA2S8S1S3S2fS2S4fZ15A2A2M2S3S2fS4dA2A2S8S1Z0M3G1A2S1G3G2A2A2A2A2").
Proof. unfold V_T, K_T, VMAX, KMAX, V_DRV, K_DRV, NCALLS, CV, CV0, CK_DIV, CK0, MAX_INPUT, KU. cbn. lia. Qed.

Definition argv1 : list byte := nth 1 argv [].
Definition argv0 : list byte := hd [] argv.

Theorem main_join_M : ltac2:(tb__ "0|0|
S2aS60S3aVrhoM;A2S1cS13S28VMmain;VB;A2S27VrhoM;VtpM;R2A6S1cS13S45VAInv;VCST;VXGL;Vargv;VFS0;S1fVFS0;A1VrhoM;S3dS52A9S27VrhoM;VtpM;R3A6F_;F_;Fw;").
Proof.
  intros w HP0 HS. unfold SpineA.JMx, DrvM.JM, DrvM.KcM, nd_M.
  pose proof (bd_M0_sums rhoM) as [EV EK]. pose proof bd_M0_fits as (F1 & F2 & F3 & F4). destruct HV as (HV1 & HV2 & HV3).
  apply (ja_init (DrvM.P0M argv1) (SpineA.PAx argv FS0) bd_M0 DrvIfaceM.S_M w HP0 (SpineA.PAx_init argv FS0 A0 Hfresh));
    [reflexivity | | rewrite EV; lia | rewrite EK; lia | rewrite EV; lia | rewrite EK, HV2, HV3; lia | exact HS].
  unfold bd_nn, bd_M0. repeat constructor; unfold bival, BIc; cbn [lfval bi_f bi_c bi_v bi_k]; lia.
Qed.

Theorem main_join_U : ltac2:(tb__ "0|2|
ScS34A1S2aS7SeS33R2A1S10A3S32R3VrhoM;A2S1Z0M0S31R4VrhoM;A2A2S1G0S30R5VrhoM;A2A2S1S2S31R6VrhoM;A2Z10000A2S4eA2S1S30R7VrhoM;A2S3S2fS4dA2A2S20S39VrhoM;A2S1cS13S28VMmain;VB;A2S26VrhoM;VtpM;R8A6S1cS13S4aVAInv;VCST;VXGL;S49VKc0;VrhoM;S20S39A1SbSaS0S0A2M1A1SbSaG1S0A2A1S47S44Vargv;VFS0;A2S4cSbSaS22S22A2A1SbSaSaS22S0A2S22A2A1RaS4bA4AcS26VrhoM;VtpM;R9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;FbdU;").
Proof.
  intros bdU w Hwp Hnn HsV HsK HBV HBK HP0 HS. destruct HV as (HV1 & HV2 & HV3).
  apply (ja_init (P0U argv0) (SpineA.PAx argv FS0) bdU DrvIfaceM.S_U w HP0 (SpineA.PAx_init argv FS0 A0 Hfresh) Hwp Hnn HsV HsK);
    [lia | rewrite HV2, HV3; lia | exact HS].
Qed.

Section Usage.
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S0S46S48R1A2S46VCST;R2A2F_;Fz;").
Hypothesis HLPP : DrvTLXa.law_pp_stmt AInv CST.
Hypothesis HCSTdrv2 : ltac2:(tb__ "0|0|
S0S46S3eR1A2S46VCST;R2A2F_;Fz;").
Hypothesis Hargc : length argv <> 2%nat.
Hypothesis Hnonul0 : ~ In (Z_to_bv 8 0) argv0.
Hypothesis HP0 : P0U argv0 rhoM.

Lemma HSPEC_U : ltac2:(tb__ "0|1|
S15S1fVFS0;R1A2S43Vargv;VFS0;SdS14SbS14A1M0SdS14G0SdS14S5dS36Q8A1S14S1aS5eA1S64S62S63S39A3A4SfS14S17S37Q40Z2A2S16R2A1A2G0A3A3A3A3A3F_;Fmd;").
Proof.
  intros md Hmd. rewrite (MDfs_fs FS0 md Hmd). cbn [app]. rewrite SpineA.MSGb_U, SpineA.die_eq. unfold SpineA.SpecT, argv0. apply spec_usage. exact Hargc.
Qed.

Lemma join_U : ltac2:(tb__ "0|1|
S2aS1cS13S28VMmain;VB;A2S26VrhoM;VtpM;R1A6S1cS13S4aVAInv;VCST;VXGL;S49VKc0;VrhoM;S20S39A1SbSaS0S0A2M0A1SbSaG0S0A2A1S47S44Vargv;VFS0;A2S61AcS26VrhoM;VtpM;R2A6F_;Fw;").
Proof.
  intros w HS. unfold nd_U.
  apply (main_join_U [] w eq_refl (Forall_nil _)); [cbn; lia | cbn; lia | | | exact HP0 | exact HS];
    unfold VMAX, KMAX, V_DRV, K_DRV, NCALLS, CV, CV0, CK_DIV, CK0, MAX_INPUT, KU; cbn; lia.
Qed.

Section S.
Variable ok : world -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S1dS23ScS36Q40A1A1ScS14A1S15R5R4R3R2R1A4S2bS43Vargv;VFS0;A2R3A2F_;Fmd;Ftr;Ftp;Frho;S1eS13Vok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S1dS23ScS36Q40A1A1ScS14A1S15R5R4R3R2R1A4S2bS43Vargv;VFS0;A2R3A2F_;Fmd;Ftr;Ftp;Frho;S67S13Vok;R2A3F_;FJ;").
Hypothesis Hokh : ltac2:(tb__ "0|0|
S65Vok;S43Vargv;VFS0;A2A2").
Theorem usage_safe : ltac2:(tb__ "0|0|
S2dS13Vok;S1cS13S28VMmain;VB;A2S26VrhoM;VtpM;A5S2aS9L_;A4").
Proof.
  eapply (triple_conseq (P := SPA segs (JA AInv CST XGL NF Kc0 rhoM (P0U argv0) [] [] BX0 (SpineA.PAx argv FS0) nd_U) DrvIfaceM.S_U rhoM tpM));
    [intros w HS; exact (join_U w HS) | intros w' Hw'; exact Hw' |].
  exact (usage_tail_safe AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 ok (SpineA.SpecT argv FS0) HOKJ HOKP Hokh [] (MDfs FS0) (MDfs_vm FS0)
           std_fds eq_refl eq_refl rhoM (P0U argv0) (SpineA.PAx argv FS0) argv0 Hnonul0 (fun r H => H) HSPEC_U rhoM tpM).
Qed.
End S.

Theorem usage_ex : ltac2:(tb__ "0|0|
S2cS13S1cS13S28VMmain;VB;A2S26VrhoM;VtpM;A5S2aS7ScS14A1S2eR1A1S6aVFS0;S6bS39A1A2A3Lw;A3").
Proof.
  eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF Kc0 rhoM (P0U argv0) [] [] BX0 (SpineA.PAx argv FS0) nd_U) DrvIfaceM.S_U rhoM tpM));
    [intros w HS; exact (join_U w HS) | intros w' Hw'; exact Hw' |].
  apply (usage_tail_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 (SpineA.SpecT argv FS0) [] (MDfs FS0) (MDfs_vm FS0)
           std_fds eq_refl eq_refl rhoM (P0U argv0) (SpineA.PAx argv FS0) argv0 Hnonul0 (fun r H => H) HSPEC_U).
  intros w md Hmd Hw. rewrite Hw, (MDfs_fs FS0 md Hmd). cbn [app]. rewrite SpineA.MSGb_U, SpineA.die_eq. reflexivity.
Qed.
End Usage.
End MAINJOIN.
