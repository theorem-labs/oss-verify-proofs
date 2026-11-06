(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstFreeSecRhreply.v (commit eb934de95d13, blob 40f2b0ab196f) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstFreeSig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstRcPrim DMwalkIFA DMrcReadsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcSecCutCf DMrcSecMaprCf DMrcSecCf DMrcRhA DMrcCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFg8 YGcfInstRcSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehideAR YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM03.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Local Ltac lia := YM03.lf_lia_orig.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Existing Instance AImg_A.
Local Existing Instance DImg_A.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis HIOK : IOK_ok B IOK.
Hypothesis EAP : YGcfImgRows.ERRB_QAPART.
Hypothesis RLE : DMrcSecCf.REC_LE.

Hypothesis NBIG : kQuarantineMax <= cf_malloc_max + 1.

Lemma big_map_above : cf_malloc_max + 1 <= sec_map_size cf_malloc_max.
Proof.
pose proof cf_malloc_max_pos as MP. assert (P20 : 2 ^ 20 = 1048576) by reflexivity.
assert (M1 : 1048576 <= cf_malloc_max) by (rewrite <- P20; exact MP). clear MP P20.
assert (M0 : 0 <= cf_malloc_max) by lia.
pose proof (rounded_size_bounds cf_malloc_max M0) as [R1 _].
pose proof (rz_size_bounds cf_malloc_max) as [Z1 _].
pose proof (req_size_bounds cf_malloc_max M0) as (_ & _ & Q3).
assert (FP : from_primary cf_malloc_max = false).
{ unfold from_primary, needed_primary. apply Z.leb_gt. unfold kMaxSize. lia. }
pose proof (secondary_geometry cf_malloc_max M0 FP) as (_ & _ & S3 & _).
unfold kPage, kSecRz in S3. lia.
Qed.

Lemma sec_pre_rh_sec_cf : forall inst ly X k cbp W regs mem md r o sm i,
  rcc_pre_sec B (YGcfInstDrainR.ARXr_cf B IOK Hp) inst ly X k cbp W regs mem md -> ck_beg k = PSec r o ->
  nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r -> In k (st_chunks X) ->
  In (shull (AFg8.MAP ly r, AFg8.LEN sm)) (w_A W) /\ YGcfRehidePost.sec_real sm /\
  Forall (zdisjoint (AFg8.MAP ly r, AFg8.LEN sm)) (sec_extents ly (AFg8.X2v X k r sm i)) /\
  kMaxSize + kPage <= AFg8.LEN sm.
Proof.
intros inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hk.
pose proof (proj1 (proj2 (proj1 PRE))) as MR.
pose proof (@YGcfInstRcSec.KFACTS rc ci cp AImg_A B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & EL & _ & _ & GI & _).
pose proof (proj1 (Forall_forall _ _) (YG03cf.wfr_chunks _ _ _ _ _ (YGcfInstDrainR.amr_wfr _ _ _ _ _ (proj1 MR))) k Hk) as CK.
assert (EL' : AFg8.LEN sm = YGcfInstRcSec.LEN k) by exact EL.
split.
{ pose proof MR as (_ & _ & (_ & SA & _) & _). rewrite EL'. exact (proj2 (SA _ GI)). }
split; [exact (YGcfRehideAR.SREAL_of_pre X k r o sm CK Hb Hsm)|].
split; [|exact (YGcfRehideAR.M2_of_pre X k r o sm CK Hb Hsm)].
apply Forall_forall. intros e He. rewrite <- DMrcSecCf.X2_eq in He.
apply YGcfRehideAR.zdisjoint_sym_rh. rewrite EL'.
exact (YGcfInstRcSec.APART2 (IM := AImg_A) B ly X Hp k r o sm i W mem md MR Hk Hb Hsm e He).
Qed.

Theorem SEC_rh_preset :
  SEC_rh_t B (aowned B) (YGcfInstDrainR.ARXr_cf B IOK Hp) (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf).
Proof.
intros inst ly X k ks zs cbp W regs mem md r o sm i PRE RX Hb Hsm Hi.
pose proof YG08cf.cf_malloc_max_bound as MB. pose proof cf_malloc_max_pos as MP. pose proof big_map_above as BMA.
assert (P20 : 2 ^ 20 = 1048576) by reflexivity.
assert (P30 : 2 ^ 30 = 1073741824) by reflexivity.
assert (M1 : 1048576 <= cf_malloc_max) by (rewrite <- P20; exact MP).
assert (M2 : cf_malloc_max + 15 <= 1073741824) by (rewrite <- P30; exact MB).
assert (NB' : 268435456 <= cf_malloc_max + 1) by (unfold kQuarantineMax in NBIG; exact NBIG).
assert (NOK : DMwalkIFA.nmaxd_ok (YGcfInstDrainR.NMAXD_big_cf + 1)).
{ unfold DMwalkIFA.nmaxd_ok, YGcfInstDrainR.NMAXD_big_cf. split; [exact NBIG|]. rewrite P30. lia. }
assert (LOK : DMwalkIFA.lmaxd_ok (YGcfInstDrainR.NMAXD_big_cf + 1) (sec_map_size YGcfInstDrainR.NMAXD_big_cf)).
{ pose proof YGcfInstDrainR.lmaxd_ok_big_cf as [L1 L2]. unfold DMwalkIFA.lmaxd_ok, YGcfInstDrainR.LMAXD_big_cf in *.
  unfold YGcfInstDrainR.NMAXD_big_cf in *. lia. }
assert (RDS : DMwalkIFA.drq_sizes (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf) (YGcfInstDrainR.NMAXD_big_cf + 1)
  (sec_map_size YGcfInstDrainR.NMAXD_big_cf)).
{ intros S0 its zs0 k0 D Hin. eapply YGcfInstDrainR.drq_sizes_cf; [|exact D|exact Hin].
  unfold YGcfInstDrainR.NMAXD_big_cf, kMaxSize. lia. }
assert (RHD : DMrcReadsA.rc_head_t (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf)).
{ intros X0 k0 ks0 zs0 D. eapply YGcfInstRcPrim.rc_head_cf. exact D. }
assert (RMD : DMrcReadsA.rc_model_t (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf)).
{ intros X0 k0 ks0 zs0 D. eapply YGcfInstRcPrim.rc_model_cf. exact D. }
pose proof (DMrcSecCutCf.rc_sec_cut_nf_of_cf B TB IOK Hp HIOK) as RCnf.
pose proof (DMrcSecMaprCf.rc_sec_mapr_nf_of_cf B TB IOK Hp) as RMnf.
pose proof (DMrcSecCf.rc_sec_step_nf_sl_of_cf B TB IOK Hp EAP RLE) as RSnf.

pose proof RX as ((_ & IT & _) & _).
apply Forall_app in IT as [IT _]. apply Forall_cons_iff in IT as [[Hk _] _].
destruct (sec_pre_rh_sec_cf inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hk) as (HULL & SREAL & HM1 & HM2).
exact (DMrcRhA.rchunk_sec_rh_nf B TB _ (DMrcSecCf.ARXsl_cf B IOK Hp) (aowned B) _ _ _ NOK LOK RCnf RMnf RSnf RHD RMD RDS
  inst ly X k ks zs cbp W regs mem md r o sm i PRE RX Hb Hsm Hi HULL SREAL HM1 HM2
  (DMrcCf.rc_sec_rehide_all_cf B IOK Hp inst ly X k r sm i)).
Qed.
End c.
