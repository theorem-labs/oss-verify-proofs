(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto ABase AMalloc_iface AInstanceM AInstanceU AMalloc_iface2 AInstanceU2. Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB AMalloc_iface2.TwinB AInstanceU2.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntryBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op. Import Ledger.TwinB Op.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanRun AsanImgx AsanDrun AsanApart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootBoth2 RootBothN.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops ClientX TdOps TdInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothU Require UnivBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2A Require T_Both2A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2T Require T_Both2T.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothNU Require T_BothNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2D Require T_Both2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.Run Require RunBothATND.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Both2A_1 Both2T_1 BothNU_1 Both2D_1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP StepB StepS PlanS FXN CertS DrvLib LibLib HeapOp DrvShape.
Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Open Scope Z_scope.
Unset Lia Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.
Module R2 := RootBoth2.RootBoth2.
Module RN := RootBothN.RootBothN.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.

Section TopBothATND.
Context {rc : runConstT}.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono bsegs m m' -> AHEAP AIu2 L RNG st LB m'.
Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Let Cw : client_world := Ops.UO.unp_cw bsegs (ClientX.CX.XTP bsegs).

Variables (en : ExecEntry) (inp : ProcInput).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hsp : valid_sp (en_sp en).
Hypothesis Hfit : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Let p1 := AsanDrun.TwinB.p1 inp.
Let RAx : drun := AsanDrun.TwinB.RA AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivBoth.UNIV AI_frame_top Cw ACCT_fds AsanImgx.TwinB.IMGX_A_rs3 inp (en_sp en) (en_draw en) Hva.

Lemma CW0 : forall m ws, Forall (fun w => w_kind w = K_STACK) ws -> cw_holds Cw 0 [] [] ws m.
Proof.
  intros m ws H. unfold Cw. apply TdInst.TdInst.cw0. apply TdOps.TD.nosub_kinds. intros w Hw. left.
  rewrite (proj1 (Forall_forall _ _) H w Hw). unfold K_STACK, K_SUB. lia.
Qed.

Definition H0_at (ms : machine_state) (mo : Model) (L : alayout) (RNG : footprint) (sta : astate) (PRIV : list (int * int)) : Prop :=
  ME.bmain_at en inp ms mo /\ bv_unsigned (en_sp en) = ATOP + 8388608 /\
  AHEAP AIu2 L RNG sta [] (ms_mem ms) /\ ACCT (wbv (wlit RunBothATND.CRED0i)) L RNG sta [] mo /\ incl UnivBoth.UNIV (al_U L) /\ lazy_shape C0 mo /\ aprist sta.

Theorem rz_absent_asan_top : forall ms mo (L : alayout) (RNG : footprint) (sta : astate),
  length (in_argv inp) = 2%nat -> (length p1 < 4096)%nat -> (p1 = [] \/ (path_is_dirref p1 = false /\ fs_lookup (in_fs inp) p1 = None)) ->
  ctab_ok bsegs RAx T_Both2A.CONTRACTS ->
  H0_at ms mo L RNG sta R2.PRIV -> OUR.realizes bsegs (mkCfg ms mo) (K inp).
Proof.
  intros ms mo L RNG sta Hargc2 Hshort Hcase cA (HM & USP & AH & AC & HU & LZ & APR).
  exact (RunBothATND.rz_absent_asan AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivBoth.UNIV AI_frame_top Cw ACCT_fds
           AsanImgx.TwinB.IMGX_A_rs3 AsanImgx.TwinB.IMGX_A_stksh en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta HM USP AH AC HU LZ APR (CW0 (ms_mem ms)) (@AsanApart.TwinB.IMGX_A_apart2 rc)
           Hargc2 Hshort Hcase (Both2A_1.Hyps RAx cA)).
Qed.

Theorem rz_toolong_asan_top : forall ms mo (L : alayout) (RNG : footprint) (sta : astate),
  length (in_argv inp) = 2%nat -> (4096 <= length p1)%nat ->
  ctab_ok bsegs RAx T_Both2T.CONTRACTS ->
  H0_at ms mo L RNG sta R2.PRIV -> OUR.realizes bsegs (mkCfg ms mo) (K inp).
Proof.
  intros ms mo L RNG sta Hargc2 Hlong cT (HM & USP & AH & AC & HU & LZ & APR).
  exact (RunBothATND.rz_toolong_asan AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivBoth.UNIV AI_frame_top Cw ACCT_fds
           AsanImgx.TwinB.IMGX_A_rs3 AsanImgx.TwinB.IMGX_A_stksh en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta HM USP AH AC HU LZ APR (CW0 (ms_mem ms)) (@AsanApart.TwinB.IMGX_A_apart2 rc)
           Hargc2 Hlong (Both2T_1.Hyps RAx cT)).
Qed.

Theorem rz_dir_asan_top : forall ms mo (L : alayout) (RNG : footprint) (sta : astate),
  length (in_argv inp) = 2%nat -> path_is_dirref p1 = true ->
  ctab_ok bsegs RAx T_Both2D.CONTRACTS ->
  H0_at ms mo L RNG sta R2.PRIV -> OUR.realizes bsegs (mkCfg ms mo) (K inp).
Proof.
  intros ms mo L RNG sta Hargc2 Hdir cD (HM & USP & AH & AC & HU & LZ & APR).
  exact (RunBothATND.rz_dir_asan AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivBoth.UNIV AI_frame_top Cw ACCT_fds
           AsanImgx.TwinB.IMGX_A_rs3 AsanImgx.TwinB.IMGX_A_stksh en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta HM USP AH AC HU LZ APR (CW0 (ms_mem ms)) (@AsanApart.TwinB.IMGX_A_apart2 rc)
           Hargc2 Hdir (Both2D_1.Hyps RAx cD Hdir)).
Qed.

Theorem rz_usage_asan_top : forall ms mo (L : alayout) (RNG : footprint) (sta : astate),
  length (in_argv inp) <> 2%nat ->
  ctab_ok bsegs RAx T_BothNU.CONTRACTS ->
  H0_at ms mo L RNG sta RN.PRIV -> OUR.realizes bsegs (mkCfg ms mo) (K inp).
Proof.
  intros ms mo L RNG sta HargcN cN (HM & USP & AH & AC & HU & LZ & APR).
  exact (RunBothATND.rz_usage_asan AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivBoth.UNIV AI_frame_top Cw ACCT_fds
           AsanImgx.TwinB.IMGX_A_rs3 AsanImgx.TwinB.IMGX_A_stksh en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta HM USP AH AC HU LZ APR (CW0 (ms_mem ms)) (@AsanApart.TwinB.IMGX_A_apartN rc)
           HargcN (BothNU_1.Hyps RAx cN)).
Qed.
End TopBothATND.
