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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntry.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootAsan2 AsanRun AsanImgx AsanDrun AsanApart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops ClientX TdOps TdInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanU Require UnivAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L Require T_Asan2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E Require T_Asan2E.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Asan_r12.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run Require RunAsanF TopHypsAsanF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP StepB StepS PlanS FXN CertS DrvLib LibLib HeapOp DrvShape.
Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Open Scope Z_scope.
Unset Lia Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.
Module R2 := RootAsan2.RootAsan2.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.

Section TopAsanF.
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
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono asegs m m' -> AHEAP AIu2 L RNG st LB m'.
Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Let Cw : client_world := Ops.UO.unp_cw asegs (ClientX.CX.XTP asegs).

Variables (en : ExecEntry) (inp : ProcInput).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hsp : valid_sp (en_sp en).
Hypothesis Hfit : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hargc2 : length (in_argv inp) = 2%nat.
Let p1 := AsanDrun.p1 inp.
Let file := AsanDrun.file inp.
Hypothesis Hfile : fs_lookup (in_fs inp) p1 = Some file.
Hypothesis Hndir : path_is_dirref p1 = false.
Hypothesis Hne : p1 <> [].
Hypothesis Hshort : (length p1 < 4096)%nat.
Let RAx : drun := AsanDrun.RA AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivAsan.UNIV AI_frame_top Cw ACCT_fds AsanImgx.IMGX_A_rs3 inp (en_sp en) (en_draw en) Hva.
Hypothesis cF : ctab_ok asegs RAx T_Asan2F.CONTRACTS.
Hypothesis cL : ctab_ok asegs RAx T_Asan2L.CONTRACTS.
Hypothesis cE : ctab_ok asegs RAx T_Asan2E.CONTRACTS.
Hypothesis G0 : forall E0 K, r_PB RAx (Val.eb E0) -> LNODE asegs RAx Asan_r12.LibRunAsan_r12.N E0 K (t_st T_Asan2F.R_LIBGEN_r12_RET) ->
  LNODE asegs RAx Asan_r12.LibRunAsan_r12.N E0 K (t_st T_Asan2L.T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0).

Lemma CW0 : forall m ws, Forall (fun w => w_kind w = K_STACK) ws -> cw_holds Cw 0 [] [] ws m.
Proof.
  intros m ws H. unfold Cw. apply TdInst.TdInst.cw0. apply TdOps.TD.nosub_kinds. intros w Hw. left.
  rewrite (proj1 (Forall_forall _ _) H w Hw). unfold K_STACK, K_SUB. lia.
Qed.

Lemma p1_noslash : path_has_slash p1 = false.
Proof.
  pose proof Hva as (_ & _ & _ & _ & HS). unfold p1, AsanDrun.p1. clear - HS. destruct (in_argv inp) as [|x [|y l]]; cbn [hd tl]; try reflexivity.
  exact (proj1 (proj1 (Forall_forall _ _) HS y (or_introl eq_refl))).
Qed.
Theorem rz_file_asan_top : forall ms mo (L : alayout) (RNG : footprint) (sta : astate),
  ME.amain_at en inp ms mo ->
  bv_unsigned (en_sp en) = ATOP + 8388608 ->
  AHEAP AIu2 L RNG sta [] (ms_mem ms) -> ACCT (wbv (wlit RunAsanF.CRED0i)) L RNG sta [] mo -> incl UnivAsan.UNIV (al_U L) -> lazy_shape C0 mo -> aprist sta ->
  OUR.realizes asegs (mkCfg ms mo) (K inp).
Proof.
  intros ms mo L RNG sta HM USP AH AC HU LZ APR. pose proof (@AsanApart.IMGX_A_apart2 rc) as IMGAP.
  exact (RunAsanF.rz_file_asan AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivAsan.UNIV AI_frame_top Cw ACCT_fds
           AsanImgx.IMGX_A_rs3 AsanImgx.IMGX_A_stksh en inp Hva Hve Hsp Hfit Hhw Hargc2
           (TopHypsAsanF.hypsF inp (en_sp en) (en_draw en) Hva ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat AI_frame_top ACCT_fds
              Hfile p1_noslash Hndir Hne Hshort cF cL cE G0)
           Hfile Hndir Hne Hshort ms mo L RNG sta HM USP AH AC HU LZ APR (CW0 (ms_mem ms)) IMGAP).
Qed.
End TopAsanF.

