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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op. Import Ledger.TwinB Op.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanRun AsanImgx AsanDrun AsanPB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops ClientX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothU Require UnivBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2F Require T_Both2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2L Require T_Both2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E Require T_Both2E.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Both2F_1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Both_r9 Both_r12.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP StepB StepS PlanS FXN CertS DrvLib LibLib HeapOp DrvShape.
Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Open Scope Z_scope.
Unset Lia Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section TopHypsBothF.
Context {rc : runConstT}.
Variable inp : ProcInput.
Variables (sp : word) (rnd : EntryDraw).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Let p1 : list byte := AsanDrun.TwinB.p1 inp.
Let file : list byte := AsanDrun.TwinB.file inp.
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
Let Cw : client_world := Ops.UO.unp_cw bsegs (ClientX.CX.XTP bsegs).
Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Let RAx : drun := AsanDrun.TwinB.RA AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UnivBoth.UNIV AI_frame_top Cw ACCT_fds AsanImgx.TwinB.IMGX_A_rs3 inp sp rnd Hva.

Hypothesis Hfile : fs_lookup (in_fs inp) p1 = Some file.
Hypothesis Hnoslash : path_has_slash p1 = false.
Hypothesis Hndir : path_is_dirref p1 = false.
Hypothesis Hne : p1 <> [].
Hypothesis Hshort : (length p1 < 4096)%nat.
Lemma HFILE : fs_lookup (in_fs inp) (AsanDrun.TwinB.p1 inp) <> None.
Proof. fold p1. rewrite Hfile. discriminate. Qed.

Hypothesis cF : ctab_ok bsegs RAx T_Both2F.CONTRACTS.
Hypothesis cL : ctab_ok bsegs RAx T_Both2L.CONTRACTS.
Hypothesis cE : ctab_ok bsegs RAx T_Both2E.CONTRACTS.

Hypothesis G0 : forall E0 K, r_PB RAx (eb E0) -> LNODE bsegs RAx Both_r12.LibRunBoth_r12.N E0 K (t_st T_Both2F.R_LIBGEN_r12_RET) ->
  LNODE bsegs RAx Both_r12.LibRunBoth_r12.N E0 K (t_st T_Both2L.T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0).

Lemma file_pb_RA : file_pb RAx.
Proof. intros b H. cbn [r_PB RAx AsanDrun.TwinB.RA] in H. unfold AsanDrun.TwinB.PB in H. rewrite H. cbn [r_file RAx AsanDrun.TwinB.RA]. repeat split; reflexivity. Qed.

Theorem hypsF : Both2F_1.hyps RAx.
Proof.
  refine (Both2F_1.Hyps RAx cF file_pb_RA _ _ _ _).
  - intros m Hm. cbn [r_p1 r_file RAx AsanDrun.TwinB.RA]. exact (AsanPB.TwinB.MP_file inp HFILE m Hm).
  - cbn [r_p1 RAx AsanDrun.TwinB.RA]. fold p1. repeat split; assumption.
  - exact (Both_r12.LibRunBoth_r12.lib_ok_r12 RAx cL cE G0).
  - exact (Both_r9.LibRunBoth_r9.lib_ok_r9 RAx cL cE).
Qed.
End TopHypsBothF.

