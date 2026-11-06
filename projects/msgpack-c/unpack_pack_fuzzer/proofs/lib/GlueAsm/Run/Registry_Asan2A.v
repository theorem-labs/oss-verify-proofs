(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanOps AsanRun AsanImgx.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops ClientX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require F1Unp WPatSub.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require MemsetPre WPat AsanDrun AsanPB MemcpySound MemcpyFinal Memcpy0Sound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm Require F1Cw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RoLitA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm Require RoLitInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AcctPlug AsanAcct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AInstanceArena.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require HnrInst SmInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ahnr.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Ctr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrAnnot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrTwinIn.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrTwinOut.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require CaseF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require GTwinSub.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AmallocNnSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanDrun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanRun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require BlobFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require FaSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require FfSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require FprintfFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require FprintfSFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require FwriteFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require FwritePostFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require HnrSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Memcpy0Sound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require MemcpyFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require MemcpyPFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require MemsetFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require MemsetPFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require NnDel.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require OpDropSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require PayloadFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadDirFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RstageFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require SinkFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require SmSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require StrlenFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require StrnlenFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require TlsSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require VprintfFinal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require PkInstB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require PkMidInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require PkShrinkInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GRealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GUnrealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require PkInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require PkInstA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require TdInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require UnpInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require G6RegrowInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require GCapB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require GTwinBnd.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require GVEndA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require UnpInstA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require DrvLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FaC RangeC StrRegC ReadC MemsetC MemcpyC Memcpy0C PubC MemcpyPC MemsetPC RstageC BlobC PayloadC HalfC VprintfC FprintfC FprintfSC StrnlenC FwriteC FwritePostC UnreggC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import GshC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StrlenC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import OpDropC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RoLitA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AmallocNnC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadDirC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GViewDrop2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GUnrealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GBgNone.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanU Require UnivAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2A Require T_Asan2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St HeapOp.
Open Scope Z_scope.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Local Notation AIu_fake := (FakeLaw.AIu_fake ExhFirst.exh_first).
Section Reg.
Context {rc : runConstT}.

Variable inp : ProcInput.
Variables (sp : word) (rnd : EntryDraw).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Let p1 : list byte := AsanDrun.p1 inp.
Let file : list byte := AsanDrun.file inp.
Let MP : Model -> Prop := AsanDrun.MP inp.
Let PB : (int -> list byte) -> Prop := AsanDrun.PB inp sp rnd.
Let ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop := Acct.ACCT AsanAcct.NMAX AsanAcct.SHFIX.
Let COVP : Model -> word -> Prop := Acct.COVPb AsanAcct.SHFIX.
Let NMAX : nat := AsanAcct.NMAX.
Let ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p) := AcctPlug.ACCT_ledx.
Let ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z) := AcctPlug.ACCT_covx.
Let ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z) := AcctPlug.ACCT_cov_shx.
Let ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo' := AcctPlug.ACCT_matx.
Let UNIV : list (list Z) := UnivAsan.UNIV.
Let AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono asegs m m' -> AHEAP AIu2 L RNG st LB m' := AcctPlug.AI_frame_topx.
Let Cw : client_world := Ops.UO.unp_cw asegs (ClientX.CX.XTP asegs).
Let ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo) := AcctPlug.ACCT_fdsx.
Let OPSA : optable := AsanRun.OPSA AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.
Let MINV : Model -> Prop := op_minv OPSA.
Let MINV_intro : forall mo, m_halted mo = None -> Acct.lazy_shapeA Acct.C0A mo -> MINV mo := AcctPlug.MINV_introx.
Let AWAx := AWA AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake.
Let HOPSx := (AsanRun.OPSA_heap_ops AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file AsanImgx.IMGX_A_stage AsanImgx.IMGX_A_cov AsanImgx.IMGX_A_shlit AsanImgx.IMGX_A_stksh).
Let W_PAT_SUBx := F1Cw.W_PAT_SUB_A ACCT UNIV.
Let W_PATx := (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.WPat.w_pat_ok AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake W_PAT_SUBx).
Let CHSx := GLib.UG.chg_user asegs AsanImgx.IMGX_A AWAx OPSA.
Let RAx : DrvLib.DrvLib.drun := AsanDrun.RA AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw ACCT_fds AsanImgx.IMGX_A_rs3 inp sp rnd Hva.
Local Ltac ra_0 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.amemcpy_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_ssh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zro AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_gsh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_shmap AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) W_PAT_SUBx (F1Unp.F1Unp.cw_sub_ghost asegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_1 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.aasan_memcpy_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_ssh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zro AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_gsh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_shmap AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) W_PAT_SUBx (F1Unp.F1Unp.cw_sub_ghost asegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_2 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.amemcpy0_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_3 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.aasan_memcpy0_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_4 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.StrnlenFinal.astrnlen_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (AsanPB.PB_str inp sp rnd Hva) (AsanPB.PB12 inp sp rnd Hsp Hfit)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_5 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.FprintfSFinal.afprintf_pre_usage_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_zro AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (AsanPB.PB_str inp sp rnd Hva)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_6 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.FprintfSFinal.afprintf_pre_cantopen_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_zro AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (AsanPB.PB_str inp sp rnd Hva)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_7 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.FprintfSFinal.afprintf_pre_readerr_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_zro AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (AsanPB.PB_str inp sp rnd Hva)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_8 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.UnreggFinal.unregg_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_shmap AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanImgx.ACI_mtx_A AsanImgx.ACI_glob_A AsanImgx.ACI_desc_A (AsanRun.OPSA_fp_mtx AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_shw AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_9 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.OpDropSound.op_drop_sound asegs OPSA MP PB (AsanRun.OPSA_cov1_heap AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_10 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.RoLit.RoLit.rolit_sound asegs OPSA RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_ASAN asegs) CHSx (AsanRun.OPSA_acc_user_law AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (RoLitInst.OPSA_rolit_HR AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB (AsanPB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Definition ctab_Asan2A := let _USE := (Hva, Hsp, Hfit, ACCT_led, ACCT_cov, ACCT_cov_sh, ACCT_mat, AI_frame_top, ACCT_fds) in
  fun (h_FAM_ABSENT : _) =>
  (ltac:(apply (DrvLib.DrvLib.ctab_ok_of_list asegs RAx); repeat (apply Forall_cons || apply Forall_nil); cbn [snd];
    [ first [ (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.AsanDrun.open_absent_sound_RA AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw inp sp rnd Hva h_FAM_ABSENT _); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]) | fail 1 "registry row cid 26 (c_open_absent): no census theorem applies" ]
    | first [ ra_0 | ra_1 | fail 1 "registry row cid 410 (amemcpy_c): no census theorem applies" ]
    | first [ ra_2 | ra_3 | fail 1 "registry row cid 414 (amemcpy0_c): no census theorem applies" ]
    | first [ ra_4 | fail 1 "registry row cid 421 (astrnlen_c): no census theorem applies" ]
    | first [ ra_5 | ra_6 | ra_7 | fail 1 "registry row cid 425 (afprintf_s_pre_c): no census theorem applies" ]
    | first [ ra_8 | fail 1 "registry row cid 429 (unregg_c): no census theorem applies" ]
    | first [ ra_9 | fail 1 "registry row cid 440 (op_drop_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442244560 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442244596 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442575820 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442575824 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442624244 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442624248 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442776648 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442776652 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442776660 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442777364 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442798596 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442802020 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442802508 (rolit_c): no census theorem applies" ] ]) : DrvLib.DrvLib.ctab_ok asegs RAx T_Asan2A.CONTRACTS).
End Reg.
