(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; a copy of GlueAsm/Run/Registry_Asan2U.v for the start state with CONFIG_RSEQ (its certificates' paths renamed to the CONFIG_RSEQ copies; each failure message that held a run of 7 or more hex digits written as pieces that hold none, the same text). *)
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GFmv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkMid.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkLoad2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkFld2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpShLoad.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkRegrowAC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkBodyAC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Ops GLib GUnp GWin G2 G2Z G2B G3 G3P G4 GRoom G1 G0 G6 GCap GNz GShr GCur GBnd VDestroy GSplit GName GVEnd GInv TdEnter Td PkOps PkEnter PkExit PkStack PkPeek PkFld PkBody PkRegrow PkCap PkInv G0A G1A G3PA G4A G6A GInvA GWinA GBndA GMid GNarrow GNameA GPerm GTwinViewC GVecHi GViewDrop2 GSeal GPotHR Pot GPot GPotInit GPotName OpShLoadU GGran GGranP GChk GBgNone GExcl GRoomA GAncA GCnt GCurA PkShrink.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import SinkC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require Import G6RegrowAC GCapB GTwinBnd GVEndA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2UR Require T_Asan2U.
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
Hypothesis Hvl : valid_launch inp.
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
Local Ltac ra_0 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.TdInst.TdInst.tdenter_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_1 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.TdInst.TdInst.znext_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_2 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.g0a_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_3 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g2z_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_4 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g2_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_5 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g2b_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_6 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.g3pa_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_7 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.grooma_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_8 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g3r_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_9 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gcap_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_10 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gnz_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_11 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.g4a_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_12 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gsplit_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_13 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.g1a_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_14 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.G6RegrowInst.G6RegrowInst.g6regrow_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV (ClientX.CX.XTP asegs) OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.F1Unp.cw_sub_ghost asegs) W_PATx MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) MemcpySound.ASAN_MEMCPY_SYM MemcpyFinal.memcpy_walk_asan 379908%uint63 eq_refl AWAx HOPSx _); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_15 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.roome_a_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_16 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.push_a_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_17 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.next_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_18 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pop_a_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_19 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.push0_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_20 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkenter_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_21 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkexit_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_22 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.peek_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_23 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkInstB.PkInstB.pkextb_sound AsanImgx.IMGX_A OPSA MP PB AWAx HOPSx (AsanPB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_24 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkcap_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_25 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gname_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_26 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.ginva_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_27 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkinv_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_28 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.amalloc_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok AsanImgx.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_grow (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (FakeLaw.AIu_errno ExhFirst.exh_first) (Acct.ACCT_malloc AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_29 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.afree_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok AsanImgx.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_free (F1Unp.F1Unp.cw_vec_unowned asegs) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_free AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_30 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.arealloc_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok AsanImgx.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_grow F1Cw.Cw_ghost_free (F1Unp.F1Unp.cw_vec_unowned asegs) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (FakeLaw.AIu_errno ExhFirst.exh_first) (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (FakeLaw.AIu_realloc ExhFirst.exh_first) (Acct.ACCT_realloc AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_31 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.stack_malloc_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok AsanImgx.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_grow_f MP PB AsanAcct.NMAX 0%uint63 eq_refl 16384 AsanW.AFake_sm0.AFake_sm0.ASTKMALLOC0 ltac:(lia) SmInst.sm_walk_0 (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frame_in AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_32 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.stack_malloc_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok AsanImgx.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_grow_f MP PB AsanAcct.NMAX 1%uint63 eq_refl 8192 AsanW.AFake_sm0.AFake_sm1g.ASTKMALLOC1 ltac:(lia) SmInst.sm_walk_1 (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frame_in AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_33 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.stack_malloc_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok AsanImgx.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_grow_f MP PB AsanAcct.NMAX 2%uint63 eq_refl 4096 AsanW.AFake_sm0.AFake_sm2.ASTKMALLOC2 ltac:(lia) SmInst.sm_walk_2 (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frame_in AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_34 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.FaSound.settle_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_free_f (F1Unp.F1Unp.cw_zc asegs) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA AsanRun.OTHERA_refl (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_35 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.amemcpy_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_ssh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zro AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_gsh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_shmap AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) W_PAT_SUBx (F1Unp.F1Unp.cw_sub_ghost asegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_36 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.aasan_memcpy_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_ssh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zro AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_gsh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_shmap AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_holds_zarg AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_aimg_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) W_PAT_SUBx (F1Unp.F1Unp.cw_sub_ghost asegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_37 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemsetFinal.amemset_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_ssh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) W_PAT_SUBx (F1Unp.F1Unp.cw_sub_ghost asegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_38 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemsetFinal.aasan_memset_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_ssh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) W_PAT_SUBx (F1Unp.F1Unp.cw_sub_ghost asegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_39 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.amemcpy0_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_40 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.aasan_memcpy0_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_41 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.CtrAnnot.annotate_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.F1Unp.cw_vec_unowned asegs) (F1Unp.F1Unp.cw_vecs_distinct asegs) (F1Unp.F1Unp.cw_sub_ghost asegs) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_42 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SinkFinal.asink_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.F1Unp.cw_sub_ghost asegs) W_PAT_SUBx MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_43 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SinkFinal.aasan_sink_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.F1Unp.cw_sub_ghost asegs) W_PAT_SUBx MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_44 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.afree0_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok AsanImgx.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_45 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.CtrTwinOut.twin_out_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_grow (F1Unp.F1Unp.cw_vec_unowned asegs) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA AsanRun.OTHERA_refl (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_46 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkInstB.PkInstB.pkregrowa_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.F1Unp.cw_sub_ghost asegs) W_PATx MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) MemcpySound.ASAN_MEMCPY_SYM MemcpyFinal.memcpy_walk_asan 2224 ltac:(lia) Memcpy0Sound.memcpy0_walk_asan AWAx HOPSx 379908%uint63 eq_refl); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_47 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkInstB.PkInstB.pkbody_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.F1Unp.cw_sub_ghost asegs) W_PATx MP PB AsanAcct.NMAX (Acct.ACCT_rng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_rng_aimg AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_silent AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX) (AsanRun.OPSA_holds_ssh AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.ACCT_rng_stk_sh AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) MemcpySound.ASAN_MEMCPY_SYM MemcpyFinal.memcpy_walk_asan 2224 ltac:(lia) Memcpy0Sound.memcpy0_walk_asan AWAx HOPSx 379908%uint63 eq_refl); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_48 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInstA.PkInstA.pkload2_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_49 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInstA.PkInstA.pkfld2_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_50 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.AsanRun.azpb_shload_sound AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file MP PB (AsanPB.HMPA inp) _); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_51 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.AsanRun.agsh_shload_sound AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file MP PB (AsanPB.HMPA inp) _); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_52 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.RoLit.RoLit.rolit_sound asegs OPSA RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_ASAN asegs) CHSx (AsanRun.OPSA_acc_user_law AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (RoLitInst.OPSA_rolit_HR AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB (AsanPB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_53 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.CaseF.CaseF.casef_sound _ _ asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_54 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.FfSound.fake_free_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_free_f (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.NMAX (Acct.ACCT_frng AsanAcct.NMAX AsanAcct.SHFIX) (Acct.ACCT_frame_out AsanAcct.NMAX AsanAcct.HLIM MP MINV AsanRun.OTHERA (AcctPlug.MP_relx inp) AcctPlug.OTHER_relx MINV_intro AsanAcct.SHFIX Op.is_fake Op.lb_del Op.lb_del_In (fun id Aaddr sz FK => Op.heap_not_fake (HB id Aaddr sz) (ex_intro _ id eq_refl) FK))); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_55 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInstA.PkInstA.opshload_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.HMPA inp) (AsanRun.CHSAx AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_acc_user_lawA AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_shlaw AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_56 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gtvc_carg_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_57 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gviewgc_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_58 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gvechi_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_59 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.CtrTwinIn.twin_in_sound AIu2 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.OPSA_holds1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov1 AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.Cw_ghost_free (F1Unp.F1Unp.cw_vec_unowned asegs) (AsanRun.OPSA_frame_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_fp_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.OTHERA AsanRun.OTHERA_refl (AsanRun.OPSA_mo_other AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_cov0_img AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_60 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gbnda_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_61 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gbnd_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_62 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gnarrow_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_63 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gperm_vec_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_64 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gpotinit_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_65 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.opshloadu_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.HMPA inp) (AsanRun.CHSAx AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_acc_user_lawA AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.OPSA_shlaw AsanImgx.IMGX_A AsanImgx.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_66 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GUnrealign.GUnrealign.gunrealign_sound _ _ asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_67 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gviewdrop_reg_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_68 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gshr_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_69 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gbgnone_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_70 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gchkl_sound asegs OPSA MP PB (AsanPB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_71 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkMidInst.PkMidInst.pkmid_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_72 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gexcl_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_73 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.GTwinBnd.GTwinBnd.gtwinbnd_sound _ asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_74 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gtwinbnd_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_75 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.ganca_sound asegs AsanImgx.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_76 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gpothr_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_77 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.GVEndA.GVEA.gvea3_sound _ _ asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Local Ltac ra_78 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.UnpInstA.gvea3_sound asegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound asegs); vm_compute; reflexivity)]).
Definition ctab_Asan2U := let _USE := (Hva, Hsp, Hfit, Hvl, ACCT_led, ACCT_cov, ACCT_cov_sh, ACCT_mat, AI_frame_top, ACCT_fds) in

  (ltac:(apply (DrvLib.DrvLib.ctab_ok_of_list asegs RAx); repeat (apply Forall_cons || apply Forall_nil); cbn [snd];
    [ first [ ra_0 | fail 1 "registry row cid 38 (tdenter_contract): no census theorem applies" ]
    | first [ ra_1 | fail 1 "registry row cid 39 (znext_contract): no census theorem applies" ]
    | first [ ra_2 | fail 1 "registry row cid 40 (g0a_contract): no census theorem applies" ]
    | first [ ra_3 | fail 1 "registry row cid 41 (g2z_contract): no census theorem applies" ]
    | first [ ra_4 | fail 1 "registry row cid 42 (g2_contract): no census theorem applies" ]
    | first [ ra_5 | fail 1 "registry row cid 43 (g2b_contract): no census theorem applies" ]
    | first [ ra_6 | fail 1 "registry row cid 44 (g3pa_contract): no census theorem applies" ]
    | first [ ra_7 | fail 1 "registry row cid 45 (grooma_contract): no census theorem applies" ]
    | first [ ra_7 | fail 1 "registry row cid 47 (grooma_contract): no census theorem applies" ]
    | first [ ra_7 | fail 1 "registry row cid 48 (grooma_contract): no census theorem applies" ]
    | first [ ra_8 | fail 1 "registry row cid 50 (g3r_contract): no census theorem applies" ]
    | first [ ra_9 | fail 1 "registry row cid 55 (gcap_contract): no census theorem applies" ]
    | first [ ra_9 | fail 1 "registry row cid 56 (gcap_contract): no census theorem applies" ]
    | first [ ra_9 | fail 1 "registry row cid 57 (gcap_contract): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 58 (gnz_contract): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 59 (gnz_contract): no census theorem applies" ]
    | first [ ra_11 | fail 1 "registry row cid 60 (g4a_contract): no census theorem applies" ]
    | first [ ra_11 | fail 1 "registry row cid 61 (g4a_contract): no census theorem applies" ]
    | first [ ra_11 | fail 1 "registry row cid 62 (g4a_contract): no census theorem applies" ]
    | first [ ra_11 | fail 1 "registry row cid 63 (g4a_contract): no census theorem applies" ]
    | first [ ra_11 | fail 1 "registry row cid 64 (g4a_contract): no census theorem applies" ]
    | first [ ra_12 | fail 1 "registry row cid 68 (gsplit_contract): no census theorem applies" ]
    | first [ ra_12 | fail 1 "registry row cid 69 (gsplit_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 70 (g1a_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 71 (g1a_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 72 (g1a_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 73 (g1a_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 74 (g1a_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 75 (g1a_contract): no census theorem applies" ]
    | first [ ra_14 | fail 1 "registry row cid 80 (g6r_contract): no census theorem applies" ]
    | first [ ra_14 | fail 1 "registry row cid 81 (g6r_contract): no census theorem applies" ]
    | first [ ra_15 | fail 1 "registry row cid 82 (roome_contract_a): no census theorem applies" ]
    | first [ ra_16 | fail 1 "registry row cid 83 (push_contract_a): no census theorem applies" ]
    | first [ ra_17 | fail 1 "registry row cid 84 (next_contract): no census theorem applies" ]
    | first [ ra_18 | fail 1 "registry row cid 85 (pop_contract_a): no census theorem applies" ]
    | first [ ra_19 | fail 1 "registry row cid 86 (push0_contract): no census theorem applies" ]
    | first [ ra_20 | fail 1 "registry row cid 87 (pkenter_contract): no census theorem applies" ]
    | first [ ra_21 | fail 1 "registry row cid 88 (pkexit_contract): no census theorem applies" ]
    | first [ ra_21 | fail 1 "registry row cid 89 (pkexit_contract): no census theorem applies" ]
    | first [ ra_22 | fail 1 "registry row cid 92 (peek_contract): no census theorem applies" ]
    | first [ ra_23 | fail 1 "registry row cid 94 (pkextb_c): no census theorem applies" ]
    | first [ ra_24 | fail 1 "registry row cid 95 (pkcap_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 100 (gname_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 101 (gname_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 102 (gname_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 103 (gname_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 104 (gname_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 105 (gname_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 107 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 108 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 109 (ginva_contract): no census theorem applies" ]
    | first [ ra_27 | fail 1 "registry row cid 110 (pkinv_contract): no census theorem applies" ]
    | first [ ra_27 | fail 1 "registry row cid 111 (pkinv_contract): no census theorem applies" ]
    | first [ ra_28 | fail 1 "registry row cid 400 (amalloc_c): no census theorem applies" ]
    | first [ ra_29 | fail 1 "registry row cid 401 (afree_c): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 402 (arealloc_c): no census theorem applies" ]
    | first [ ra_31 | fail 1 "registry row cid 404 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_32 | fail 1 "registry row cid 405 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_33 | fail 1 "registry row cid 406 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_34 | fail 1 "registry row cid 408 (settle_c): no census theorem applies" ]
    | first [ ra_35 | ra_36 | fail 1 "registry row cid 411 (amemcpy_c): no census theorem applies" ]
    | first [ ra_37 | ra_38 | fail 1 "registry row cid 413 (amemset_c): no census theorem applies" ]
    | first [ ra_39 | ra_40 | fail 1 "registry row cid 415 (amemcpy0_c): no census theorem applies" ]
    | first [ ra_41 | fail 1 "registry row cid 419 (annotate_c): no census theorem applies" ]
    | first [ ra_42 | ra_43 | fail 1 "registry row cid 431 (asink_c): no census theorem applies" ]
    | first [ ra_44 | fail 1 "registry row cid 436 (afree0_c): no census theorem applies" ]
    | first [ ra_45 | fail 1 "registry row cid 441 (twin_out_c): no census theorem applies" ]
    | first [ ra_46 | fail 1 "registry row cid 477 (pkregrow_contract): no census theorem applies" ]
    | first [ ra_47 | fail 1 "registry row cid 479 (pkbody_c): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 610648 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 610828 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 610832 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 610888 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 610936 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 610972 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611044 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611052 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611156 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611212 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611220 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611276 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611284 (pkload2_contract): no census theorem applies" ]
    | first [ ra_49 | fail 1 "registry row cid 611348 (pkfld2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611492 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611564 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611572 (pkload2_contract): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 611644 (pkload2_contract): no census theorem applies" ]
    | first [ ra_50 | ra_51 | fail 1 "registry row cid 439586" "568 (shloadlit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442577" "328 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442577" "332 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442579" "552 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442579" "556 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581" "260 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581" "264 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581" "604 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581" "608 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "120 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "124 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "280 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "284 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "440 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "444 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "956 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582" "960 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583" "124 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583" "128 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583" "300 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583" "304 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "188 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "192 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "532 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "536 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "808 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "812 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "968 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584" "972 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585" "116 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585" "120 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585" "400 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585" "404 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585" "616 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585" "620 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595" "204 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595" "208 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595" "564 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595" "568 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442596" "664 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442596" "668 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442597" "388 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442597" "392 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442598" "224 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442598" "228 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442599" "352 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442599" "356 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442600" "460 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442600" "464 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442601" "296 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442601" "300 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602" "112 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602" "116 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602" "952 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602" "956 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442603" "764 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442603" "768 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442604" "804 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442604" "808 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606" "036 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606" "040 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606" "572 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606" "576 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607" "328 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607" "332 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607" "532 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607" "536 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609" "104 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609" "108 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609" "420 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609" "424 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609" "428 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609" "432 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610" "160 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610" "164 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610" "168 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610" "172 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612" "792 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612" "796 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612" "800 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612" "804 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613" "360 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613" "364 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613" "368 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613" "372 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614" "336 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614" "340 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614" "344 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614" "348 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615" "148 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615" "152 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615" "416 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615" "420 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615" "424 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615" "428 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616" "192 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616" "196 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616" "200 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616" "204 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617" "000 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617" "004 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617" "388 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617" "392 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617" "664 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617" "668 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618" "000 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618" "004 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618" "008 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618" "012 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619" "080 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619" "084 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619" "088 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619" "092 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620" "716 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620" "720 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620" "724 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620" "728 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "004 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "008 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "468 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "472 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "644 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "648 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "836 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622" "840 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "192 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "196 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "532 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "536 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "692 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "696 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "892 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623" "896 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442624" "460 (rolit_c): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 444386" "028 (casef_contract): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453577" "012 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453578" "516 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453580" "568 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453609" "780 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453612" "220 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453613" "160 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453614" "052 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453614" "944 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453615" "972 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453616" "748 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453618" "824 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453620" "372 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453621" "740 (fake_free_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454579" "596 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610" "492 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610" "628 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610" "800 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610" "820 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610" "868 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610" "916 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610" "964 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "020 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "040 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "112 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "148 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "188 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "208 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "252 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "272 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "320 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "484 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "540 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "560 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611" "636 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454615" "188 (opshload_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455596" "812 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455597" "540 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455600" "644 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455601" "504 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455602" "300 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455603" "164 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455603" "844 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455606" "652 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455611" "648 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455611" "684 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455622" "084 (gtvc_carg): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456577" "128 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456580" "336 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456596" "812 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456597" "540 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456600" "644 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456601" "504 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456602" "300 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456603" "164 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456604" "116 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456611" "648 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456738" "876 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457596" "812 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457597" "540 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457600" "644 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457601" "504 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457602" "300 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457603" "164 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457611" "648 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457611" "684 (gvechi_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458585" "552 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458596" "140 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458598" "804 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458599" "928 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458605" "308 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458608" "028 (twin_in_c): no census theorem applies" ]
    | first [ ra_60 | ra_61 | fail 1 "registry row cid 460586" "380 (gbnd_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461596" "812 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461597" "540 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461600" "644 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461601" "504 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461602" "300 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461603" "164 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463580" "336 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463585" "832 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463603" "844 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463738" "876 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_64 | fail 1 "registry row cid 464585" "552 (gpotinit_contract): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465585" "968 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586" "000 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586" "152 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586" "184 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586" "996 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587" "032 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587" "240 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587" "288 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587" "680 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587" "720 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587" "924 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587" "952 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588" "356 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588" "564 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588" "788 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588" "832 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589" "512 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589" "552 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589" "780 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589" "808 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590" "068 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590" "096 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590" "260 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590" "292 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591" "044 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591" "068 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591" "192 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591" "216 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591" "340 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465595" "676 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596" "056 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596" "080 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596" "168 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596" "192 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "336 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "832 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "856 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465599" "464 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465599" "956 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465599" "980 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465604" "964 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465604" "992 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465605" "320 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465606" "124 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465606" "312 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465607" "692 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465607" "720 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465608" "040 (opshloadu_c): no census theorem applies" ]
    | first [ ra_66 | fail 1 "registry row cid 466577" "128 (gunrealign_contract): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468580" "336 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468582" "520 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468596" "812 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468596" "972 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468597" "540 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468597" "700 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468600" "644 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468600" "836 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468601" "504 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468601" "664 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468602" "300 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468602" "492 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468603" "164 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468603" "324 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468603" "844 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468606" "116 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468606" "652 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469596" "812 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469597" "540 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469600" "644 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469601" "504 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469602" "300 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469603" "164 (gvechi_contract): no census theorem applies" ]
    | first [ ra_67 | fail 1 "registry row cid 471394" "828 (gviewdrop_reg_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472394" "828 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472596" "812 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472597" "540 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472600" "644 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472601" "504 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472602" "300 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472603" "164 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472604" "116 (ginva_contract): no census theorem applies" ]
    | first [ ra_68 | fail 1 "registry row cid 473583" "108 (gshr_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478379" "860 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478577" "396 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478617" "788 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 482604" "844 (gnz_contract): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 482607" "572 (gnz_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485585" "860 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586" "456 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586" "608 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586" "828 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586" "852 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587" "100 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587" "124 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587" "512 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587" "536 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587" "580 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587" "788 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587" "808 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588" "100 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588" "120 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588" "224 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588" "244 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588" "632 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588" "656 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588" "676 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "056 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "076 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "196 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "216 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "320 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "376 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "396 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "620 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "640 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "908 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589" "928 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590" "164 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590" "392 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590" "412 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590" "536 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590" "556 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485596" "680 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485597" "404 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485600" "476 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485600" "500 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485601" "312 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485601" "336 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602" "128 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602" "152 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602" "968 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602" "992 (gchkl_contract): no census theorem applies" ]
    | first [ ra_71 | fail 1 "registry row cid 486394" "828 (pkmid_contract): no census theorem applies" ]
    | first [ ra_72 | fail 1 "registry row cid 487606" "536 (gexcl_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488582" "520 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488596" "812 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488596" "972 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488597" "540 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488597" "700 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488600" "644 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488600" "836 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488601" "504 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488601" "664 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488602" "300 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488602" "492 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488603" "164 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488603" "324 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488604" "124 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488604" "208 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488606" "116 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488606" "652 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488738" "876 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489596" "812 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489597" "540 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489600" "644 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489601" "504 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489602" "300 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489603" "164 (ganca_contract): no census theorem applies" ]
    | first [ ra_76 | fail 1 "registry row cid 494580" "336 (gpothr_contract): no census theorem applies" ]
    | first [ ra_76 | fail 1 "registry row cid 494738" "876 (gpothr_contract): no census theorem applies" ]
    | first [ ra_77 | ra_78 | fail 1 "registry row cid 496738" "876 (gvea3_contract): no census theorem applies" ] ]) : DrvLib.DrvLib.ctab_ok asegs RAx T_Asan2U.CONTRACTS).
End Reg.
