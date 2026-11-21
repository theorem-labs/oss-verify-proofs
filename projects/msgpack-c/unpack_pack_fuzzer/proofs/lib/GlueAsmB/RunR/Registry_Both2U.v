(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; a copy of GlueAsmB/Run/Registry_Both2U.v for the start state with CONFIG_RSEQ (its certificates' paths renamed to the CONFIG_RSEQ copies; each failure message that held a run of 7 or more hex digits written as pieces that hold none, the same text). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto ABase AMalloc_iface AInstanceM AInstanceU AMalloc_iface2 AInstanceU2. Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB AMalloc_iface2.TwinB AInstanceU2.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op. Import Ledger.TwinB Op.TwinB.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RoLitA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GViewDrop2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GUnrealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GBgNone.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GFmv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkMid.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkLoad2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkFld2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpShLoad.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Ops GLib GUnp GWin G2 G2Z G2B G3 G3P G4 GRoom G1 G0 G6 GCap GNz GShr GCur GBnd VDestroy GSplit GName GVEnd GInv TdEnter Td PkOps PkEnter PkExit PkStack PkPeek PkFld PkBody PkRegrow PkCap PkInv G0A G1A G3PA G4A G6A GInvA GWinA GBndA GMid GNarrow GNameA GPerm GTwinViewC GVecHi GViewDrop2 GSeal GPotHR Pot GPot GPotInit GPotName OpShLoadU GGran GGranP GChk GBgNone GExcl GRoomA GAncA GCnt GCurA PkShrink.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2UR Require T_Both2U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St HeapOp.
Open Scope Z_scope.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Local Notation AIu_fake := (FakeLaw.TwinB.AIu_fake ExhFirst.TwinB.exh_first).
Section Reg.
Context {rc : runConstT}.

Variable inp : ProcInput.
Variables (sp : word) (rnd : EntryDraw).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Let p1 : list byte := AsanDrun.TwinB.p1 inp.
Let file : list byte := AsanDrun.TwinB.file inp.
Let MP : Model -> Prop := AsanDrun.TwinB.MP inp.
Let PB : (int -> list byte) -> Prop := AsanDrun.TwinB.PB inp sp rnd.
Let ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop := Acct.TwinB.ACCT AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX.
Let COVP : Model -> word -> Prop := Acct.TwinB.COVPb AsanAcct.TwinB.SHFIX.
Let NMAX : nat := AsanAcct.TwinB.NMAX.
Let ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p) := AcctPlug.TwinB.ACCT_ledx.
Let ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z) := AcctPlug.TwinB.ACCT_covx.
Let ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z) := AcctPlug.TwinB.ACCT_cov_shx.
Let ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo' := AcctPlug.TwinB.ACCT_matx.
Let UNIV : list (list Z) := UnivBoth.UNIV.
Let AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono bsegs m m' -> AHEAP AIu2 L RNG st LB m' := AcctPlug.TwinB.AI_frame_topx.
Let Cw : client_world := Ops.UO.unp_cw bsegs (ClientX.CX.XTP bsegs).
Let ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo) := AcctPlug.TwinB.ACCT_fdsx.
Let OPSA : optable := AsanRun.TwinB.OPSA AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.
Let MINV : Model -> Prop := op_minv OPSA.
Let MINV_intro : forall mo, m_halted mo = None -> Acct.TwinB.lazy_shapeA Acct.TwinB.C0A mo -> MINV mo := AcctPlug.TwinB.MINV_introx.
Let AWAx := AWA AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake.
Let HOPSx := (AsanRun.TwinB.OPSA_heap_ops AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file AsanImgx.TwinB.IMGX_A_stage AsanImgx.TwinB.IMGX_A_cov AsanImgx.TwinB.IMGX_A_shlit AsanImgx.TwinB.IMGX_A_stksh).
Let W_PAT_SUBx := F1Cw.TwinB.W_PAT_SUB_A ACCT UNIV.
Let W_PATx := (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.WPat.TwinB.w_pat_ok AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake W_PAT_SUBx).
Let CHSx := GLib.UG.chg_user bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA.
Let RAx : DrvLib.DrvLib.drun := AsanDrun.TwinB.RA AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw ACCT_fds AsanImgx.TwinB.IMGX_A_rs3 inp sp rnd Hva.
Local Ltac ra_0 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.TdInst.TdInst.tdenter_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_1 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.TdInst.TdInst.znext_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_2 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.g0a_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_3 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g2z_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_4 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g2_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_5 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g2b_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_6 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.g3pa_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_7 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.grooma_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_8 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.g3r_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_9 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gcura_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_10 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gcur_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_11 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gbnda_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_12 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gbnd_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_13 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gcap_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_14 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gnz_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_15 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.g4a_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_16 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gsplit_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_17 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.g1a_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_18 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.G6RegrowInst.TwinB.G6RegrowInst.g6regrow_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV (ClientX.CX.XTP bsegs) OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs) W_PATx MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) MemcpySound.TwinB.ASAN_MEMCPY_SYM MemcpyFinal.TwinB.memcpy_walk_asan 382356%uint63 eq_refl AWAx HOPSx _); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_19 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.roome_a_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_20 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.push_a_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_21 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.next_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_22 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pop_a_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_23 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.push0_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_24 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkenter_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_25 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkexit_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_26 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.peek_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.TwinB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_27 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkInstB.TwinB.PkInstB.pkextb_sound AsanImgx.TwinB.IMGX_A OPSA MP PB AWAx HOPSx (AsanPB.TwinB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_28 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkcap_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_29 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gname_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_30 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.ginva_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_31 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.PkInst.pkinv_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_32 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.TwinB.amalloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (FakeLaw.TwinB.AIu_errno ExhFirst.TwinB.exh_first) (Acct.TwinB.ACCT_malloc AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_33 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.TwinB.afree_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_free (F1Unp.TwinB.F1Unp.cw_vec_unowned bsegs) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_free AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_34 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.TwinB.arealloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow F1Cw.TwinB.Cw_ghost_free (F1Unp.TwinB.F1Unp.cw_vec_unowned bsegs) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (FakeLaw.TwinB.AIu_errno ExhFirst.TwinB.exh_first) (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (FakeLaw.TwinB.AIu_realloc ExhFirst.TwinB.exh_first) (Acct.TwinB.ACCT_realloc AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_35 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.TwinB.stack_malloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow_f MP PB AsanAcct.TwinB.NMAX 0%uint63 eq_refl 16384 AsanW.AFake_sm0.TwinB.AFake_sm0.ASTKMALLOC0 ltac:(lia) SmInst.TwinB.sm_walk_0 (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frame_in AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_36 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.TwinB.stack_malloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow_f MP PB AsanAcct.TwinB.NMAX 1%uint63 eq_refl 8192 AsanW.AFake_sm0.TwinB.AFake_sm1g.ASTKMALLOC1 ltac:(lia) SmInst.TwinB.sm_walk_1 (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frame_in AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_37 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.TwinB.stack_malloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow_f MP PB AsanAcct.TwinB.NMAX 2%uint63 eq_refl 4096 AsanW.AFake_sm0.TwinB.AFake_sm2.ASTKMALLOC2 ltac:(lia) SmInst.TwinB.sm_walk_2 (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frame_in AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_38 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.FaSound.TwinB.settle_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_free_f (F1Unp.TwinB.F1Unp.cw_zc bsegs) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA AsanRun.TwinB.OTHERA_refl (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_39 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.TwinB.amemcpy_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zro AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_gsh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_shmap AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zarg AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_aimg_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_40 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.TwinB.aasan_memcpy_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zro AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_gsh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_shmap AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zarg AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_aimg_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_41 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemsetFinal.TwinB.amemset_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_42 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemsetFinal.TwinB.aasan_memset_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_43 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.TwinB.amemcpy0_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_44 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.TwinB.aasan_memcpy0_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_45 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.CtrAnnot.TwinB.annotate_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.TwinB.F1Unp.cw_vec_unowned bsegs) (F1Unp.TwinB.F1Unp.cw_vecs_distinct bsegs) (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_46 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SinkFinal.TwinB.asink_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs) W_PAT_SUBx MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_47 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SinkFinal.TwinB.aasan_sink_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs) W_PAT_SUBx MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_48 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.TwinB.afree0_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_49 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.CtrTwinOut.TwinB.twin_out_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow (F1Unp.TwinB.F1Unp.cw_vec_unowned bsegs) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA AsanRun.TwinB.OTHERA_refl (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_50 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkInstB.TwinB.PkInstB.pkregrowa_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs) W_PATx MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) MemcpySound.TwinB.ASAN_MEMCPY_SYM MemcpyFinal.TwinB.memcpy_walk_asan 2224 ltac:(lia) Memcpy0Sound.TwinB.memcpy0_walk_asan AWAx HOPSx 382356%uint63 eq_refl); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_51 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkInstB.TwinB.PkInstB.pkbody_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs) W_PATx MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) MemcpySound.TwinB.ASAN_MEMCPY_SYM MemcpyFinal.TwinB.memcpy_walk_asan 2224 ltac:(lia) Memcpy0Sound.TwinB.memcpy0_walk_asan AWAx HOPSx 382356%uint63 eq_refl); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_52 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInstA.PkInstA.pkfld2_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.TwinB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_53 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInstA.PkInstA.pkload2_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.TwinB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_54 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.RoLit.RoLit.rolit_sound bsegs OPSA RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH bsegs) CHSx (AsanRun.TwinB.OPSA_acc_user_law AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (RoLitInst.TwinB.OPSA_rolit_HR AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB (AsanPB.TwinB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_55 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.CaseF.CaseF.casef_sound _ _ bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_56 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.FfSound.TwinB.fake_free_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_free_f (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frame_out AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX Op.TwinB.is_fake Op.TwinB.lb_del Op.TwinB.lb_del_In (fun id Aaddr sz FK => Op.TwinB.heap_not_fake (HB id Aaddr sz) (ex_intro _ id eq_refl) FK))); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_57 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInstA.PkInstA.opshload_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.TwinB.HMPA inp) (AsanRun.TwinB.CHSAx AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_acc_user_lawA AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_shlaw AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_58 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gtvc_carg_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_59 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gviewgc_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_60 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gvechi_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_61 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.CtrTwinIn.TwinB.twin_in_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_free (F1Unp.TwinB.F1Unp.cw_vec_unowned bsegs) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA AsanRun.TwinB.OTHERA_refl (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_62 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gnarrow_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_63 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gperm_vec_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_64 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gpotinit_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_65 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.opshloadu_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB (AsanPB.TwinB.HMPA inp) (AsanRun.TwinB.CHSAx AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_acc_user_lawA AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_shlaw AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_66 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GUnrealign.GUnrealign.gunrealign_sound _ _ bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_67 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gviewdrop_reg_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_68 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst.UnpInst.gshr_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_69 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gbgnone_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_70 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gchkl_sound bsegs OPSA MP PB (AsanPB.TwinB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_71 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gexcl_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_72 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.GTwinBnd.TwinB.GTwinBnd.gtwinbnd_sound _ bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_73 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gtwinbnd_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_74 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.ganca_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_75 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gcnt_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_76 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gfmv_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_77 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA.PkShrinkInst.TwinB.PkShrinkInst.pkshrink_sound bsegs AsanImgx.TwinB.IMGX_A AWAx OPSA HOPSx MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_78 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gpothr_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_79 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.GVEndA.TwinB.GVEA.gvea3_sound _ _ bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_80 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA.UnpInstA.TwinB.UnpInstA.gvea3_sound bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Definition ctab_Both2U := let _USE := (Hva, Hsp, Hfit, Hvl, ACCT_led, ACCT_cov, ACCT_cov_sh, ACCT_mat, AI_frame_top, ACCT_fds) in

  (ltac:(apply (DrvLib.DrvLib.ctab_ok_of_list bsegs RAx); repeat (apply Forall_cons || apply Forall_nil); cbn [snd];
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
    | first [ ra_9 | ra_10 | fail 1 "registry row cid 53 (gcur_contract): no census theorem applies" ]
    | first [ ra_11 | ra_12 | fail 1 "registry row cid 54 (gbnd_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 55 (gcap_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 56 (gcap_contract): no census theorem applies" ]
    | first [ ra_13 | fail 1 "registry row cid 57 (gcap_contract): no census theorem applies" ]
    | first [ ra_14 | fail 1 "registry row cid 58 (gnz_contract): no census theorem applies" ]
    | first [ ra_14 | fail 1 "registry row cid 59 (gnz_contract): no census theorem applies" ]
    | first [ ra_15 | fail 1 "registry row cid 60 (g4a_contract): no census theorem applies" ]
    | first [ ra_16 | fail 1 "registry row cid 68 (gsplit_contract): no census theorem applies" ]
    | first [ ra_16 | fail 1 "registry row cid 69 (gsplit_contract): no census theorem applies" ]
    | first [ ra_17 | fail 1 "registry row cid 70 (g1a_contract): no census theorem applies" ]
    | first [ ra_17 | fail 1 "registry row cid 71 (g1a_contract): no census theorem applies" ]
    | first [ ra_17 | fail 1 "registry row cid 72 (g1a_contract): no census theorem applies" ]
    | first [ ra_17 | fail 1 "registry row cid 73 (g1a_contract): no census theorem applies" ]
    | first [ ra_17 | fail 1 "registry row cid 74 (g1a_contract): no census theorem applies" ]
    | first [ ra_17 | fail 1 "registry row cid 75 (g1a_contract): no census theorem applies" ]
    | first [ ra_18 | fail 1 "registry row cid 80 (g6r_contract): no census theorem applies" ]
    | first [ ra_18 | fail 1 "registry row cid 81 (g6r_contract): no census theorem applies" ]
    | first [ ra_19 | fail 1 "registry row cid 82 (roome_contract_a): no census theorem applies" ]
    | first [ ra_20 | fail 1 "registry row cid 83 (push_contract_a): no census theorem applies" ]
    | first [ ra_21 | fail 1 "registry row cid 84 (next_contract): no census theorem applies" ]
    | first [ ra_22 | fail 1 "registry row cid 85 (pop_contract_a): no census theorem applies" ]
    | first [ ra_23 | fail 1 "registry row cid 86 (push0_contract): no census theorem applies" ]
    | first [ ra_24 | fail 1 "registry row cid 87 (pkenter_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 88 (pkexit_contract): no census theorem applies" ]
    | first [ ra_25 | fail 1 "registry row cid 89 (pkexit_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 92 (peek_contract): no census theorem applies" ]
    | first [ ra_27 | fail 1 "registry row cid 94 (pkextb_c): no census theorem applies" ]
    | first [ ra_28 | fail 1 "registry row cid 95 (pkcap_contract): no census theorem applies" ]
    | first [ ra_29 | fail 1 "registry row cid 100 (gname_contract): no census theorem applies" ]
    | first [ ra_29 | fail 1 "registry row cid 101 (gname_contract): no census theorem applies" ]
    | first [ ra_29 | fail 1 "registry row cid 102 (gname_contract): no census theorem applies" ]
    | first [ ra_29 | fail 1 "registry row cid 103 (gname_contract): no census theorem applies" ]
    | first [ ra_29 | fail 1 "registry row cid 104 (gname_contract): no census theorem applies" ]
    | first [ ra_29 | fail 1 "registry row cid 105 (gname_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 107 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 108 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 109 (ginva_contract): no census theorem applies" ]
    | first [ ra_31 | fail 1 "registry row cid 110 (pkinv_contract): no census theorem applies" ]
    | first [ ra_31 | fail 1 "registry row cid 111 (pkinv_contract): no census theorem applies" ]
    | first [ ra_32 | fail 1 "registry row cid 400 (amalloc_c): no census theorem applies" ]
    | first [ ra_33 | fail 1 "registry row cid 401 (afree_c): no census theorem applies" ]
    | first [ ra_34 | fail 1 "registry row cid 402 (arealloc_c): no census theorem applies" ]
    | first [ ra_35 | fail 1 "registry row cid 404 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_36 | fail 1 "registry row cid 405 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_37 | fail 1 "registry row cid 406 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_38 | fail 1 "registry row cid 408 (settle_c): no census theorem applies" ]
    | first [ ra_39 | ra_40 | fail 1 "registry row cid 411 (amemcpy_c): no census theorem applies" ]
    | first [ ra_41 | ra_42 | fail 1 "registry row cid 413 (amemset_c): no census theorem applies" ]
    | first [ ra_43 | ra_44 | fail 1 "registry row cid 415 (amemcpy0_c): no census theorem applies" ]
    | first [ ra_45 | fail 1 "registry row cid 419 (annotate_c): no census theorem applies" ]
    | first [ ra_46 | ra_47 | fail 1 "registry row cid 431 (asink_c): no census theorem applies" ]
    | first [ ra_48 | fail 1 "registry row cid 436 (afree0_c): no census theorem applies" ]
    | first [ ra_49 | fail 1 "registry row cid 441 (twin_out_c): no census theorem applies" ]
    | first [ ra_50 | fail 1 "registry row cid 477 (pkregrow_contract): no census theorem applies" ]
    | first [ ra_51 | fail 1 "registry row cid 479 (pkbody_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 614964 (pkfld2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615024 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615028 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615100 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615164 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615228 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615300 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615308 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615416 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615480 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615488 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615544 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615552 (pkload2_contract): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 615592 (pkfld2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615864 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615936 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 615944 (pkload2_contract): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 616020 (pkload2_contract): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442579" "816 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442579" "820 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442582" "192 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442582" "196 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442583" "868 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442583" "872 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442584" "100 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442584" "104 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442584" "480 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442584" "484 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442584" "976 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442584" "980 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442585" "584 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442585" "588 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442585" "772 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442585" "776 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442585" "956 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442585" "960 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "096 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "100 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "324 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "328 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "708 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "712 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "940 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442586" "944 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442587" "124 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442587" "128 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442587" "316 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442587" "320 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442587" "592 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442587" "596 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442588" "344 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442588" "348 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442588" "724 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442588" "728 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "220 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "224 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "548 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "552 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "736 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "740 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "920 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442589" "924 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "064 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "068 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "340 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "344 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "488 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "492 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "748 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "752 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "756 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442590" "760 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442597" "584 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442597" "588 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442597" "800 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442597" "804 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442598" "148 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442598" "152 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442598" "380 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442598" "384 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442599" "204 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442599" "208 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442599" "896 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442599" "900 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442600" "548 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442600" "552 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442600" "748 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442600" "752 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442601" "016 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442601" "020 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442601" "212 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442601" "216 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442601" "436 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442601" "440 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442602" "260 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442602" "264 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442603" "084 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442603" "088 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442603" "840 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442603" "844 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442604" "620 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442604" "624 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442605" "380 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442605" "384 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442606" "168 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442606" "172 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "088 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "092 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "240 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "244 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "392 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "396 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "544 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "548 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "692 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "696 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "972 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442607" "976 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442608" "620 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442608" "624 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442608" "732 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442608" "736 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442608" "908 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442608" "912 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442609" "720 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442609" "724 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442609" "992 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442609" "996 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442610" "220 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442610" "224 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442610" "616 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442610" "620 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442610" "800 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442610" "804 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442611" "152 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442611" "156 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442611" "660 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442611" "664 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442611" "892 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442611" "896 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442612" "072 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442612" "076 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442612" "184 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442612" "188 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442612" "360 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442612" "364 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442613" "624 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442613" "628 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442613" "748 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442613" "752 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442614" "052 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442614" "056 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442614" "060 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442614" "064 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442614" "768 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442614" "772 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442616" "632 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442616" "636 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442616" "640 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442616" "644 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "132 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "136 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "140 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "144 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "736 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "740 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "744 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442617" "748 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442618" "296 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442618" "300 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442618" "304 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442618" "308 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442618" "848 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442618" "852 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "072 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "076 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "292 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "296 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "564 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "568 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "844 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442619" "848 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442620" "296 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442620" "300 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442620" "568 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442620" "572 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442620" "884 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442620" "888 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442621" "240 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442621" "244 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442621" "248 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442621" "252 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442622" "408 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442622" "412 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442622" "416 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442622" "420 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442624" "196 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442624" "200 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442624" "204 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442624" "208 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "132 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "136 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "140 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "144 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "956 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "960 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "964 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442625" "968 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442627" "472 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442627" "476 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442627" "480 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442627" "484 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442628" "220 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442628" "224 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442628" "408 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442628" "412 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442628" "776 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442628" "780 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "020 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "024 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "216 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "220 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "352 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "356 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "572 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "576 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "984 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442629" "988 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442630" "488 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442630" "492 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442630" "860 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442630" "864 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442631" "048 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442631" "052 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442631" "300 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442631" "304 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442631" "308 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442631" "312 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442632" "088 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442632" "092 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442632" "264 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442632" "268 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442632" "540 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442632" "544 (rolit_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 442632" "976 (rolit_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 444388" "516 (casef_contract): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453579" "500 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453581" "096 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453583" "232 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453596" "316 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453614" "412 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453616" "956 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453617" "548 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453618" "108 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453618" "700 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453622" "148 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453623" "856 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453624" "892 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453625" "732 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453627" "164 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453628" "060 (fake_free_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 453631" "888 (fake_free_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454582" "244 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454614" "880 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454614" "956 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454614" "996 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "016 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "092 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "156 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "220 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "276 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "296 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "372 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "408 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "456 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "476 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "520 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "540 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "584 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "856 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "912 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454615" "932 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454616" "012 (opshload_c): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 454619" "352 (opshload_c): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455599" "324 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455600" "020 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455603" "244 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455604" "024 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455604" "784 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455605" "568 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455606" "248 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455610" "868 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455615" "648 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455616" "024 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 455628" "308 (gtvc_carg): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456579" "616 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456582" "988 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456599" "324 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456600" "020 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456603" "244 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456604" "024 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456604" "784 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456605" "568 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456607" "640 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456616" "024 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 456747" "392 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457599" "324 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457600" "020 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457603" "244 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457604" "024 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457604" "784 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457605" "568 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457615" "648 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 457616" "024 (gvechi_contract): no census theorem applies" ]
    | first [ ra_61 | fail 1 "registry row cid 458590" "656 (twin_in_c): no census theorem applies" ]
    | first [ ra_61 | fail 1 "registry row cid 458608" "336 (twin_in_c): no census theorem applies" ]
    | first [ ra_11 | ra_12 | fail 1 "registry row cid 460592" "392 (gbnd_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461599" "324 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461600" "020 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461603" "244 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461604" "024 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461604" "784 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461605" "568 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463582" "988 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463591" "296 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463606" "248 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463747" "392 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_64 | fail 1 "registry row cid 464590" "656 (gpotinit_contract): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465597" "676 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465597" "704 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "240 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "276 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "520 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "760 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "784 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "812 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598" "836 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465600" "640 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465600" "668 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465600" "840 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465601" "108 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465601" "136 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465601" "304 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465601" "332 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465601" "576 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465601" "820 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465601" "844 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465602" "400 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465602" "640 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465602" "664 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465609" "096 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465609" "124 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465609" "216 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465610" "084 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465610" "396 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465612" "548 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465612" "576 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465612" "668 (opshloadu_c): no census theorem applies" ]
    | first [ ra_66 | fail 1 "registry row cid 466579" "616 (gunrealign_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468582" "988 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468586" "164 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468599" "324 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468600" "020 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468603" "244 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468604" "024 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468604" "784 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468605" "568 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468606" "248 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468608" "852 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468610" "060 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468610" "868 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 468612" "304 (gtvc_carg): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 469599" "324 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 469600" "020 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 469603" "244 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 469604" "024 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 469604" "784 (gvechi_contract): no census theorem applies" ]
    | first [ ra_60 | fail 1 "registry row cid 469605" "568 (gvechi_contract): no census theorem applies" ]
    | first [ ra_67 | fail 1 "registry row cid 471397" "316 (gviewdrop_reg_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472397" "316 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472599" "324 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472600" "020 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472603" "244 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472604" "024 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472604" "784 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472605" "568 (ginva_contract): no census theorem applies" ]
    | first [ ra_30 | fail 1 "registry row cid 472607" "640 (ginva_contract): no census theorem applies" ]
    | first [ ra_68 | fail 1 "registry row cid 473587" "108 (gshr_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478382" "348 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478579" "884 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478621" "008 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_14 | fail 1 "registry row cid 482608" "948 (gnz_contract): no census theorem applies" ]
    | first [ ra_14 | fail 1 "registry row cid 482612" "400 (gnz_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485591" "332 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485591" "712 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485592" "504 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485592" "648 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485592" "668 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485592" "808 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485592" "828 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "036 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "056 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "136 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "160 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "180 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "332 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "352 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "504 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "524 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "736 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "792 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485593" "812 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "056 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "076 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "220 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "240 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "340 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "384 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "404 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "492 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "512 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "696 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "716 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "860 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "928 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485594" "948 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485595" "080 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485595" "100 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485599" "220 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485599" "912 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485603" "100 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485603" "124 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485603" "856 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485603" "880 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485604" "636 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485604" "660 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485605" "396 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485605" "420 (gchkl_contract): no census theorem applies" ]
    | first [ ra_71 | fail 1 "registry row cid 487610" "592 (gexcl_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488586" "164 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488599" "324 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488600" "020 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488603" "244 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488604" "024 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488604" "784 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488605" "568 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488606" "408 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488606" "552 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488606" "616 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488608" "852 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488610" "060 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488610" "868 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488612" "304 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_72 | ra_73 | fail 1 "registry row cid 488747" "392 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_74 | fail 1 "registry row cid 489599" "324 (ganca_contract): no census theorem applies" ]
    | first [ ra_74 | fail 1 "registry row cid 489600" "020 (ganca_contract): no census theorem applies" ]
    | first [ ra_74 | fail 1 "registry row cid 489603" "244 (ganca_contract): no census theorem applies" ]
    | first [ ra_74 | fail 1 "registry row cid 489604" "024 (ganca_contract): no census theorem applies" ]
    | first [ ra_74 | fail 1 "registry row cid 489604" "784 (ganca_contract): no census theorem applies" ]
    | first [ ra_74 | fail 1 "registry row cid 489605" "568 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 490585" "864 (gcnt_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 490587" "176 (gcnt_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 490589" "828 (gcnt_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 490590" "540 (gcnt_contract): no census theorem applies" ]
    | first [ ra_76 | fail 1 "registry row cid 491617" "724 (gfmv_contract): no census theorem applies" ]
    | first [ ra_76 | fail 1 "registry row cid 491618" "284 (gfmv_contract): no census theorem applies" ]
    | first [ ra_77 | fail 1 "registry row cid 492629" "408 (pkshrink_contract): no census theorem applies" ]
    | first [ ra_78 | fail 1 "registry row cid 494582" "988 (gpothr_contract): no census theorem applies" ]
    | first [ ra_78 | fail 1 "registry row cid 494747" "392 (gpothr_contract): no census theorem applies" ]
    | first [ ra_79 | ra_80 | fail 1 "registry row cid 496747" "392 (gvea3_contract): no census theorem applies" ] ]) : DrvLib.DrvLib.ctab_ok bsegs RAx T_Both2U.CONTRACTS).
End Reg.
