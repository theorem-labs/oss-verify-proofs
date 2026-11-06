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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2U Require T_Asan2U.
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
Definition ctab_Asan2U := let _USE := (Hva, Hsp, Hfit, ACCT_led, ACCT_cov, ACCT_cov_sh, ACCT_mat, AI_frame_top, ACCT_fds) in

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
    | first [ ra_50 | ra_51 | fail 1 "registry row cid 439586568 (shloadlit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442577328 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442577332 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442579552 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442579556 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581260 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581264 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581604 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442581608 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582120 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582124 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582280 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582284 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582440 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582444 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582956 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442582960 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583124 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583128 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583300 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442583304 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584188 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584192 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584532 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584536 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584808 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584812 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584968 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442584972 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585116 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585120 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585400 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585404 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585616 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442585620 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595204 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595208 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595564 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442595568 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442596664 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442596668 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442597388 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442597392 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442598224 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442598228 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442599352 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442599356 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442600460 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442600464 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442601296 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442601300 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602112 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602116 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602952 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442602956 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442603764 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442603768 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442604804 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442604808 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606036 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606040 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606572 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442606576 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607328 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607332 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607532 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442607536 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609104 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609108 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609420 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609424 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609428 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442609432 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610160 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610164 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610168 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442610172 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612792 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612796 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612800 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442612804 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613360 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613364 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613368 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442613372 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614336 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614340 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614344 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442614348 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615148 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615152 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615416 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615420 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615424 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442615428 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616192 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616196 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616200 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442616204 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617000 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617004 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617388 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617392 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617664 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442617668 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618000 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618004 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618008 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442618012 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619080 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619084 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619088 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442619092 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620716 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620720 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620724 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442620728 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622004 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622008 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622468 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622472 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622644 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622648 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622836 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442622840 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623192 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623196 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623532 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623536 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623692 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623696 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623892 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442623896 (rolit_c): no census theorem applies" ]
    | first [ ra_52 | fail 1 "registry row cid 442624460 (rolit_c): no census theorem applies" ]
    | first [ ra_53 | fail 1 "registry row cid 444386028 (casef_contract): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453577012 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453578516 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453580568 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453609780 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453612220 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453613160 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453614052 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453614944 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453615972 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453616748 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453618824 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453620372 (fake_free_c): no census theorem applies" ]
    | first [ ra_54 | fail 1 "registry row cid 453621740 (fake_free_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454579596 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610492 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610628 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610800 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610820 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610868 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610916 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454610964 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611020 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611040 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611112 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611148 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611188 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611208 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611252 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611272 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611320 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611484 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611540 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611560 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454611636 (opshload_c): no census theorem applies" ]
    | first [ ra_55 | fail 1 "registry row cid 454615188 (opshload_c): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455596812 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455597540 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455600644 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455601504 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455602300 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455603164 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455603844 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455606652 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455611648 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455611684 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 455622084 (gtvc_carg): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456577128 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456580336 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456596812 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456597540 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456600644 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456601504 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456602300 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456603164 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456604116 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456611648 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_57 | fail 1 "registry row cid 456738876 (gviewgc_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457596812 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457597540 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457600644 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457601504 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457602300 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457603164 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457611648 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 457611684 (gvechi_contract): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458585552 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458596140 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458598804 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458599928 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458605308 (twin_in_c): no census theorem applies" ]
    | first [ ra_59 | fail 1 "registry row cid 458608028 (twin_in_c): no census theorem applies" ]
    | first [ ra_60 | ra_61 | fail 1 "registry row cid 460586380 (gbnd_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461596812 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461597540 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461600644 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461601504 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461602300 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_62 | fail 1 "registry row cid 461603164 (gnarrow_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463580336 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463585832 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463603844 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_63 | fail 1 "registry row cid 463738876 (gperm_vec_contract): no census theorem applies" ]
    | first [ ra_64 | fail 1 "registry row cid 464585552 (gpotinit_contract): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465585968 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586000 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586152 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586184 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465586996 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587032 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587240 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587288 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587680 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587720 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587924 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465587952 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588356 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588564 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588788 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465588832 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589512 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589552 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589780 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465589808 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590068 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590096 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590260 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465590292 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591044 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591068 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591192 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591216 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465591340 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465595676 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596056 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596080 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596168 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465596192 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598336 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598832 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465598856 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465599464 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465599956 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465599980 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465604964 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465604992 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465605320 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465606124 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465606312 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465607692 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465607720 (opshloadu_c): no census theorem applies" ]
    | first [ ra_65 | fail 1 "registry row cid 465608040 (opshloadu_c): no census theorem applies" ]
    | first [ ra_66 | fail 1 "registry row cid 466577128 (gunrealign_contract): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468580336 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468582520 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468596812 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468596972 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468597540 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468597700 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468600644 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468600836 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468601504 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468601664 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468602300 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468602492 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468603164 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468603324 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468603844 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468606116 (gtvc_carg): no census theorem applies" ]
    | first [ ra_56 | fail 1 "registry row cid 468606652 (gtvc_carg): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469596812 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469597540 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469600644 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469601504 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469602300 (gvechi_contract): no census theorem applies" ]
    | first [ ra_58 | fail 1 "registry row cid 469603164 (gvechi_contract): no census theorem applies" ]
    | first [ ra_67 | fail 1 "registry row cid 471394828 (gviewdrop_reg_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472394828 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472596812 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472597540 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472600644 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472601504 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472602300 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472603164 (ginva_contract): no census theorem applies" ]
    | first [ ra_26 | fail 1 "registry row cid 472604116 (ginva_contract): no census theorem applies" ]
    | first [ ra_68 | fail 1 "registry row cid 473583108 (gshr_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478379860 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478577396 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_69 | fail 1 "registry row cid 478617788 (gbgnone_contract): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 482604844 (gnz_contract): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 482607572 (gnz_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485585860 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586456 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586608 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586828 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485586852 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587100 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587124 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587512 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587536 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587580 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587788 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485587808 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588100 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588120 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588224 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588244 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588632 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588656 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485588676 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589056 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589076 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589196 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589216 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589320 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589376 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589396 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589620 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589640 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589908 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485589928 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590164 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590392 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590412 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590536 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485590556 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485596680 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485597404 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485600476 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485600500 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485601312 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485601336 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602128 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602152 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602968 (gchkl_contract): no census theorem applies" ]
    | first [ ra_70 | fail 1 "registry row cid 485602992 (gchkl_contract): no census theorem applies" ]
    | first [ ra_71 | fail 1 "registry row cid 486394828 (pkmid_contract): no census theorem applies" ]
    | first [ ra_72 | fail 1 "registry row cid 487606536 (gexcl_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488582520 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488596812 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488596972 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488597540 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488597700 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488600644 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488600836 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488601504 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488601664 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488602300 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488602492 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488603164 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488603324 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488604124 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488604208 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488606116 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488606652 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_73 | ra_74 | fail 1 "registry row cid 488738876 (gtwinbnd_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489596812 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489597540 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489600644 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489601504 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489602300 (ganca_contract): no census theorem applies" ]
    | first [ ra_75 | fail 1 "registry row cid 489603164 (ganca_contract): no census theorem applies" ]
    | first [ ra_76 | fail 1 "registry row cid 494580336 (gpothr_contract): no census theorem applies" ]
    | first [ ra_76 | fail 1 "registry row cid 494738876 (gpothr_contract): no census theorem applies" ]
    | first [ ra_77 | ra_78 | fail 1 "registry row cid 496738876 (gvea3_contract): no census theorem applies" ] ]) : DrvLib.DrvLib.ctab_ok asegs RAx T_Asan2U.CONTRACTS).
End Reg.
