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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RoLitA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GViewDrop2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GUnrealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GBgNone.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2L Require T_Both2L.
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
Local Ltac ra_0 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Ctr.TwinB.amalloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (FakeLaw.TwinB.AIu_errno ExhFirst.TwinB.exh_first) (Acct.TwinB.ACCT_malloc AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_1 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.TwinB.stack_malloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow_f MP PB AsanAcct.TwinB.NMAX 1%uint63 eq_refl 8192 AsanW.AFake_sm0.TwinB.AFake_sm1g.ASTKMALLOC1 ltac:(lia) SmInst.TwinB.sm_walk_1 (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frame_in AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_2 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.SmSound.TwinB.stack_malloc_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok AsanImgx.TwinB.IMGSH_aci_A ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) F1Cw.TwinB.Cw_ghost_grow_f MP PB AsanAcct.TwinB.NMAX 2%uint63 eq_refl 4096 AsanW.AFake_sm0.TwinB.AFake_sm2.ASTKMALLOC2 ltac:(lia) SmInst.TwinB.sm_walk_2 (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frame_in AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_3 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.TwinB.amemcpy_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zro AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_gsh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_shmap AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zarg AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_aimg_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_4 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemcpyFinal.TwinB.aasan_memcpy_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zro AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_gsh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_shmap AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_holds_zarg AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_aimg_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_5 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemsetFinal.TwinB.amemset_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_6 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.MemsetFinal.TwinB.aasan_memset_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX) (AsanRun.TwinB.OPSA_holds_ssh AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (Acct.TwinB.ACCT_rng_stk_sh AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_frng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) W_PAT_SUBx (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_7 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.TwinB.amemcpy0_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_8 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.Memcpy0Sound.TwinB.aasan_memcpy0_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_9 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.CtrAnnot.TwinB.annotate_sound AIu2 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT UNIV Cw OPSA AIu_fake (AsanRun.TwinB.OPSA_holds1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov1 AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (F1Unp.TwinB.F1Unp.cw_vec_unowned bsegs) (F1Unp.TwinB.F1Unp.cw_vecs_distinct bsegs) (F1Unp.TwinB.F1Unp.cw_sub_ghost bsegs) (AsanRun.TwinB.OPSA_frame_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_fp_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) AsanRun.TwinB.OTHERA (AsanRun.TwinB.OPSA_mo_other AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (AsanRun.TwinB.OPSA_cov0_img AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB AsanAcct.TwinB.NMAX (Acct.TwinB.ACCT_rng AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_rng_aimg AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX) (Acct.TwinB.ACCT_silent AsanAcct.TwinB.NMAX AsanAcct.TwinB.HLIM MP MINV AsanRun.TwinB.OTHERA (AcctPlug.TwinB.MP_relx inp) AcctPlug.TwinB.OTHER_relx MINV_intro AsanAcct.TwinB.SHFIX)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_10 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.RoLit.RoLit.rolit_sound bsegs OPSA RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH bsegs) CHSx (AsanRun.TwinB.OPSA_acc_user_law AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) (RoLitInst.TwinB.OPSA_rolit_HR AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file) MP PB (AsanPB.TwinB.HMPA inp)); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_11 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GRealign.GRealign.grealign_sound _ _ bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Local Ltac ra_12 := (eapply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.GTwinSub.GTwinSub.gtwinsub_sound _ _ _ bsegs OPSA MP PB); first [reflexivity | vm_compute; reflexivity | (apply (DrvLib.DrvLib.ecall_atb_sound bsegs); vm_compute; reflexivity)]).
Definition ctab_Both2L := let _USE := (Hva, Hsp, Hfit, ACCT_led, ACCT_cov, ACCT_cov_sh, ACCT_mat, AI_frame_top, ACCT_fds) in

  (ltac:(apply (DrvLib.DrvLib.ctab_ok_of_list bsegs RAx); repeat (apply Forall_cons || apply Forall_nil); cbn [snd];
    [ first [ ra_0 | fail 1 "registry row cid 400 (amalloc_c): no census theorem applies" ]
    | first [ ra_1 | fail 1 "registry row cid 405 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_2 | fail 1 "registry row cid 406 (stack_malloc_c): no census theorem applies" ]
    | first [ ra_3 | ra_4 | fail 1 "registry row cid 411 (amemcpy_c): no census theorem applies" ]
    | first [ ra_5 | ra_6 | fail 1 "registry row cid 413 (amemset_c): no census theorem applies" ]
    | first [ ra_7 | ra_8 | fail 1 "registry row cid 415 (amemcpy0_c): no census theorem applies" ]
    | first [ ra_9 | fail 1 "registry row cid 419 (annotate_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442578904 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442578908 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442578912 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442578916 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442580152 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442580156 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442580160 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442580164 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442581928 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442581932 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442582356 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442582360 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442582676 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442582680 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442582684 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442582688 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442583640 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442583644 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442583868 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442583872 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442584100 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442584104 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442584480 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442584484 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442584976 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442584980 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442585584 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442585588 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442585772 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442585776 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442585956 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442585960 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442586096 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442586100 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442586708 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442586712 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442586940 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442586944 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442588072 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442588076 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442588344 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442588348 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442588724 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442588728 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589220 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589224 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589548 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589552 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589736 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589740 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589920 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442589924 (rolit_c): no census theorem applies" ]
    | first [ ra_10 | fail 1 "registry row cid 442632976 (rolit_c): no census theorem applies" ]
    | first [ ra_11 | fail 1 "registry row cid 450578888 (grealign_contract): no census theorem applies" ]
    | first [ ra_12 | fail 1 "registry row cid 451578888 (gtwinsub_contract): no census theorem applies" ] ]) : DrvLib.DrvLib.ctab_ok bsegs RAx T_Both2L.CONTRACTS).
End Reg.
