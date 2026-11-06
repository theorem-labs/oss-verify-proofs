(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: made for reac-repacer/fuzz_uci's ASan image from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/A/DecodeClose.v (the closing form: one named Section hypothesis per open part, the parts proved elsewhere applied as Lemmas of the hypotheses' names and statements, the program contract LIB_CONTRACT from the entry walk and its callees, the two statements from AsanTop; its About / Print Assumptions commands are left out, because on this image's core those commands for the three tops take about 13 minutes per build) and libreac/fuzz_grant proofs/libreac/fuzz_grant/lib/A/AGrantT.v (the driver step: the core arguments of tfib_srealizesX, the run ceiling and TFIB_T), with the sink guard of fuzz_grant's lib/A/GrantTop.v; names GrantB -> UciB, the library shape fuzz_uci's checksum_shape, fuzz_uci's own program statements and rows; module paths changed. *)
(* The closing side of fuzz_uci's two ASan statements (this file is assembly: it proves no function).

   TFIB_T (lib/A/UciTFIB.v) is closed as fuzz_grant's lib/A/AGrantT.v closes it: the relocated core's
   lib/A/AD1q.v:71 tfib_srealizesX joins the start-up certificate (lib/A/AB1n.v:54 tfib_startup_T1) and the driver's
   closed walk (lib/A/AD1q.v:69 DRV_MAINX, from lib/A/AD1p.v tfib_drv_main) over the program contract of the entry
   function (lib/A/ACfn.v:73 tfib_lib_contract_x_all) and the runtime walks. Every argument of tfib_srealizesX is a
   core lemma at B := UciB (lib/A/AD2l.v:16) except the program contract, LIB_CONTRACT below, which the entry's walk
   statement (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v) gives from its callees' contracts. From TFIB_T, lib/A/AsanTop.v
   gives Statements.asan_agrees and Statements.asan_halts.

   The Section has no hypothesis: every part of the composition is a Lemma: a proved program walk (check_clamp,
   lib/A/Prog/check_clamp_cgW.v; LLVMFuzzerTestOneInput, lib/A/Prog/LLVMFuzzerTestOneInput_walk.v; check_no_overread,
   lib/A/Prog/check_no_overread_cgW.v; check_value, lib/A/Prog/check_value_cgW.v; rp_uci_int, lib/A/Prog/rp_uci_int_cgW.v;
   rp_hot_clamp's footprint walk, lib/A/Prog/rp_hot_clamp_FW.v), a core lemma at UciB, a relocated runtime contract at
   UciB (the class-1 fake stack, lib/A/Rt/AF0s.v; the memchr interceptor, lib/A/Rt/Memchr.v), a leaf-kit fact
   (lib/A/Prog/LeafCgClose.v) or a computation at UciB (lib/A/UciAFacts.v).

   THE SINK INSTANCE IS EXPLICIT (as fuzz_grant's lib/A/GrantTop.v): lib/A/AsanTop.v loads the plain build's
   lib/Reusable/YI5b.v and YI5c.v, whose global instances name the PLAIN build's output head. Both hints are removed
   below, every part names SK := AE2k.tfib_sink_head, and sk_probe_is_asan shows what a bare sink_head resolves to.

   NO hypothesis here restates a top: TFIB_T, Statements.asan_agrees and Statements.asan_halts occur only as the
   conclusions proved below. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_uci Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK15 YK18 YA02.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1h.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK04 YA0i YA0n YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YE00 YE01 YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YG0t.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import ACfn AB1v AF0m.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import
AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AE2k AD1u.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import ACej.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AD1q UciTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciPSyms UciPAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require PaBase UciCg UciPImg LeafCgKit LeafCgClose
LLVMFuzzerTestOneInput_cg check_no_overread_cg check_value_cg check_clamp_cg rp_uci_int_cg rp_hot_clamp_F_c
rp_hot_clamp_cg rp_uci_int_cgW rp_hot_clamp_FW check_no_overread_cgW check_value_cgW LLVMFuzzerTestOneInput_walk
check_clamp_cgW.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt Require MemchrDef AF0s Memchr.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require UciAFacts AsanTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Open Scope Z_scope.

Module USt := OSSVerify.reac_repacer.fuzz_uci.Statements.
Module PB := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.PaBase.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.UciCg.
Module UImg := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.UciPImg.
Module UAddr := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.UciPAddr.
Module LK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgKit.
Module LCl := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgClose.
Module PL := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LLVMFuzzerTestOneInput_cg.
Module PN := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_no_overread_cg.
Module PV := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_value_cg.
Module PK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_clamp_cg.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_uci_int_cg.
Module PH := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_hot_clamp_F_c.
Module LHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_hot_clamp_cg.
Module MD := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt.MemchrDef.
Module UAF := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.UciAFacts.

(* The guard: the plain build's sink hints are out of the way, so no `{SK}` can be filled with the plain build's
   head. *)
#[local] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints YI5c.src0_sink : typeclass_instances.

(* What a bare `sink_head` resolves to in this file: the ASan image's own head. *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = AE2k.tfib_sink_head.
Proof. reflexivity. Qed.

(* The stack-pointer window, from valid_sp (fuzz_grant's AGrantT.v valid_sp_windowX). *)
Lemma valid_sp_windowU : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The image's data the parts are stated at. *)
(* segs: image A's loaded segments (lib/A/UciTFIB.v; = lib/A/AB1v.v:13 tfibsegs = lib/A/AB1h.v:19 TSEGS). *)
Local Abbreviation segs := ucisegs0.
(* B: the image's symbol and trace record, lib/A/AD2l.v:16 UciB (UciB_syms : UciSyms UciB at :74). *)
Local Abbreviation B := AD2l.UciB.
(* MT: lib/Reusable/YCbp.v ameter_triv; XL: lib/A/UciAFacts.v uci_XL0 (fun _ => 0). *)
Local Abbreviation MT := ameter_triv.
Local Abbreviation XL := UAF.uci_XL0.
(* The program's read-only range: [0x96ac0, 0x97d18) (.data.rel.ro and .got, lib/A/AB1w.v), the second disjunct of
   the core's lib/A/ACeg.v:49-51 in_ro_tfa, which gives the driver's premise RO_IN. *)
Local Abbreviation RLO := 0x96ac0.
Local Abbreviation RHI := 0x97d18.
(* The sink: the ASan image's own head (lib/A/AE2k.v:36) and record (:44). *)
Local Abbreviation SK := AE2k.tfib_sink_head.
Local Abbreviation KS := AE2k.tfib_K.

Section asan.

(* ===================================================================================================== *)
(* 1. The program walks (the statements of lib/A/Prog)                                                   *)
(* ===================================================================================================== *)
(* H_PROG_LLVMF: the walk of LLVMFuzzerTestOneInput (0x7f2e8), lib/A/Prog/LLVMFuzzerTestOneInput_cg.v
   uci_llvmf_holds_stmt (its callee contracts give the core's slot): PROVED for every record, meter, bound and
   read-only range by lib/A/Prog/LLVMFuzzerTestOneInput_walk.v uci_llvmf_holds_any, applied at UciB, ameter_triv,
   uci_XL0, RLO and RHI. *)
Lemma H_PROG_LLVMF : forall (rc : YM05.RunCeil),
  @PL.uci_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof. exact (fun rc => LLVMFuzzerTestOneInput_walk.uci_llvmf_holds_any rc B MT XL RLO RHI). Qed.
(* H_PROG_CNO: the walk of check_no_overread (0x7f4fc), caller-journal form, at the caller's context,
   lib/A/Prog/check_no_overread_cg.v uci_check_no_overread_cg_holds_stmt: PROVED for every record, meter and context by
   lib/A/Prog/check_no_overread_cgW.v uci_check_no_overread_cg_holds, applied at UciB, ameter_triv and
   CTX_check_no_overread. *)
Lemma H_PROG_CNO : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PN.uci_check_no_overread_cg_holds_stmt fx rc B MT PL.CTX_check_no_overread.
Proof.
  exact (fun fx rc => @check_no_overread_cgW.uci_check_no_overread_cg_holds fx rc AD2l.UciB ameter_triv
    PL.CTX_check_no_overread).
Qed.
(* H_PROG_CV: the walk of check_value (0x7f62c), caller-journal form, lib/A/Prog/check_value_cg.v
   uci_check_value_cg_holds_stmt: PROVED for every record and meter by lib/A/Prog/check_value_cgW.v
   uci_check_value_cg_holds, applied at UciB and ameter_triv. *)
Lemma H_PROG_CV : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PV.uci_check_value_cg_holds_stmt fx rc B MT.
Proof. exact (fun fx rc => @check_value_cgW.uci_check_value_cg_holds fx rc B MT). Qed.
(* H_PROG_CC: the walk of check_clamp (0x7f888), caller-journal form (its class-1 fake frame changes frames S),
   lib/A/Prog/check_clamp_cg.v uci_check_clamp_cg_holds_stmt: PROVED for every record and meter by
   lib/A/Prog/check_clamp_cgW.v uci_check_clamp_cg_holds, applied at UciB and ameter_triv. *)
Lemma H_PROG_CC : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PK.uci_check_clamp_cg_holds_stmt fx rc B MT.
Proof. exact (fun fx rc => @check_clamp_cgW.uci_check_clamp_cg_holds fx rc AD2l.UciB ameter_triv). Qed.
(* H_PROG_RUI: the walk of rp_uci_int (0x7fef0), realizes form (it calls only the memchr interceptor),
   lib/A/Prog/rp_uci_int_cg.v uci_rp_uci_int_holds_stmt: PROVED for every record by lib/A/Prog/rp_uci_int_cgW.v
   uci_rp_uci_int_holds, applied at UciB. *)
Lemma H_PROG_RUI : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PR.uci_rp_uci_int_holds_stmt fx rc B.
Proof. exact (fun fx rc => @rp_uci_int_cgW.uci_rp_uci_int_holds fx rc AD2l.UciB). Qed.
(* H_PROG_RHC_F: the footprint walk of the leaf rp_hot_clamp (0x7fc64), lib/A/Prog/rp_hot_clamp_F_c.v
   rp_hot_clamp_contract_F: PROVED by lib/A/Prog/rp_hot_clamp_FW.v rp_hot_clamp_holds_F; its translation to the leaf
   form is PROVED too (lib/A/Prog/rp_hot_clamp_cg.v uci_rp_hot_clamp_cg_of_F). *)
Lemma H_PROG_RHC_F : PH.rp_hot_clamp_contract_F.
Proof. exact rp_hot_clamp_FW.rp_hot_clamp_holds_F. Qed.

(* ===================================================================================================== *)
(* 2. The runtime contracts, relocated onto this image (lib/A/Rt)                                         *)
(* ===================================================================================================== *)
(* H_RT_STACK_MALLOC1: the class-1 fake stack (__asan_stack_malloc_1, 0x3c1b8), called by check_clamp at +0x64
   with a0 = 0x60: lib/A/Rt/AF0s.v stack_malloc1_contract (fuzz_grant's released lib/A/Rt/AF0r.v / AF0s.v relocated
   onto this image) at UciB. *)
Lemma H_RT_STACK_MALLOC1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astack_malloc_realizes fx rc segs B 1.
Proof. intros rc fx. exact (@AF0s.stack_malloc1_contract fx rc AD2l.UciB (AR_laws_ok tfibsegs AD2l.UciB) AD2l.UciB_syms). Qed.
(* H_RT_MEMCHR: the memchr interceptor (0x4107c) with any byte c (rp_uci_int calls it with c = '\n'), over musl
   memchr's constant window [0x10350, 0x10370) (lib/A/Rt/MemchrDef.v amemchr_realizesM): lib/A/Rt/Memchr.v
   memchr_icpt_contract (fuzz_boxreg's released lib/A/Rt/Memchr*.v relocated onto this image) at UciB. The core's
   lib/A/AE6x.v memchr0_icpt_contract is c = 0 only. *)
Lemma H_RT_MEMCHR : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @MD.amemchr_realizesM fx rc segs B 0x10350 0x10370 (UAddr.uci_sigma US___interceptor_trampoline_memchr).
Proof. intros rc fx. exact (@Memchr.memchr_icpt_contract fx rc AD2l.UciB (AR_laws_ok tfibsegs AD2l.UciB) AD2l.UciB_syms). Qed.

(* ===================================================================================================== *)
(* 3. The leaf-kit facts (lib/A/Prog/LeafCgClose.v)                                                      *)
(* ===================================================================================================== *)
Lemma H_KIT_AVIEW_EXT : @LK.aview_ext_stmt (aview segs).
Proof. exact LCl.uci_a_kit_aview_ext. Qed.
Lemma H_KIT_AVIEW_SOME : @LK.aview_some_stmt (aview segs).
Proof. exact LCl.uci_a_kit_aview_some. Qed.
Lemma H_LEAF_GLUE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview segs) -> @LK.aview_some_stmt (aview segs) ->
  @PCs.uci_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof. exact (LCl.uci_a_leaf_glue B). Qed.

(* ===================================================================================================== *)
(* 4. The facts about B the walks take, by computation at UciB (lib/A/UciAFacts.v)                       *)
(* ===================================================================================================== *)
Lemma HB_CELLS : @PCs.uci_cells B.
Proof. exact UAF.uci_cells_UciB. Qed.
Lemma HB_RO_RD_UNOWNED : PCs.uci_ro_rd_unowned B.
Proof. exact UAF.uci_ro_rd_unowned_UciB. Qed.
Lemma HB_ROM_NO_ERRNO : PCs.uci_rom_no_errno B.
Proof. exact UAF.uci_rom_no_errno_UciB. Qed.
Lemma HB_CNO_UCTX : @PN.uci_cno_uctx B PL.CTX_check_no_overread.
Proof. exact UAF.uci_cno_uctx_UciB. Qed.
Lemma HB_CNO_UFIX : @PN.uci_cno_ufix B.
Proof. exact UAF.uci_cno_ufix_UciB. Qed.
Lemma HB_CV_UFIX : @PV.uci_cv_ufix B.
Proof. exact UAF.uci_cv_ufix_UciB. Qed.
Lemma HB_COST : forall n, 0 <= n -> @PL.uci_llvmf_cost MT n <= XL n.
Proof. exact UAF.uci_llvmf_cost_triv. Qed.
Lemma HB_API_ENV : api_env segs B.
Proof. exact UAF.uci_api_env_UciB. Qed.
Lemma HB_RO_BELOW_OFL : @PB.ro_below_ofl segs RLO RHI SK.
Proof. exact UAF.uci_ro_below_ofl_UciB. Qed.

(* ===================================================================================================== *)
(* 5. The core facts, each a lemma of the relocated core at UciB                                          *)
(* ===================================================================================================== *)
(* H_RT_MALLOC / H_RT_FREE: lib/A/AF0w.v:46 tfib_amalloc_realizes, lib/A/AF0q.v:14 afree_realizes_closed. *)
Lemma H_RT_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. intros rc fx. exact (@AF0w.tfib_amalloc_realizes fx rc B UciB_syms (fun t => eq_refl)). Qed.
Lemma H_RT_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. intros rc fx. exact (@AF0q.afree_realizes_closed fx rc B UciB_syms (fun t => eq_refl)). Qed.
(* H_RT_MEMCPY_WRAP: the memcpy interceptor the driver calls, lib/A/AD2m.v:18 tfib_AICPY. *)
Lemma H_RT_MEMCPY_WRAP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. intros rc fx. exact (AD2m.tfib_AICPY B UciB_syms). Qed.
(* H_RT_ASAN_MEMCPY: __asan_memcpy (0x50674), lib/A/AE2q.v:145 asan_memcpy_realizes; one contract for the four
   harness sites, each site's premises proved by the walk at the site. *)
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (uci_sigma US___asan_memcpy).
Proof.
  intros rc fx. change (uci_sigma US___asan_memcpy) with 0x50674.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
  exact (AE2q.asan_memcpy_realizes B (AR_laws_ok tfibsegs B) UciB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
(* HB_PC_WRAP_MALLOC / HB_PC_WRAP_FREE / HB_PC_STACK_MALLOC1: the record's code addresses are the listing's,
   0x51788 / 0x51784 / 0x3c1b8 (lib/A/AF0l.v Tfib_code). *)
Lemma HB_PC_WRAP_MALLOC : pc_wrap_malloc (as_code B) = uci_sigma US___interceptor_trampoline_malloc.
Proof. reflexivity. Qed.
Lemma HB_PC_WRAP_FREE : pc_wrap_free (as_code B) = uci_sigma US___interceptor_trampoline_free.
Proof. reflexivity. Qed.
Lemma HB_PC_STACK_MALLOC1 : pc_stack_malloc (as_code B) 1 = uci_sigma US___asan_stack_malloc_1.
Proof. reflexivity. Qed.
(* HB_UNIVERSE_OK / HB_MODEL_LAWS: lib/A/AF0m.v:386 ts_universe at UciB_syms; Reusable/YG05.v:140 model_laws_ok. *)
Lemma HB_UNIVERSE_OK : universe_ok (as_universe B).
Proof. exact (ts_universe B UciB_syms). Qed.
Lemma HB_MODEL_LAWS : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) HB_UNIVERSE_OK). Qed.
(* HB_METER_LAWS / HB_METER_FS_LAWS: Reusable/YCbp.v:23 ameter_triv_laws, :25 ameter_triv_fs_laws. *)
Lemma HB_METER_LAWS : ameter_laws MT.
Proof. exact ameter_triv_laws. Qed.
Lemma HB_METER_FS_LAWS : ameter_fs_laws MT.
Proof. exact ameter_triv_fs_laws. Qed.
(* HB_SMP / HB_ASF / HB_FFL: Reusable/YG05.v:71 stack_malloc_progress, Reusable/YG0t.v:475 astack_free_law_ok, and
   AR_laws' al_flag / al_client_img with the image cover lib/A/ACeg.v:92 tfib_img_cover. *)
Lemma HB_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma HB_ASF : forall (rc : YM05.RunCeil), astack_free_law segs B.
Proof. intros rc. exact (YG0t.astack_free_law_ok (rc := rc) segs B). Qed.
Lemma HB_FFL : forall (rc : YM05.RunCeil), frame_flag_lawP segs B.
Proof.
  intros rc ly S W mem md cid pos HAR Hin.
  pose proof (AR_laws_ok segs B) as LAWS.
  destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
  destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
  { right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
  pose proof HAR as (M & L & _). pose proof (ACeg.tfib_img_cover ly S md L) as [C1 C2].
  unfold ACeg.TFIB_IMG_LO, ACeg.TFIB_IMG_END in C1, C2.
  destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
  split; [exact Hp|]. split; [exact Ho|]. split.
  - split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
  - split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* HB_SINK_IMG_LAWS / HB_SINK_KEPT / HB_META_KEPT: the core's sink record laws, lib/A/AD1u.v:44 tfib_AIL, and
   Reusable/YE01.v:85 asink_none_kept / :156 ameta_inv_kept specialised to one journal step. *)
Lemma HB_SINK_IMG_LAWS : @asink_img_laws SK segs B KS.
Proof. apply AD1u.tfib_AIL; first [exact UciB_syms | apply AR_laws_ok]. Qed.
Lemma HB_SINK_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    asink_none segs KS (mrestrict (w_H W0) mem0) md0 -> asink_none segs KS (mrestrict (w_H W') mem') md'.
Proof.
  intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hc HS.
  exact (asink_none_kept (rc := rc) (SK := SK) segs B KS HB_SINK_IMG_LAWS
    STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hc HS).
Qed.
Lemma HB_META_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ameta_inv segs KS ly (mrestrict (w_H W0) mem0) M -> ameta_inv segs KS ly' (mrestrict (w_H W') mem') M.
Proof.
  intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM.
  exact (ameta_inv_kept (rc := rc) (SK := SK) segs B KS HB_SINK_IMG_LAWS
    STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM).
Qed.
(* H_LINK_MALLOC04 / H_LINK_FREE04: the call-rule form the walks consume, Reusable/YCbp.v:31 amalloc04_rule_triv /
   :40 afree04_rule_triv, at the image's segments (lib/A/Prog/UciPImg.v uci_segs_low), HB_API_ENV, AR_laws_ok and
   HB_MODEL_LAWS. *)
Lemma H_LINK_MALLOC04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @amalloc_realizes fx rc segs B -> @amalloc04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AM. apply (amalloc04_rule_triv (SK := SK) segs B).
  - exact UImg.uci_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AM.
Qed.
Lemma H_LINK_FREE04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree_realizes fx rc segs B -> @afree04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AF. apply (afree04_rule_triv (SK := SK) segs B).
  - exact UImg.uci_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AF.
Qed.

(* ===================================================================================================== *)
(* 6. The composition                                                                                     *)
(* ===================================================================================================== *)
Section RC. Context {rc : YM05.RunCeil}.

(* rp_hot_clamp, from its PROVED translation (lib/A/Prog/rp_hot_clamp_cg.v uci_rp_hot_clamp_cg_of_F) over the kit's
   generic translation, applied to its footprint walk. *)
Lemma LEAF_HOT_CLAMP : forall fx : YK11.FPState, @PCs.uci_leaf_wr_at rc B (@LHC.uci_rp_hot_clamp_cg) fx.
Proof.
  intros fx. exact (@LHC.uci_rp_hot_clamp_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_RHC_F).
Qed.

(* rp_uci_int's walk, from the memchr interceptor's contract. *)
Lemma RUI_HOLDS : forall fx : YK11.FPState, @PR.uci_rp_uci_int_cg fx rc B (uci_sigma US_rp_uci_int).
Proof.
  intros fx. apply (H_PROG_RUI fx rc).
  - exact HB_CELLS.
  - apply AR_laws_ok.
  - exact HB_ROM_NO_ERRNO.
  - intros fx'. exact (H_RT_MEMCHR rc fx').
Qed.

(* check_no_overread's walk, from its callee contracts. *)
Lemma CNO_HOLDS : forall fx : YK11.FPState,
  @PN.uci_check_no_overread_cg fx rc B MT (uci_sigma US_check_no_overread) PL.CTX_check_no_overread.
Proof.
  intros fx. apply (H_PROG_CNO fx rc).
  - exact HB_PC_WRAP_MALLOC.
  - exact HB_PC_WRAP_FREE.
  - exact HB_CELLS.
  - exact HB_RO_RD_UNOWNED.
  - exact HB_ROM_NO_ERRNO.
  - apply AR_laws_ok.
  - exact HB_METER_LAWS.
  - exact HB_CNO_UCTX.
  - exact HB_CNO_UFIX.
  - intros fx'. exact (H_LINK_MALLOC04 rc fx' (H_RT_MALLOC rc fx')).
  - intros fx'. exact (H_LINK_FREE04 rc fx' (H_RT_FREE rc fx')).
  - intros fx'. exact (H_RT_ASAN_MEMCPY rc fx').
  - exact RUI_HOLDS.
Qed.

(* check_value's walk, from its callee contracts. *)
Lemma CV_HOLDS : forall fx : YK11.FPState, @PV.uci_check_value_cg fx rc B MT (uci_sigma US_check_value).
Proof.
  intros fx. apply (H_PROG_CV fx rc).
  - exact HB_PC_WRAP_MALLOC.
  - exact HB_PC_WRAP_FREE.
  - exact HB_CELLS.
  - exact HB_RO_RD_UNOWNED.
  - exact HB_ROM_NO_ERRNO.
  - apply AR_laws_ok.
  - exact HB_METER_LAWS.
  - exact HB_CV_UFIX.
  - intros fx'. exact (H_LINK_MALLOC04 rc fx' (H_RT_MALLOC rc fx')).
  - intros fx'. exact (H_LINK_FREE04 rc fx' (H_RT_FREE rc fx')).
  - intros fx'. exact (H_RT_ASAN_MEMCPY rc fx').
  - exact RUI_HOLDS.
Qed.

(* check_clamp's walk, from the class-1 fake stack, __asan_memcpy and the leaf rp_hot_clamp. *)
Lemma CC_HOLDS : forall fx : YK11.FPState, @PK.uci_check_clamp_cg fx rc B MT (uci_sigma US_check_clamp).
Proof.
  intros fx. apply (H_PROG_CC fx rc).
  - exact HB_PC_STACK_MALLOC1.
  - exact HB_CELLS.
  - apply AR_laws_ok.
  - exact HB_METER_LAWS.
  - exact HB_METER_FS_LAWS.
  - exact HB_SMP.
  - exact (HB_ASF rc).
  - exact (HB_FFL rc).
  - intros fx'. exact (H_RT_STACK_MALLOC1 rc fx').
  - intros fx'. exact (H_RT_ASAN_MEMCPY rc fx').
  - exact LEAF_HOT_CLAMP.
Qed.

(* The program contract of the entry function, from its walk and every callee it names. *)
Lemma LIB_CONTRACT : @tfib_lib_contract_x_all rc checksum_shape B MT XL XL RLO RHI.
Proof.
  apply (H_PROG_LLVMF rc).
  - exact HB_CELLS.
  - exact HB_RO_RD_UNOWNED.
  - exact HB_ROM_NO_ERRNO.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact HB_METER_LAWS.
  - exact HB_METER_FS_LAWS.
  - exact HB_SINK_IMG_LAWS.
  - exact (HB_SINK_KEPT rc).
  - exact (HB_META_KEPT rc).
  - exact HB_RO_BELOW_OFL.
  - exact CNO_HOLDS.
  - exact CV_HOLDS.
  - exact CC_HOLDS.
  - exact HB_COST.
Qed.

(* The driver step: the core's tfib_srealizesX over LIB_CONTRACT (fuzz_grant's AGrantT.v:42-73 at fuzz_uci's
   names). *)
Let HB : UciSyms B := UciB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let LIBX : tfib_lib_contract_x_all B MT XL XL RLO RHI := LIB_CONTRACT.
Let RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a := fun a H => or_intror H.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok MT S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d5e6 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d5fb (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x157cd (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.

Lemma uci_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs UAs.M.init_pc UAs.M.phdrs sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS:=checksum_shape) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  change target_alloc_limit with YA02.LIMIT.
  exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK MT XL XL RLO RHI MT_FREE RO_IN LIBX xst XFR PF1 PFN est ESTI
    ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.

(* fuzz_grant's AGrantT.v:75-84 grant_srealizesX_top and grant_TFIB_T_of_lib: the run ceiling of the start. *)
Theorem uci_TFIB_T_of_parts : TFIB_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@uci_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowU sp Hsp)) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan statements of record, given only the named parts above. *)
Theorem uci_asan_agrees_of_parts : USt.asan_agrees.
Proof. exact (AsanTop.uci_asan_agrees_of_tfib uci_TFIB_T_of_parts). Qed.
Theorem uci_asan_halts_of_parts : USt.asan_halts.
Proof. exact (AsanTop.uci_asan_halts_of_tfib uci_TFIB_T_of_parts). Qed.
End asan.
