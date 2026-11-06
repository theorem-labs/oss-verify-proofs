(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD1q.v (tfib_srealizesX),
   lib/YB1n.v (tfib_startup_T1, HS_ok) and lib/YD2o.v (TFIB_TB_of_partsXF), in the form of fuzz_pcap's closing side
   (proofs/libreac/fuzz_pcap/lib/A/PcapClose.v, origin/cold/port-pcap-comp 86b0e893fe8), for libreac/fuzz_decode's
   ASan+UBSan image: one named Section hypothesis per remaining part, module paths and names changed. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_decode, by way of fuzz_grant's lib/A/AsanTop.v: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain slot contract of lib/Prog/LLVMFuzzerTestOneInput_gfr.v, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: adapted from lib/A/GrantTop.v for image B (fuzz_grant.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_decode/lib/B/DecodeBClose.v and lib/A/AsanTop.v
   (Section b) at recipes commit 88154566652a and proofs/libreac/fuzz_grant/lib/B/GrantBTop.v at recipes commit
   4f87de75d67, for reac-repacer/fuzz_uci's ASan+UBSan image (fuzz_uci.asan-ubsan): the image-B core's closed walk
   lib/B/YD1q.v tfib_srealizesX takes the place of the donor's H_STARTUP / H_DRIVER pair; its slot lib/B/YCfn.v:140 is
   LIB_CONTRACT, composed from the six program walk statements of lib/B/Prog and their callees' contracts; one named
   Section hypothesis per program walk; the runtime, kit and computed rows are Lemmas citing lib/B/Rt, lib/B/Prog/
   LeafCgClose.v and lib/B/UciBFacts.v; the read-only range 0x96bc8 .. 0x97e20 and the memchr window 0x10350 ..
   0x10370 are image B's; module paths and names changed. *)
(* The image-B composition of fuzz_uci's two ASan+UBSan statements from the 18 rows below (proves no function).
   Image A's twin is lib/A/UciClose.v: the same 18 rows in the same order (the 8 program and runtime rows, the 3 KIT
   rows, the 7 COMPUTE rows), the same CORE lemmas and the same composition, with B's modules (lib/B, lib/B/Prog,
   lib/B/Rt), B's values and the asan_ubsan statement types; every row and lemma is stated at the concrete record
   B := UciB (lib/B/YD2l.v:17). Each row proved in another file is a Lemma or Definition of the same name and
   statement, citing that proof; no row is a Section hypothesis. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_uci Require Statements Images.
From OSSVerify.reac_repacer.fuzz_uci.images Require Plain.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB12 YB1h YB01 YB1n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG0q YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YC5d YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import ZTraceSpec UciAsanShared.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require UciHaltsSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v YF0m YCeg YD1v YD1w YD1x YD1i YCfn YD1p.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YM09 YK0o HaltsKitB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require UciBTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YD1q YD2l UciBRtAlloc YD2m YD1k YD1o YD1l YD1j YE2q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require LeafCgKit LeafCgFacts check_value_cgW check_clamp_cgW.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Rt Require YF0s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Module CVW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_value_cgW.
Module UBT := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.UciBTFIB.
Module BD2l := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD2l.
Module BD1q := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD1q.
Module BAl := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.UciBRtAlloc.
Module BD2m := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD2m.
Module BD1k := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD1k.
Module BD1o := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD1o.
Module BD1l := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD1l.
Module BD1j := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD1j.
Module BE2q := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YE2q.
Module BCbp := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YCbp.
Module BCeg := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YCeg.
Module BCfn := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YCfn.
Module USt := OSSVerify.reac_repacer.fuzz_uci.Statements.
Module UIm := OSSVerify.reac_repacer.fuzz_uci.Images.
Module UPl := OSSVerify.reac_repacer.fuzz_uci.images.Plain.
Module UHS := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.UciHaltsSpec.
Module LK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LeafCgFacts.
Module BF0s := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Rt.YF0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import UciPSyms.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require UciPAddr UciPImg UciCg LLVMFuzzerTestOneInput_cg
  check_no_overread_cg check_value_cg check_clamp_cg rp_uci_int_cg rp_hot_clamp_F_c rp_hot_clamp_cg PaBase LeafCgClose.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Rt Require MemchrDef Memchr.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require UciBFacts YE2k YE01 YD1u.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG05 YG0t YE00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI5b YI5c.
Module PL := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LLVMFuzzerTestOneInput_cg.
Module PN := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_no_overread_cg.
Module PV := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_value_cg.
Module PK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_clamp_cg.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_uci_int_cg.
Module PH := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_hot_clamp_F_c.
Module LHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_hot_clamp_cg.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.UciCg.
Module UAddr := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.UciPAddr.
Module BImg := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.UciPImg.
Module PB := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.PaBase.
Module BLC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LeafCgClose.
Module MD := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Rt.MemchrDef.
Module BMc := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Rt.Memchr.
Module BF := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.UciBFacts.
Module BE2k := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YE2k.
Module BE01 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YE01.
Module BD1u := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YD1u.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require check_no_overread_cgW rp_uci_int_cgW.
(* The guard, as image A's lib/A/UciClose.v: the plain build's sink hints are out of the way, so no `{SK}` can be
   filled with the plain build's head. *)
#[local] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink : typeclass_instances.
Module CNOW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_no_overread_cgW.
(* What a bare `sink_head` resolves to in this file: the ASan+UBSan image's own head (lib/B/YE2k.v:37). *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = BE2k.tfib_sink_head.
Proof. reflexivity. Qed.
Module RUIW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_uci_int_cgW.
(* ===================================================================================================== *)
(* The two ASan+UBSan statements from TFIB_T (decode lib/A/AsanTop.v Section b, at fuzz_uci's names): the  *)
(* plain side, the budget orderings and SPECX_shape_ok are the shared files' (lib/UciAsanShared.v,         *)
(* lib/A/UciHaltsSpec.v, both free of image-A files).                                                     *)
(* ===================================================================================================== *)
Section b.
Hypothesis TFIBB : UBT.TFIB_T.

Theorem uci_asan_ubsan_agrees_of_tfib : USt.asan_ubsan_agrees.
Proof.
  unfold USt.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (uci_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold UIm.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    UPl.M.loaded_segments UPl.M.init_pc UPl.M.phdrs sp brk mb rnd
    UBT.ucisegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=checksum_shape) inp) (SPECX (LS:=checksum_shape) inp) inp
    asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem uci_asan_ubsan_halts_of_tfib : USt.asan_ubsan_halts.
Proof.
  unfold USt.asan_ubsan_halts, UIm.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage UBT.ucisegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused UBT.ucisegsB0 AsanUbsan.M.init_pc
    AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (UHS.SPECX_shape_ok inp).
Qed.
End b.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require LLVMFuzzerTestOneInput_cgW.
(* The stack-pointer window, from valid_sp (decode lib/B/DecodeBClose.v valid_sp_windowD). *)
Lemma valid_sp_windowU : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require rp_hot_clamp_FW.
Module RHCW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_hot_clamp_FW.
(* The values the core's closed walk and the rows are stated at; no Section Variable. segs =
   AsanUbsan.M.loaded_segments (= lib/B/YB1v.v:13 tfibsegs); B = lib/B/YD2l.v:17 UciB (UciB_syms :75); MT = the B
   core's own lib/B/YCbp.v:18 ameter_triv; XL = lib/B/UciBFacts.v uci_XL0 (fun _ => 0); RLO = 0x96bc8
   (lib/B/YB1w.v:17, the second disjunct of lib/B/YCeg.v:50-52 in_ro_tfa); RHI = 0x97e20 (lib/B/YB1w.v:18); SK / KS =
   the B core's sink head and record lib/B/YE2k.v tfib_sink_head / tfib_K. *)
Local Notation segs := UBT.ucisegsB0.
Local Notation B := BD2l.UciB.
Local Notation MT := BCbp.ameter_triv.
Local Notation XL := BF.uci_XL0.
Local Notation RLO := 0x96bc8.
Local Notation RHI := 0x97e20.
Local Notation SK := BE2k.tfib_sink_head.
Local Notation KS := BE2k.tfib_K.
Lemma RO_IN : forall a, RLO <= a < RHI -> BCeg.in_ro_tfa a.
Proof. intros a H. right. exact H. Qed.
Lemma MT_FREE : forall S m, mo_ok MT S m.
Proof. intros S m. exact I. Qed.
Module LLVMFW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LLVMFuzzerTestOneInput_cgW.
Section asan_ubsan.

(* ===================================================================================================== *)
(* The 18 rows of the block, in image A's order.                                                          *)
(* ===================================================================================================== *)

(* The walk of LLVMFuzzerTestOneInput (0x7f2e8): lib/B/Prog/LLVMFuzzerTestOneInput_cgW.v uci_llvmf_holds (824090cba246). *)
Definition H_PROG_LLVMF : forall (rc : YM05.RunCeil), @PL.uci_llvmf_holds_stmt rc B MT XL RLO RHI := fun rc => @LLVMFW.uci_llvmf_holds rc B MT XL RLO RHI.
(* The walk of check_no_overread (0x7f56c), caller-journal form, at the caller's context: lib/B/Prog/
   check_no_overread_cgW.v uci_check_no_overread_cg_holds (e61d8b88c3d0) at UciB, ameter_triv and that context. *)
Definition H_PROG_CNO : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PN.uci_check_no_overread_cg_holds_stmt fx rc
  B MT PL.CTX_check_no_overread := fun fx rc => @CNOW.uci_check_no_overread_cg_holds fx rc B MT PL.CTX_check_no_overread.
(* The walk of check_value (0x7f6b0), caller-journal form: lib/B/Prog/check_value_cgW.v uci_check_value_cg_holds (faf4885cf4dd). *)
Definition H_PROG_CV : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PV.uci_check_value_cg_holds_stmt fx rc B MT := fun fx rc => @CVW.uci_check_value_cg_holds fx rc B MT.
(* The walk of check_clamp (0x7f950), caller-journal form: lib/B/Prog/check_clamp_cgW.v uci_check_clamp_cg_holds (e5e90545d4c8). *)
Definition H_PROG_CC : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PK.uci_check_clamp_cg_holds_stmt fx rc B MT := fun fx rc => @OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_clamp_cgW.uci_check_clamp_cg_holds fx rc B MT.
(* The walk of rp_uci_int (0x7ffd4), realizes form: lib/B/Prog/rp_uci_int_cgW.v uci_rp_uci_int_holds (d3f024dc2e5). *)
Definition H_PROG_RUI : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PR.uci_rp_uci_int_holds_stmt fx rc B := fun fx rc => @RUIW.uci_rp_uci_int_holds fx rc B.
(* The footprint walk of the leaf rp_hot_clamp (0x7fd38): lib/B/Prog/rp_hot_clamp_FW.v rp_hot_clamp_holds_F
   (783ed4e623d); its translation to the leaf form is lib/B/Prog/rp_hot_clamp_cg.v uci_rp_hot_clamp_cg_of_F. *)
Definition H_PROG_RHC_F : PH.rp_hot_clamp_contract_F := RHCW.rp_hot_clamp_holds_F.

(* The class-1 fake stack (check_clamp's one call, 0x7f9b4 -> 0x3c1b8); the predicate is
   lib/Reusable/YG0d.v:286 at cid 1, of which the core proves no instance (it is only a premise at lib/B/YCbq.v:1749 and
   a record field at lib/Reusable/YG0d.v:537). lib/B/Rt/YF0s.v:516 stack_malloc1_contract (forall B, AR_laws tfibsegs B
   -> UciSyms B -> astack_malloc_realizes tfibsegs B 1; gate record provenance/evidence/stackmalloc1-B, commit
   51cfb939a547) applied at UciB with lib/Reusable/YG0q.v:805 AR_laws_ok and
   lib/B/YD2l.v:75 UciB_syms: stack_malloc reads no trace or .got field beyond UciSyms, so YF0s's abstract form
   applied at UciB suffices. *)
Lemma H_RT_STACK_MALLOC1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 1.
Proof. intros rc fx. exact (@BF0s.stack_malloc1_contract fx rc B (AR_laws_ok tfibsegs B) BD2l.UciB_syms). Qed.
(* The memchr interceptor with c = '\n' (rp_uci_int's call, 0x80020 -> the trampoline 0x4107c):
   lib/B/Rt/Memchr.v memchr_icpt_contract (forall B, AR_laws tfibsegs B -> UciSyms B -> amemchr_realizesM tfibsegs B
   0x10350 0x10370 0x4107c; commit 43a6893892d7, records provenance/evidence/memchr-B) applied at UciB; the trampoline is
   UAddr.uci_sigma US___interceptor_trampoline_memchr = 0x4107c by computation. *)
Lemma H_RT_MEMCHR : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @MD.amemchr_realizesM fx rc segs B 0x10350 0x10370 (UAddr.uci_sigma US___interceptor_trampoline_memchr).
Proof. intros rc fx. exact (@BMc.memchr_icpt_contract fx rc B (AR_laws_ok tfibsegs B) BD2l.UciB_syms). Qed.

(* The kit rows: lib/B/Prog/LeafCgClose.v (LeafCgFacts.v / LeafCgGlue.v, from fuzz_decode's released lib/B at
   88154566652a). *)
Lemma H_KIT_AVIEW_EXT : @LK.aview_ext_stmt (aview segs).
Proof. exact BLC.H_KIT_AVIEW_EXT. Qed.
Lemma H_KIT_AVIEW_SOME : @LK.aview_some_stmt (aview segs).
Proof. exact BLC.H_KIT_AVIEW_SOME. Qed.
Lemma H_LEAF_GLUE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview segs) -> @LK.aview_some_stmt (aview segs) ->
  @PCs.uci_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof. exact BLC.H_LEAF_GLUE. Qed.

(* The computed rows: lib/B/UciBFacts.v (computation at UciB). *)
Lemma HB_CELLS : @PCs.uci_cells B.
Proof. exact BF.HB_CELLS. Qed.
Lemma HB_RO_RD_UNOWNED : PCs.uci_ro_rd_unowned B.
Proof. exact BF.HB_RO_RD_UNOWNED. Qed.
Lemma HB_ROM_NO_ERRNO : PCs.uci_rom_no_errno B.
Proof. exact BF.HB_ROM_NO_ERRNO. Qed.
Lemma HB_CNO_UCTX : @PN.uci_cno_uctx B PL.CTX_check_no_overread.
Proof. exact BF.HB_CNO_UCTX. Qed.
Lemma HB_CNO_UFIX : @PN.uci_cno_ufix B.
Proof. exact BF.HB_CNO_UFIX. Qed.
Lemma HB_CV_UFIX : @PV.uci_cv_ufix B.
Proof. exact BF.HB_CV_UFIX. Qed.
Lemma HB_COST : forall n, 0 <= n -> @PL.uci_llvmf_cost MT n <= XL n.
Proof. exact BF.HB_COST. Qed.

(* ===================================================================================================== *)
(* CORE lemmas, each one `exact` (or a short proof) of a landed core lemma at UciB.                       *)
(* ===================================================================================================== *)
(* H_RT_MALLOC / H_RT_FREE: lib/B/UciBRtAlloc.v:18 uciB_MALLOC / :21 uciB_FREE (lib/B/YF0w.v:45 / lib/B/YF0q.v:11 at
   UciB; record provenance/evidence/uci-b-alloc, commit 81e5b92bbab3). H_RT_MEMCPY_WRAP: lib/B/YD2m.v:17 tfib_AICPY.
   H_RT_ASAN_MEMCPY: lib/B/YE2q.v:146 asan_memcpy_realizes at __asan_memcpy 0x50674, one site-agnostic contract for the
   four harness sites 0x7f5d8, 0x7f5e8, 0x7f708, 0x7fa64 (record provenance/evidence/uci-b-memcpy, commit
   7af39d3f61cc). *)
Lemma H_RT_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. intros rc fx. exact (BAl.uciB_MALLOC fx rc). Qed.
Lemma H_RT_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. intros rc fx. exact (BAl.uciB_FREE fx rc). Qed.
Lemma H_RT_MEMCPY_WRAP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. intros rc fx. exact (@BD2m.tfib_AICPY fx rc B BD2l.UciB_syms). Qed.
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (UAddr.uci_sigma US___asan_memcpy).
Proof. intros rc fx. exact (@BE2q.asan_memcpy_realizes fx rc B (AR_laws_ok tfibsegs B) BD2l.UciB_syms). Qed.
(* HB_PC_WRAP_MALLOC / _FREE / HB_PC_STACK_MALLOC1: lib/B/YF0l.v:12-14 (0x51788 / 0x51784 / 0x3c1b8), by
   computation. *)
Lemma HB_PC_WRAP_MALLOC : pc_wrap_malloc (as_code B) = UAddr.uci_sigma US___interceptor_trampoline_malloc.
Proof. reflexivity. Qed.
Lemma HB_PC_WRAP_FREE : pc_wrap_free (as_code B) = UAddr.uci_sigma US___interceptor_trampoline_free.
Proof. reflexivity. Qed.
Lemma HB_PC_STACK_MALLOC1 : pc_stack_malloc (as_code B) 1 = UAddr.uci_sigma US___asan_stack_malloc_1.
Proof. reflexivity. Qed.
(* HB_UNIVERSE_OK: lib/B/YF0m.v:309 ts_universe at UciB_syms. HB_MODEL_LAWS: lib/Reusable/YG05.v:140 model_laws_ok. *)
Lemma HB_UNIVERSE_OK : universe_ok (as_universe B).
Proof. exact (ts_universe B BD2l.UciB_syms). Qed.
Lemma HB_MODEL_LAWS : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) HB_UNIVERSE_OK). Qed.
(* HB_METER_LAWS / HB_METER_FS_LAWS: lib/B/YCbp.v:23 ameter_triv_laws / :25 ameter_triv_fs_laws. *)
Lemma HB_METER_LAWS : ameter_laws MT.
Proof. exact BCbp.ameter_triv_laws. Qed.
Lemma HB_METER_FS_LAWS : ameter_fs_laws MT.
Proof. exact BCbp.ameter_triv_fs_laws. Qed.
(* HB_SMP / HB_ASF / HB_FFL: lib/Reusable/YG05.v:71 stack_malloc_progress, lib/Reusable/YG0t.v:475
   astack_free_law_ok, and AR_laws' al_flag / al_client_img with the image cover (lib/B/Prog/UciPImg.v uci_img_cover),
   as fuzz_grant's released lib/B/GrantBCloseInst.v grantB_SMP / grantB_ASF / grantB_FFL. *)
Lemma HB_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma HB_ASF : forall (rc : YM05.RunCeil), astack_free_law segs B.
Proof. intros rc. exact (astack_free_law_ok _ B). Qed.
Lemma HB_FFL : forall (rc : YM05.RunCeil), frame_flag_lawP segs B.
Proof.
  intros rc ly S W mem md cid pos HAR Hin.
  destruct (al_flag _ _ (AR_laws_ok tfibsegs B) ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
  destruct (al_client_img _ _ (AR_laws_ok tfibsegs B) ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
  { right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
  pose proof HAR as (M & L & _).
  assert (LO : layout_ok ly) by (destruct M; assumption).
  pose proof (BImg.uci_img_cover ly S md LO L) as [C1 C2].
  destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
  split; [exact Hp|]. split; [exact Ho|]. split.
  - split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
  - split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* HB_SINK_IMG_LAWS: lib/B/YD1u.v:45 tfib_AIL at UciB. HB_SINK_KEPT / HB_META_KEPT: lib/B/YE01.v:86 asink_none_kept /
   :157 ameta_inv_kept, specialised to one journal step, as the entry's statement takes them. *)
Lemma HB_SINK_IMG_LAWS : @asink_img_laws SK segs B KS.
Proof. exact (BD1u.tfib_AIL B BD2l.UciB_syms). Qed.
Lemma HB_SINK_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    asink_none segs KS (mrestrict (w_H W0) mem0) md0 -> asink_none segs KS (mrestrict (w_H W') mem') md'.
Proof.
  intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ HFP HN.
  exact (BE01.asink_none_kept segs B KS HB_SINK_IMG_LAWS STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ HFP HN).
Qed.
Lemma HB_META_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ameta_inv segs KS ly (mrestrict (w_H W0) mem0) M -> ameta_inv segs KS ly' (mrestrict (w_H W') mem') M.
Proof.
  intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM.
  exact (BE01.ameta_inv_kept segs B KS HB_SINK_IMG_LAWS STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM).
Qed.
(* HB_API_ENV / HB_RO_BELOW_OFL: lib/B/UciBFacts.v (computation at UciB; the class of lib/B/Prog/PaBase.v). *)
Lemma HB_API_ENV : api_env segs B.
Proof. exact BF.HB_API_ENV. Qed.
Lemma HB_RO_BELOW_OFL : @PB.ro_below_ofl segs RLO RHI SK.
Proof. exact BF.HB_RO_BELOW_OFL. Qed.
(* H_LINK_MALLOC04 / H_LINK_FREE04: the call-rule form a program walk consumes, lib/B/YCbp.v:31 amalloc04_rule_triv /
   :40 afree04_rule_triv, at the image's segments (lib/B/Prog/UciPImg.v uci_segs_low), HB_API_ENV, AR_laws_ok and
   HB_MODEL_LAWS. *)
Lemma H_LINK_MALLOC04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @amalloc_realizes fx rc segs B -> @amalloc04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AM. apply (BCbp.amalloc04_rule_triv (SK := SK) segs B).
  - exact BImg.uci_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AM.
Qed.
Lemma H_LINK_FREE04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree_realizes fx rc segs B -> @afree04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AF. apply (BCbp.afree04_rule_triv (SK := SK) segs B).
  - exact BImg.uci_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AF.
Qed.

(* ===================================================================================================== *)
(* The composition: the callee contracts give the slot lib/B/YCfn.v:140, which the closed walk takes.      *)
(* ===================================================================================================== *)
Section RC. Context {rc : YM05.RunCeil}.

(* The leaf rp_hot_clamp, from its PROVED translation (lib/B/Prog/rp_hot_clamp_cg.v uci_rp_hot_clamp_cg_of_F) over the
   kit's generic translation H_LEAF_GLUE, applied to its footprint contract H_PROG_RHC_F. *)
Lemma LEAF_HOT_CLAMP : forall fx : YK11.FPState, @PCs.uci_leaf_wr_at rc B (@LHC.uci_rp_hot_clamp_cg) fx.
Proof.
  intros fx. exact (@LHC.uci_rp_hot_clamp_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_RHC_F).
Qed.
Lemma RUI_HOLDS : forall fx : YK11.FPState, @PR.uci_rp_uci_int_cg fx rc B (UAddr.uci_sigma US_rp_uci_int).
Proof.
  intros fx. apply (H_PROG_RUI fx rc).
  - exact HB_CELLS.
  - apply AR_laws_ok.
  - exact HB_ROM_NO_ERRNO.
  - intros fx'. exact (H_RT_MEMCHR rc fx').
Qed.
Lemma CNO_HOLDS : forall fx : YK11.FPState,
  @PN.uci_check_no_overread_cg fx rc B MT (UAddr.uci_sigma US_check_no_overread) PL.CTX_check_no_overread.
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
Lemma CV_HOLDS : forall fx : YK11.FPState, @PV.uci_check_value_cg fx rc B MT (UAddr.uci_sigma US_check_value).
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
Lemma CC_HOLDS : forall fx : YK11.FPState, @PK.uci_check_clamp_cg fx rc B MT (UAddr.uci_sigma US_check_clamp).
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
(* The slot of the entry function, from its walk and every callee it names. *)
Lemma LIB_CONTRACT : @BCfn.tfib_lib_contract_x_all rc checksum_shape B MT XL XL RLO RHI.
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

Lemma uci_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS:=checksum_shape) inp).
Proof.
  exact (@BD1q.tfib_srealizesX rc B BD2l.UciB_syms
    (BAl.uciB_MALLOC YK11.fx0 rc) (BAl.uciB_FREE YK11.fx0 rc)
    (BD2m.tfib_AICPY B BD2l.UciB_syms) (BD2m.tfib_ARDCHK B BD2l.UciB_syms)
    MT XL XL RLO RHI MT_FREE RO_IN LIB_CONTRACT
    BD1k.xst BD1k.tfib_xst_frame
    (BD1o.tfib_printf_first B BD2l.UciB_syms (AR_laws_ok tfibsegs B) BD2l.UciB_syms)
    (BD1o.tfib_printf_next B BD2l.UciB_syms (AR_laws_ok tfibsegs B) BD2l.UciB_syms)
    BD1k.est BD1k.tfib_est_img BD1k.tfib_est_frame
    (BD1k.tfib_fwrite_site B BD2l.UciB_syms (AR_laws_ok tfibsegs B))
    (BD1k.tfib_refused_site B BD2l.UciB_syms (AR_laws_ok tfibsegs B) BD2l.UciB_syms)
    (BD1l.tfib_fprintf_open_site B BD2l.UciB_syms (AR_laws_ok tfibsegs B) BD2l.UciB_syms)
    (BD1l.tfib_fprintf_rderr_site B BD2l.UciB_syms (AR_laws_ok tfibsegs B) BD2l.UciB_syms)
    (BD1l.tfib_fprintf_usage_site B BD2l.UciB_syms (AR_laws_ok tfibsegs B) BD2l.UciB_syms)
    (BD1j.tfib_exit_site B BD2l.UciB_syms (AR_laws_ok tfibsegs B))).
Qed.
End RC.

Theorem uci_B_TFIB_T_of_parts : UBT.TFIB_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@uci_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowU sp Hsp)) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan+UBSan statements of record, given only the named parts above. *)
Theorem uci_asan_ubsan_agrees_of_parts : USt.asan_ubsan_agrees.
Proof. exact (uci_asan_ubsan_agrees_of_tfib uci_B_TFIB_T_of_parts). Qed.
Theorem uci_asan_ubsan_halts_of_parts : USt.asan_ubsan_halts.
Proof. exact (uci_asan_ubsan_halts_of_tfib uci_B_TFIB_T_of_parts). Qed.

About uci_B_TFIB_T_of_parts.
Print Assumptions uci_B_TFIB_T_of_parts.
About uci_asan_ubsan_agrees_of_parts.
Print Assumptions uci_asan_ubsan_agrees_of_parts.
About uci_asan_ubsan_halts_of_parts.
Print Assumptions uci_asan_ubsan_halts_of_parts.
Print Assumptions LIB_CONTRACT.
Print Assumptions H_RT_MEMCHR.
Print Assumptions H_RT_STACK_MALLOC1.
Print Assumptions H_LEAF_GLUE.
Print Assumptions HB_CELLS.
Print Assumptions HB_FFL.
End asan_ubsan.
