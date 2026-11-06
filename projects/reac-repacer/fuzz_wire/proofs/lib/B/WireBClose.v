(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD1q.v (tfib_srealizesX),
   lib/YB1n.v (tfib_startup_T1, HS_ok) and lib/YD2o.v (TFIB_TB_of_partsXF), in the form of fuzz_pcap's closing side
   (proofs/libreac/fuzz_pcap/lib/A/PcapClose.v in a version before its release, sha256 8881c977fa66, not in the published tree; at recipes commit 88154566652a that file has no Section hypothesis left), for libreac/fuzz_decode's
   ASan+UBSan image: one named Section hypothesis per remaining part, module paths and names changed. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v at 25e3d17bdb50 for fuzz_decode's lib/A/AsanTop.v (recipes commit 88154566652a), by way of fuzz_grant's lib/A/AsanTop.v at 4f87de75d67: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v at 88154566652a builds it for the ubsan agreement, with the plain slot contract of its lib/Prog/LLVMFuzzerTestOneInput_gfr.v at 88154566652a, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: adapted from lib/A/GrantTop.v for image B (fuzz_grant.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_decode/lib/B/DecodeBClose.v and lib/A/AsanTop.v
   (Section b) at recipes commit 88154566652a and proofs/libreac/fuzz_grant/lib/B/GrantBTop.v at recipes commit
   4f87de75d67, for reac-repacer/fuzz_uci's ASan+UBSan image (fuzz_uci.asan-ubsan): the image-B core's closed walk
   lib/B/YD1q.v tfib_srealizesX takes the place of the donor's H_STARTUP / H_DRIVER pair; its slot lib/B/YCfn.v:140 is
   LIB_CONTRACT, composed from the six program walk statements of lib/B/Prog and their callees' contracts; one named
   Section hypothesis per program walk; the runtime, kit and computed rows are Lemmas citing lib/B/Rt, lib/B/Prog/
   LeafCgClose.v and lib/B/UciBFacts.v; the read-only range 0x96bc8 .. 0x97e20 and the memchr window 0x10350 ..
   0x10370 are image B's; module paths and names changed. *)
(* WireBClose: made from reac-repacer/fuzz_uci's lib/B/UciBClose.v (recipes commit
   0295462466b2; itself made from proofs/libreac/fuzz_decode/lib/B/DecodeBClose.v and lib/A/AsanTop.v at recipes commit
   88154566652a and proofs/libreac/fuzz_grant/lib/B/GrantBTop.v) for reac-repacer/fuzz_wire's ASan+UBSan image
   (fuzz_wire.asan-ubsan): the image-B core's closed walk lib/B/YD1q.v tfib_srealizesX takes the place of a start-up /
   driver pair; its slot lib/B/YCfn.v:140 is LIB_CONTRACT, composed from the program statements of lib/B/Prog and their
   callees' contracts; one row per program walk (H_PROG_<TAG> for a function in the caller-journal or realizes form,
   H_PROG_<TAG>_F for a leaf's footprint walk) and the two class contracts of __asan_stack_malloc_0 / _1; the runtime,
   kit and computed rows are Lemmas citing lib/B/WireBRtAlloc.v, lib/B/YD2m.v, lib/B/YE2q.v, lib/B/YE2s.v,
   lib/B/Rt/Memmove.v, lib/B/Prog/LeafCgClose.v and lib/B/WireBFacts.v; the read-only range 0x98318 .. 0x99570 is image
   B's; module paths and names changed. *)
(* The image-B composition of fuzz_wire's two ASan+UBSan statements (proves no function). Image A's twin is
   lib/A/WireClose.v. Every row and lemma is stated at the concrete record B := WireB (lib/B/YD2l.v:17).
   Every row is a Lemma citing a landed proof: the 21 program walks of image B (LLVMFuzzerTestOneInput, the eight
   checks, the realizes-form rp_copy_untag and the leaves' footprint walks) and the runtime, kit, computed and core rows
   (the class-0 / class-1 stack_malloc contracts among them). No Section hypothesis remains: the tops
   wire_asan_ubsan_agrees_of_parts and wire_asan_ubsan_halts_of_parts are closed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_wire Require Statements Images.
From OSSVerify.reac_repacer.fuzz_wire.images Require Plain.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB12 YB1h YB01 YB1n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG0q YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YC5d YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import ZTraceSpec WireAsanShared.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require WireHaltsSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YF0m YCeg YD1v YD1w YD1x YD1i YCfn YD1p.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YM09 YK0o HaltsKitB.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require WireBTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YD1q YD2l WireBRtAlloc YD2m YD1k YD1o YD1l YD1j YE2q YE2s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Rt Require MemmoveDef Memmove StackMalloc0 YF0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Module WBT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.WireBTFIB.
Module BD2l := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD2l.
Module BD1q := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD1q.
Module BAl := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.WireBRtAlloc.
Module BD2m := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD2m.
Module BD1k := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD1k.
Module BD1o := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD1o.
Module BD1l := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD1l.
Module BD1j := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD1j.
Module BE2q := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YE2q.
Module BE2s := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YE2s.
Module BCbp := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YCbp.
Module BCeg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YCeg.
Module BCfn := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YCfn.
Module BMd := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Rt.MemmoveDef.
Module BMm := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Rt.Memmove.
Module BSm0 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Rt.StackMalloc0.
Module BSm1 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Rt.YF0s.
Module USt := OSSVerify.reac_repacer.fuzz_wire.Statements.
Module UIm := OSSVerify.reac_repacer.fuzz_wire.Images.
Module UPl := OSSVerify.reac_repacer.fuzz_wire.images.Plain.
Module UHS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.WireHaltsSpec.
Module LK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgFacts.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require WirePAddr WirePImg WireCg PaBase LeafCgClose.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LLVMFuzzerTestOneInput_cg check_forward_cg
  check_ret_cg check_downstream_cg check_meter_cg check_counter_cg check_width_cg check_read_cg check_copy_cg
  rp_copy_untag_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_fwd_class_F_c rp_fwd_class_cg
  rp_ret_accept_F_c rp_ret_accept_cg rp_ds_accept_F_c rp_ds_accept_cg rp_meter_counter_F_c rp_meter_counter_cg
  rp_counter_F_c rp_counter_cg rp_counter_FW rp_ret_accept_FW rp_frame_channels_F_c rp_frame_channels_cg
  rp_frame_channels_F
  rp_slot_width_F_c rp_slot_width_cg
  rp_slot_read_F_c rp_slot_read_cg reac_frame_is_reac_F_nosh reac_frame_is_reac_cg reac_frame_clean_len_F_c
  reac_frame_clean_len_F reac_frame_clean_len_cg is_tagged_reac_F_c is_tagged_reac_cg is_tagged_reac_F rp_fwd_class_FW
  check_width_cgW rp_meter_counter_FW check_forward_cgW check_counter_cgW check_ret_cgW rp_copy_untag_cgW check_copy_cgW
  check_meter_cgW LLVMFuzzerTestOneInput_walk rp_slot_width_F rp_slot_read_F rp_ds_accept_FW check_downstream_cgW
  check_read_cgW.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require WireBFacts YE2k YE01 YD1u.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG05 YG0t YE00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
Module PL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LLVMFuzzerTestOneInput_cg.
Module WL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LLVMFuzzerTestOneInput_walk.
Module PCF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_forward_cg.
Module WCF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_forward_cgW.
Module PCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_ret_cg.
Module WCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_ret_cgW.
Module PCD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_downstream_cg.
Module WCD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_downstream_cgW.
Module PCM := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_meter_cg.
Module WCM := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_meter_cgW.
Module PCN := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_counter_cg.
Module WCN := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_counter_cgW.
Module PCW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_width_cg.
Module WCW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_width_cgW.
Module PCRd := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_read_cg.
Module WCRd := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_read_cgW.
Module PCC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_copy_cg.
Module WCC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_copy_cgW.
Module PRU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_copy_untag_cg.
Module WRU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_copy_untag_cgW.
Module FFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_fwd_class_F_c.
Module LFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_fwd_class_cg.
Module WFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_fwd_class_FW.
Module FRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ret_accept_F_c.
Module LRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ret_accept_cg.
Module WRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ret_accept_FW.
Module FDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ds_accept_F_c.
Module LDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ds_accept_cg.
Module WDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ds_accept_FW.
Module FMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_meter_counter_F_c.
Module LMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_meter_counter_cg.
Module WMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_meter_counter_FW.
Module FRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_counter_F_c.
Module LRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_counter_cg.
Module WRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_counter_FW.
Module FFH := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_frame_channels_F_c.
Module LFH := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_frame_channels_cg.
Module WFH := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_frame_channels_F.
Module FSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_width_F_c.
Module LSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_width_cg.
Module WSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_width_F.
Module FSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_read_F_c.
Module LSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_read_cg.
Module WSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_read_F.
Module FIRn := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_is_reac_F_nosh.
Module LIR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_is_reac_cg.
Module FCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_clean_len_F_c.
Module LCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_clean_len_cg.
Module WCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_clean_len_F.
Module FIT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_F_c.
Module LIT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_cg.
Module WIT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_F.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WireCg.
Module WAddr := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WirePAddr.
Module BImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WirePImg.
Module PB := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.PaBase.
Module BLC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgClose.
Module BF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.WireBFacts.
Module BE2k := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YE2k.
Module BE01 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YE01.
Module BD1u := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YD1u.
(* The guard, as image A's lib/A/WireClose.v: the plain build's sink hints are out of the way, so no `{SK}` can be
   filled with the plain build's head. *)
#[local] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink : typeclass_instances.
(* What a bare `sink_head` resolves to in this file: the ASan+UBSan image's own head (lib/B/YE2k.v:37). *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = BE2k.tfib_sink_head.
Proof. reflexivity. Qed.

(* ===================================================================================================== *)
(* The two ASan+UBSan statements from TFIB_T (decode lib/A/AsanTop.v Section b, at fuzz_wire's names): the *)
(* plain side, the budget orderings and SPECX_shape_ok are the shared files' (lib/WireAsanShared.v,        *)
(* lib/A/WireHaltsSpec.v, both free of image-A files).                                                    *)
(* ===================================================================================================== *)
Section b.
Hypothesis TFIBB : WBT.TFIB_T.

Theorem wire_asan_ubsan_agrees_of_tfib : USt.asan_ubsan_agrees.
Proof.
  unfold USt.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (wire_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold UIm.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    UPl.M.loaded_segments UPl.M.init_pc UPl.M.phdrs sp brk mb rnd
    WBT.wiresegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=checksum_shape) inp) (SPECX (LS:=checksum_shape) inp) inp
    asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem wire_asan_ubsan_halts_of_tfib : USt.asan_ubsan_halts.
Proof.
  unfold USt.asan_ubsan_halts, UIm.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage WBT.wiresegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused WBT.wiresegsB0 AsanUbsan.M.init_pc
    AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (UHS.SPECX_shape_ok inp).
Qed.
End b.
(* The stack-pointer window, from valid_sp (decode lib/B/DecodeBClose.v valid_sp_windowD). *)
Lemma valid_sp_windowW : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
(* The values the core's closed walk and the rows are stated at; no Section Variable. segs =
   AsanUbsan.M.loaded_segments (= lib/B/YB1v.v tfibsegs); B = lib/B/YD2l.v:17 WireB (WireB_syms :75); MT = the B
   core's own lib/B/YCbp.v:19 ameter_triv; XL = lib/B/WireBFacts.v wire_XL0 (fun _ => 0); RLO = 0x98318
   (lib/B/YB1w.v:17 tfib_data_rel_ro_lo, the second disjunct of lib/B/YCeg.v:50-52 in_ro_tfa); RHI = 0x99570
   (lib/B/YB1w.v:18 tfib_got_hi); SK / KS = the B core's sink head and record lib/B/YE2k.v tfib_sink_head / tfib_K. *)
Local Notation segs := WBT.wiresegsB0.
Local Notation B := BD2l.WireB.
Local Notation MT := BCbp.ameter_triv.
Local Notation XL := BF.wire_XL0.
Local Notation RLO := 0x98318.
Local Notation RHI := 0x99570.
Local Notation SK := BE2k.tfib_sink_head.
Local Notation KS := BE2k.tfib_K.
Lemma RO_IN : forall a, RLO <= a < RHI -> BCeg.in_ro_tfa a.
Proof. intros a H. right. exact H. Qed.
Lemma MT_FREE : forall S m, mo_ok MT S m.
Proof. intros S m. exact I. Qed.
(* ===================================================================================================== *)
(* The program walks of image B, each a Lemma citing its landed walk.                                     *)
(* ===================================================================================================== *)

(* rp_ret_accept (0x80ee0) and rp_counter (0x81314): their footprint walks are landed, lib/B/Prog/rp_ret_accept_FW.v:39
   rp_ret_accept_holds_F and lib/B/Prog/rp_counter_FW.v:44 rp_counter_holds_F. *)
Lemma H_PROG_RRET_F : FRA.rp_ret_accept_contract_F.
Proof. exact WRA.rp_ret_accept_holds_F. Qed.
Lemma H_PROG_RCNT_F : FRC.rp_counter_contract_F.
Proof. exact WRC.rp_counter_holds_F. Qed.
(* reac_frame_is_reac (0x8183c): the no-shadow footprint contract its proved translation takes (lib/B/Prog/
   reac_frame_is_reac_cg.v wire_reac_frame_is_reac_cg_of_F), as fuzz_decode's lib/B/DecodeBClose.v takes it; its walk
   is landed, relocated from fuzz_decode's released image-B walk: lib/B/Prog/reac_frame_is_reac_F_nosh.v:61
   reac_frame_is_reac_holds_F_nosh. *)
Lemma H_PROG_RISR_F : FIRn.reac_frame_is_reac_contract_F_nosh.
Proof. exact FIRn.reac_frame_is_reac_holds_F_nosh. Qed.
(* is_tagged_reac (0x8103c) and rp_fwd_class (0x80d9c): their footprint walks are landed, lib/B/Prog/is_tagged_reac_F.v:117
   is_tagged_reac_holds_F and lib/B/Prog/rp_fwd_class_FW.v:153 rp_fwd_class_holds_F. *)
Lemma H_PROG_ITR_F : FIT.is_tagged_reac_contract_F.
Proof. exact WIT.is_tagged_reac_holds_F. Qed.
Lemma H_PROG_RFWD_F : FFC.rp_fwd_class_contract_F.
Proof. exact WFC.rp_fwd_class_holds_F. Qed.
(* check_width (0x8057c): its walk is landed, lib/B/Prog/check_width_cgW.v:840 wire_check_width_holds. *)
Lemma H_PROG_CWID : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCW.wire_check_width_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (@WCW.wire_check_width_holds fx rc B MT). Qed.
(* reac_frame_clean_len (0x818e8): its footprint walk is landed, relocated from fuzz_decode's released image-B walk:
   lib/B/Prog/reac_frame_clean_len_F.v:17 reac_frame_clean_len_holds_F. *)
Lemma H_PROG_RCLN_F : FCL.reac_frame_clean_len_contract_F.
Proof. exact WCL.reac_frame_clean_len_holds_F. Qed.
(* rp_frame_channels (0x813a0): its footprint walk is landed, lib/B/Prog/rp_frame_channels_F.v:139
   rp_frame_channels_holds_F (reac_frame_clean_len's footprint contract gives rp_frame_channels'), applied to
   H_PROG_RCLN_F. *)
Lemma H_PROG_RFCH_F : FFH.rp_frame_channels_contract_F.
Proof. exact (WFH.rp_frame_channels_holds_F H_PROG_RCLN_F). Qed.
(* rp_meter_counter (0x81144): its footprint walk is landed, lib/B/Prog/rp_meter_counter_FW.v:539
   rp_meter_counter_holds_F. *)
Lemma H_PROG_RMET_F : FMC.rp_meter_counter_contract_F.
Proof. exact WMC.rp_meter_counter_holds_F. Qed.
(* check_forward (0x7fda4), check_ret (0x7ff2c) and check_counter (0x804c0): their walks are landed,
   lib/B/Prog/check_forward_cgW.v:522 wire_check_forward_cg_holds, lib/B/Prog/check_ret_cgW.v:657
   wire_check_ret_cg_holds and lib/B/Prog/check_counter_cgW.v:716 wire_check_counter_cg_holds. *)
Lemma H_PROG_CFWD : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCF.wire_check_forward_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (@WCF.wire_check_forward_cg_holds fx rc B MT). Qed.
Lemma H_PROG_CRET : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCR.wire_check_ret_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (@WCR.wire_check_ret_cg_holds fx rc B MT). Qed.
Lemma H_PROG_CCNT : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCN.wire_check_counter_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (@WCN.wire_check_counter_cg_holds fx rc B MT). Qed.
(* rp_copy_untag (0x81414), realizes form (it calls __asan_memmove): its walk is landed,
   lib/B/Prog/rp_copy_untag_cgW.v:1049 wire_rp_copy_untag_holds. *)
Lemma H_PROG_RCPY : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PRU.wire_rp_copy_untag_holds_stmt fx rc B.
Proof. intros fx rc. exact (@WRU.wire_rp_copy_untag_holds fx rc B). Qed.
(* check_copy (0x80abc): its walk is landed, lib/B/Prog/check_copy_cgW.v:21 wire_check_copy_cg_holds. *)
Lemma H_PROG_CCPY : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCC.wire_check_copy_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (@WCC.wire_check_copy_cg_holds fx rc B MT). Qed.
(* check_meter (0x8016c): its walk is landed, lib/B/Prog/check_meter_cgW.v:1497 wire_check_meter_holds. *)
Lemma H_PROG_CMET : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCM.wire_check_meter_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (@WCM.wire_check_meter_holds fx rc B MT). Qed.
(* LLVMFuzzerTestOneInput (0x7fbf8), the slot form: its walk is landed, lib/B/Prog/LLVMFuzzerTestOneInput_walk.v:21
   wire_llvmf_holds. *)
Lemma H_PROG_LLVMF : forall (rc : YM05.RunCeil), @PL.wire_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof. intros rc. exact (@WL.wire_llvmf_holds rc B MT XL RLO RHI). Qed.
(* rp_slot_width (0x8151c) calls rp_frame_channels: its walk's statement is a chain (lib/B/Prog/rp_slot_width_F_c.v
   rp_slot_width_F_holds_stmt), landed as lib/B/Prog/rp_slot_width_F.v:70 rp_slot_width_holds_F and applied to
   rp_frame_channels' footprint contract below. *)
Lemma H_PROG_RSW_F : FSW.rp_slot_width_F_holds_stmt.
Proof. exact WSW.rp_slot_width_holds_F. Qed.
(* rp_slot_read (0x815ec) calls rp_slot_width: its walk's statement is a chain (lib/B/Prog/rp_slot_read_F_c.v
   rp_slot_read_F_holds_stmt), landed as lib/B/Prog/rp_slot_read_F.v:626 rp_slot_read_holds_F and applied to
   rp_slot_width's footprint contract below. *)
Lemma H_PROG_RSR_F : FSR.rp_slot_read_F_holds_stmt.
Proof. exact WSR.rp_slot_read_holds_F. Qed.
(* rp_ds_accept (0x80f84) tail-calls is_tagged_reac: its walk's statement (lib/B/Prog/rp_ds_accept_cg.v
   wire_rp_ds_accept_holds_stmt) is over is_tagged_reac's footprint contract; landed as lib/B/Prog/rp_ds_accept_FW.v:284
   rp_ds_accept_holds_F and applied to H_PROG_ITR_F below. *)
Lemma H_PROG_RDS_F : LDA.wire_rp_ds_accept_holds_stmt.
Proof. exact WDA.rp_ds_accept_holds_F. Qed.
(* check_downstream (0x7ffe8): its walk is landed, lib/B/Prog/check_downstream_cgW.v:647 wire_check_downstream_cg_holds. *)
Lemma H_PROG_CDS : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCD.wire_check_downstream_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (@WCD.wire_check_downstream_cg_holds fx rc B MT). Qed.
(* check_read (0x805f4): its walk is landed, lib/B/Prog/check_read_cgW.v:1424 wire_check_read_holds. *)
Lemma H_PROG_CRD : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @PCRd.wire_check_read_holds_stmt fx rc B MT.
Proof. intros fx rc. exact (WCRd.wire_check_read_holds fx rc B MT). Qed.

(* ===================================================================================================== *)
(* The class-0 / class-1 fake stack (check_meter's call 0x801d8 -> 0x3c524, check_read's call 0x80668 ->     *)
(* 0x3c698): lib/B/Rt/StackMalloc0.v:515 stack_malloc0_contract and lib/B/Rt/YF0s.v:515                    *)
(* stack_malloc1_contract (forall B, AR_laws tfibsegs B -> WireSyms B -> astack_malloc_realizes tfibsegs B   *)
(* c), applied at WireB with lib/Reusable/YG0q.v AR_laws_ok and lib/B/YD2l.v:75 WireB_syms.                 *)
(* ===================================================================================================== *)
Lemma H_RT_STACK_MALLOC0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 0.
Proof. intros rc fx. exact (@BSm0.stack_malloc0_contract fx rc B (AR_laws_ok tfibsegs B) BD2l.WireB_syms). Qed.
Lemma H_RT_STACK_MALLOC1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 1.
Proof. intros rc fx. exact (@BSm1.stack_malloc1_contract fx rc B (AR_laws_ok tfibsegs B) BD2l.WireB_syms). Qed.

(* ===================================================================================================== *)
(* The kit rows: lib/B/Prog/LeafCgClose.v.                                                                 *)
(* ===================================================================================================== *)
Lemma H_KIT_AVIEW_EXT : @LK.aview_ext_stmt (aview segs).
Proof. exact BLC.H_KIT_AVIEW_EXT. Qed.
Lemma H_KIT_AVIEW_SOME : @LK.aview_some_stmt (aview segs).
Proof. exact BLC.H_KIT_AVIEW_SOME. Qed.
Lemma H_LEAF_GLUE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview segs) -> @LK.aview_some_stmt (aview segs) ->
  @PCs.wire_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof. exact BLC.H_LEAF_GLUE. Qed.

(* ===================================================================================================== *)
(* The computed rows: lib/B/WireBFacts.v (computation at WireB).                                           *)
(* ===================================================================================================== *)
Lemma HB_CELLS : @PCs.wire_cells B.
Proof. exact BF.HB_CELLS. Qed.
Lemma HB_RO_RD_UNOWNED : PCs.wire_ro_rd_unowned B.
Proof. exact BF.HB_RO_RD_UNOWNED. Qed.
Lemma HB_ROM_NO_ERRNO : PCs.wire_rom_no_errno B.
Proof. exact BF.HB_ROM_NO_ERRNO. Qed.
Lemma HB_LLVMF_UFIX : @PL.wire_llvmf_ufix B.
Proof. exact BF.HB_LLVMF_UFIX. Qed.
Lemma HB_CC_UFIX : @PCC.wire_cc_ufix B.
Proof. exact BF.HB_CC_UFIX. Qed.
Lemma HB_COST : forall n, 0 <= n -> @PL.wire_llvmf_cost MT n <= XL n.
Proof. exact BF.HB_COST. Qed.

(* ===================================================================================================== *)
(* CORE lemmas, each one `exact` (or a short proof) of a landed core lemma at WireB.                      *)
(* ===================================================================================================== *)
(* H_RT_MALLOC / H_RT_FREE: lib/B/WireBRtAlloc.v:18 wireB_MALLOC / :21 wireB_FREE. H_RT_MEMCPY_WRAP: lib/B/YD2m.v:17
   tfib_AICPY. H_RT_ASAN_MEMCPY: lib/B/YE2q.v:146 asan_memcpy_realizes at __asan_memcpy 0x50c14 (site-agnostic).
   H_RT_BCMP: lib/B/YE2s.v:712 bcmp_icpt_contract at the bcmp trampoline 0x4155c (check_copy's call). H_RT_MEMMOVE:
   lib/B/Rt/Memmove.v:148 asan_memmove_contract at __asan_memmove 0x510b0 (rp_copy_untag's call). *)
Lemma H_RT_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. intros rc fx. exact (BAl.wireB_MALLOC fx rc). Qed.
Lemma H_RT_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. intros rc fx. exact (BAl.wireB_FREE fx rc). Qed.
Lemma H_RT_MEMCPY_WRAP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. intros rc fx. exact (@BD2m.tfib_AICPY fx rc B BD2l.WireB_syms). Qed.
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (WAddr.wire_sigma WS___asan_memcpy).
Proof. intros rc fx. exact (@BE2q.asan_memcpy_realizes fx rc B (AR_laws_ok tfibsegs B) BD2l.WireB_syms). Qed.
Lemma H_RT_BCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @abcmp_realizes fx rc segs B (WAddr.wire_sigma WS___interceptor_trampoline_bcmp).
Proof. intros rc fx. exact (@BE2s.bcmp_icpt_contract fx rc B (AR_laws_ok tfibsegs B) BD2l.WireB_syms). Qed.
Lemma H_RT_MEMMOVE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @BMd.amemmove_realizes fx rc segs B (WAddr.wire_sigma WS___asan_memmove).
Proof. intros rc fx. exact (@BMm.asan_memmove_contract fx rc B (AR_laws_ok tfibsegs B) BD2l.WireB_syms). Qed.
(* HB_PC_WRAP_MALLOC / _FREE / HB_PC_STACK_MALLOC0 / _1: lib/B/YF0l.v:12-14 (0x52098 / 0x52094 / 0x3c524 / 0x3c698),
   by computation. *)
Lemma HB_PC_WRAP_MALLOC : pc_wrap_malloc (as_code B) = WAddr.wire_sigma WS___interceptor_trampoline_malloc.
Proof. reflexivity. Qed.
Lemma HB_PC_WRAP_FREE : pc_wrap_free (as_code B) = WAddr.wire_sigma WS___interceptor_trampoline_free.
Proof. reflexivity. Qed.
Lemma HB_PC_STACK_MALLOC0 : pc_stack_malloc (as_code B) PCM.CM_CID = WAddr.wire_sigma WS___asan_stack_malloc_0.
Proof. reflexivity. Qed.
Lemma HB_PC_STACK_MALLOC1 : pc_stack_malloc (as_code B) PCRd.CRD_CID = WAddr.wire_sigma WS___asan_stack_malloc_1.
Proof. reflexivity. Qed.
(* HB_UNIVERSE_OK: lib/B/YF0m.v:293 ts_universe at WireB_syms. HB_MODEL_LAWS: lib/Reusable/YG05.v:140 model_laws_ok. *)
Lemma HB_UNIVERSE_OK : universe_ok (as_universe B).
Proof. exact (ts_universe B BD2l.WireB_syms). Qed.
Lemma HB_MODEL_LAWS : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) HB_UNIVERSE_OK). Qed.
(* HB_METER_LAWS / HB_METER_FS_LAWS: lib/B/YCbp.v:24 ameter_triv_laws / :26 ameter_triv_fs_laws. *)
Lemma HB_METER_LAWS : ameter_laws MT.
Proof. exact BCbp.ameter_triv_laws. Qed.
Lemma HB_METER_FS_LAWS : ameter_fs_laws MT.
Proof. exact BCbp.ameter_triv_fs_laws. Qed.
(* HB_SMP / HB_ASF / HB_FFL: lib/Reusable/YG05.v:71 stack_malloc_progress, lib/Reusable/YG0t.v:497
   astack_free_law_ok, and AR_laws' al_flag / al_client_img with the image cover (lib/B/Prog/WirePImg.v
   wire_img_cover). *)
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
  pose proof (BImg.wire_img_cover ly S md LO L) as [C1 C2].
  destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
  split; [exact Hp|]. split; [exact Ho|]. split.
  - split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
  - split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* HB_SINK_IMG_LAWS: lib/B/YD1u.v:45 tfib_AIL at WireB. HB_SINK_KEPT / HB_META_KEPT: lib/B/YE01.v:86 asink_none_kept /
   :157 ameta_inv_kept, specialised to one journal step, as the entry's statement takes them. *)
Lemma HB_SINK_IMG_LAWS : @asink_img_laws SK segs B KS.
Proof. exact (BD1u.tfib_AIL B BD2l.WireB_syms). Qed.
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
(* HB_API_ENV / HB_RO_BELOW_OFL: lib/B/WireBFacts.v (computation at WireB; the class of lib/B/Prog/PaBase.v). *)
Lemma HB_API_ENV : api_env segs B.
Proof. exact BF.HB_API_ENV. Qed.
Lemma HB_RO_BELOW_OFL : @PB.ro_below_ofl segs RLO RHI SK.
Proof. exact BF.HB_RO_BELOW_OFL. Qed.
(* H_LINK_MALLOC04 / H_LINK_FREE04: the call-rule form a program walk consumes, lib/B/YCbp.v:32 amalloc04_rule_triv /
   :46 afree04_rule_triv, at the image's segments (lib/B/Prog/WirePImg.v wire_segs_low), HB_API_ENV, AR_laws_ok and
   HB_MODEL_LAWS. *)
Lemma H_LINK_MALLOC04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @amalloc_realizes fx rc segs B -> @amalloc04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AM. apply (BCbp.amalloc04_rule_triv (SK := SK) segs B).
  - exact BImg.wire_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AM.
Qed.
Lemma H_LINK_FREE04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree_realizes fx rc segs B -> @afree04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AF. apply (BCbp.afree04_rule_triv (SK := SK) segs B).
  - exact BImg.wire_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AF.
Qed.

(* ===================================================================================================== *)
(* The composition: the callee contracts give the slot lib/B/YCfn.v:140, which the closed walk takes.      *)
(* ===================================================================================================== *)
Section RC. Context {rc : YM05.RunCeil}.

(* The leaves, each from its PROVED translation (lib/B/Prog/<leaf>_cg.v wire_<leaf>_cg_of_F) over the kit's generic
   translation H_LEAF_GLUE, applied to its footprint contract. *)
Local Notation GLUE fx := (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME).
Lemma ITR_F : FIT.is_tagged_reac_contract_F.
Proof. exact H_PROG_ITR_F. Qed.
Lemma RDS_F : FDA.rp_ds_accept_contract_F.
Proof. exact (H_PROG_RDS_F ITR_F). Qed.
Lemma RSW_F : FSW.rp_slot_width_contract_F.
Proof. exact (H_PROG_RSW_F H_PROG_RFCH_F). Qed.
Lemma RSR_F : FSR.rp_slot_read_contract_F.
Proof. exact (H_PROG_RSR_F RSW_F). Qed.
Lemma LEAF_FWD : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LFC.wire_rp_fwd_class_cg) fx.
Proof.
  intros fx. exact (@LFC.wire_rp_fwd_class_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) H_PROG_RFWD_F).
Qed.
Lemma LEAF_RET : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LRA.wire_rp_ret_accept_cg) fx.
Proof.
  intros fx. exact (@LRA.wire_rp_ret_accept_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) H_PROG_RRET_F).
Qed.
Lemma LEAF_DS : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LDA.wire_rp_ds_accept_cg) fx.
Proof.
  intros fx. exact (@LDA.wire_rp_ds_accept_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) RDS_F).
Qed.
Lemma LEAF_METER : forall fx : YK11.FPState, @PCs.wire_leaf_wr_at rc B (@LMC.wire_rp_meter_counter_cg) fx.
Proof.
  intros fx. exact (@LMC.wire_rp_meter_counter_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) H_PROG_RMET_F).
Qed.
Lemma LEAF_CNT : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LRC.wire_rp_counter_cg) fx.
Proof.
  intros fx. exact (@LRC.wire_rp_counter_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) H_PROG_RCNT_F).
Qed.
Lemma LEAF_FCH : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LFH.wire_rp_frame_channels_cg) fx.
Proof.
  intros fx. exact (@LFH.wire_rp_frame_channels_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) H_PROG_RFCH_F).
Qed.
Lemma LEAF_SR : forall fx : YK11.FPState, @PCs.wire_leaf_wr_at rc B (@LSR.wire_rp_slot_read_cg) fx.
Proof.
  intros fx. exact (@LSR.wire_rp_slot_read_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) RSR_F).
Qed.
Lemma LEAF_ITR : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LIT.wire_is_tagged_reac_cg) fx.
Proof.
  intros fx. exact (@LIT.wire_is_tagged_reac_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) ITR_F).
Qed.
Lemma LEAF_ISR : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LIR.wire_reac_frame_is_reac_cg) fx.
Proof.
  intros fx. exact (@LIR.wire_reac_frame_is_reac_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
    (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (GLUE fx) H_PROG_RISR_F).
Qed.

(* rp_copy_untag, realizes form. *)
Lemma RCPY_HOLDS : forall fx : YK11.FPState, @PRU.wire_rp_copy_untag_cg fx rc B (WAddr.wire_sigma WS_rp_copy_untag).
Proof.
  intros fx. apply (H_PROG_RCPY fx rc).
  - exact HB_CELLS.
  - apply AR_laws_ok.
  - intros fx'. exact (H_RT_MEMMOVE rc fx').
  - exact LEAF_ITR.
  - exact LEAF_ISR.
Qed.

(* The eight checks. *)
Lemma CFWD_HOLDS : forall fx : YK11.FPState, @PCF.wire_check_forward_cg fx rc B MT (WAddr.wire_sigma WS_check_forward).
Proof. intros fx. exact (H_PROG_CFWD fx rc HB_CELLS (AR_laws_ok tfibsegs B) HB_METER_LAWS LEAF_FWD). Qed.
Lemma CRET_HOLDS : forall fx : YK11.FPState, @PCR.wire_check_ret_cg fx rc B MT (WAddr.wire_sigma WS_check_ret).
Proof. intros fx. exact (H_PROG_CRET fx rc HB_CELLS (AR_laws_ok tfibsegs B) HB_METER_LAWS LEAF_RET). Qed.
Lemma CDS_HOLDS : forall fx : YK11.FPState,
  @PCD.wire_check_downstream_cg fx rc B MT (WAddr.wire_sigma WS_check_downstream).
Proof. intros fx. exact (H_PROG_CDS fx rc HB_CELLS (AR_laws_ok tfibsegs B) HB_METER_LAWS LEAF_DS). Qed.
Lemma CCNT_HOLDS : forall fx : YK11.FPState, @PCN.wire_check_counter_cg fx rc B MT (WAddr.wire_sigma WS_check_counter).
Proof. intros fx. exact (H_PROG_CCNT fx rc HB_CELLS (AR_laws_ok tfibsegs B) HB_METER_LAWS LEAF_CNT). Qed.
Lemma CWID_HOLDS : forall fx : YK11.FPState, @PCW.wire_check_width_cg fx rc B MT (WAddr.wire_sigma WS_check_width).
Proof.
  intros fx. exact (H_PROG_CWID fx rc HB_CELLS HB_RO_RD_UNOWNED HB_ROM_NO_ERRNO (AR_laws_ok tfibsegs B) HB_METER_LAWS
    LEAF_FCH).
Qed.
Lemma CMET_HOLDS : forall fx : YK11.FPState, @PCM.wire_check_meter_cg fx rc B MT (WAddr.wire_sigma WS_check_meter).
Proof.
  intros fx. apply (H_PROG_CMET fx rc).
  - exact HB_PC_STACK_MALLOC0.
  - exact HB_CELLS.
  - apply AR_laws_ok.
  - exact HB_METER_LAWS.
  - exact HB_METER_FS_LAWS.
  - exact HB_SMP.
  - exact (HB_ASF rc).
  - exact (HB_FFL rc).
  - intros fx'. exact (H_RT_STACK_MALLOC0 rc fx').
  - exact LEAF_METER.
Qed.
Lemma CRD_HOLDS : forall fx : YK11.FPState, @PCRd.wire_check_read_cg fx rc B MT (WAddr.wire_sigma WS_check_read).
Proof.
  intros fx. apply (H_PROG_CRD fx rc).
  - exact HB_PC_STACK_MALLOC1.
  - exact HB_CELLS.
  - exact HB_RO_RD_UNOWNED.
  - exact HB_ROM_NO_ERRNO.
  - apply AR_laws_ok.
  - exact HB_METER_LAWS.
  - exact HB_METER_FS_LAWS.
  - exact HB_SMP.
  - exact (HB_ASF rc).
  - exact (HB_FFL rc).
  - intros fx'. exact (H_RT_STACK_MALLOC1 rc fx').
  - exact LEAF_SR.
Qed.
Lemma CCPY_HOLDS : forall fx : YK11.FPState, @PCC.wire_check_copy_cg fx rc B MT (WAddr.wire_sigma WS_check_copy).
Proof.
  intros fx. apply (H_PROG_CCPY fx rc).
  - exact HB_PC_WRAP_MALLOC.
  - exact HB_PC_WRAP_FREE.
  - exact HB_CELLS.
  - apply AR_laws_ok.
  - exact HB_METER_LAWS.
  - exact HB_CC_UFIX.
  - intros fx'. exact (H_LINK_MALLOC04 rc fx' (H_RT_MALLOC rc fx')).
  - intros fx'. exact (H_LINK_FREE04 rc fx' (H_RT_FREE rc fx')).
  - intros fx'. exact (H_RT_ASAN_MEMCPY rc fx').
  - intros fx'. exact (H_RT_BCMP rc fx').
  - exact RCPY_HOLDS.
Qed.

(* The slot of the entry function, from its walk and every callee it names. *)
Lemma LIB_CONTRACT : @BCfn.tfib_lib_contract_x_all rc checksum_shape B MT XL XL RLO RHI.
Proof.
  apply (H_PROG_LLVMF rc).
  - exact HB_PC_WRAP_MALLOC.
  - exact HB_PC_WRAP_FREE.
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
  - exact HB_LLVMF_UFIX.
  - intros fx'. exact (H_LINK_MALLOC04 rc fx' (H_RT_MALLOC rc fx')).
  - intros fx'. exact (H_LINK_FREE04 rc fx' (H_RT_FREE rc fx')).
  - intros fx'. exact (H_RT_ASAN_MEMCPY rc fx').
  - exact CFWD_HOLDS.
  - exact CRET_HOLDS.
  - exact CDS_HOLDS.
  - exact CMET_HOLDS.
  - exact CCNT_HOLDS.
  - exact CWID_HOLDS.
  - exact CRD_HOLDS.
  - exact CCPY_HOLDS.
  - exact HB_COST.
Qed.

Lemma wire_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS:=checksum_shape) inp).
Proof.
  exact (@BD1q.tfib_srealizesX rc B BD2l.WireB_syms
    (BAl.wireB_MALLOC YK11.fx0 rc) (BAl.wireB_FREE YK11.fx0 rc)
    (BD2m.tfib_AICPY B BD2l.WireB_syms) (BD2m.tfib_ARDCHK B BD2l.WireB_syms)
    MT XL XL RLO RHI MT_FREE RO_IN LIB_CONTRACT
    BD1k.xst BD1k.tfib_xst_frame
    (BD1o.tfib_printf_first B BD2l.WireB_syms (AR_laws_ok tfibsegs B) BD2l.WireB_syms)
    (BD1o.tfib_printf_next B BD2l.WireB_syms (AR_laws_ok tfibsegs B) BD2l.WireB_syms)
    BD1k.est BD1k.tfib_est_img BD1k.tfib_est_frame
    (BD1k.tfib_fwrite_site B BD2l.WireB_syms (AR_laws_ok tfibsegs B))
    (BD1k.tfib_refused_site B BD2l.WireB_syms (AR_laws_ok tfibsegs B) BD2l.WireB_syms)
    (BD1l.tfib_fprintf_open_site B BD2l.WireB_syms (AR_laws_ok tfibsegs B) BD2l.WireB_syms)
    (BD1l.tfib_fprintf_rderr_site B BD2l.WireB_syms (AR_laws_ok tfibsegs B) BD2l.WireB_syms)
    (BD1l.tfib_fprintf_usage_site B BD2l.WireB_syms (AR_laws_ok tfibsegs B) BD2l.WireB_syms)
    (BD1j.tfib_exit_site B BD2l.WireB_syms (AR_laws_ok tfibsegs B))).
Qed.
End RC.

Theorem wire_B_TFIB_T_of_parts : WBT.TFIB_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@wire_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowW sp Hsp)) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan+UBSan statements of record, closed: every part above is a Lemma. *)
Theorem wire_asan_ubsan_agrees_of_parts : USt.asan_ubsan_agrees.
Proof. exact (wire_asan_ubsan_agrees_of_tfib wire_B_TFIB_T_of_parts). Qed.
Theorem wire_asan_ubsan_halts_of_parts : USt.asan_ubsan_halts.
Proof. exact (wire_asan_ubsan_halts_of_tfib wire_B_TFIB_T_of_parts). Qed.

About wire_B_TFIB_T_of_parts.
Print Assumptions wire_B_TFIB_T_of_parts.
About wire_asan_ubsan_agrees_of_parts.
Print Assumptions wire_asan_ubsan_agrees_of_parts.
About wire_asan_ubsan_halts_of_parts.
Print Assumptions wire_asan_ubsan_halts_of_parts.
Print Assumptions LIB_CONTRACT.
Print Assumptions H_LEAF_GLUE.
Print Assumptions HB_CELLS.
Print Assumptions HB_FFL.
