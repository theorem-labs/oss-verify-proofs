(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_am_K () := "C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib2CJ1A9MallocRep2b8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC69OSSVerify5KrLib2CJ1A9MallocRep5zerosC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2CJ1A9MallocRep2wzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02I69OSSVerify5KrLib2CJ3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2CJ4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A6F_am_K8carve_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma zeros_length n : length (zeros n) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["AC_1"] "h01np;1p;3p;2p10000p4p70R0p1000hp4p710p8P0p1001FR1p4p710p8P0p1001bR2p4p710p8P0P2p4p7210p8P0p1002;R2p4p710p8P0p1002TR3p4p710p8P0p10034p4p73110p8P0p1003FR4p4p710p8P0p1003ZR0p4p710p8p1003np4p70R5P1p4p7210p8P5P1p4p73110p8P5p1004fR1p4p710p8P5P1p4p7210p8P5p1005Ap5p710p8P5P2p4p741110p8P5P3p4p741110p8P5P4p4p7210p8P5P4p4p73110p8P5P0p4p7210p8P5P0p4p73110p8g005]j10Tg006Bj17Tg006`j12Tg007Cj11Tg0089j36Tg008[j15Tg009Tj23Tg00:4j34Tg00:NR0g00:m#0#0#0#7#2R5g00;R#1f0R436%54,35=404eW0o"). Qed.

Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["AC_1"] "h02stp;1p;2p;3g00<0j17Tg00<Pj16Tg00=Fj12Tg00>>j11Tg00?6j15Tg00?Vj23Tg00@0j34Tg00@PR0f1f034p=0g00AH%70g00;R#6R1#2R2%11R1%50,02,01'0,02,02'0'3W0o"). Qed.

Definition carve_st (st : mstate) (p : aptr) : mstate :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3.

Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
  am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["AC_1"] "h01Rh14bailh21ch31kh41ph52stp;1p;2p;4p200R0g00BDR1p4p710p8P0g00C9R2p4p710p8P0p100D4p4p710p8P1j10Tg00E0j28Tg00Ehj22Tg00FJj21Tg00GRj27Tg00HTj26Tg00IMj23TP2j44Tg00?Vj25Tg00AHR2g0000R1g003nf4R3#0R4[\2f3R2#0P3g00JHg00KB,82,21g00L>f0R1'1'7W2f2,62'3f1P1C4,54W1W3W4W5X00o"). Qed.

End AC_1.
