(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (meta_cells_meta0, am_carve_eq)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_am_K () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc6F_am_K8carve_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma zeros_length n : length (zeros n) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CANSEC1"] "h01np;1p;3p;2p10000p4p70R0p1000ep4p710R1p8P0p1001CR2p4p710p8P0p1001_R3p4p710R4p8P0P3p4p7210R3p8P0p10028R5p4p710p8P0p1002QR6p4p710p8P0p10031p4p73110p8P0p1003CR7p4p710p8P0p1003WR0p4p710p8p1003kp4p70R8P2p4p7210p8P8P2p4p73110p8P8p1004`R2p4p710p8P8P2p4p7210p8P8p1005;p5p710p8P8P5p4p741110p8P8P6p4p741110p8P8P7p4p7210p8P8P7p4p73110p8P8P0p4p7210p8P8P0p4p73110p8P1P4p8P1P3p8g005Wj10Tg006<j17Tg006Zj12Tg007=j11Tg0085j36Tg008Wj15Tg009Rj23Tg00:2j34Tg00:LR3g00:k#0#0#0#7#2R1g00;P#1f0R436%54,31=434eX03P4O1W0o"). Qed.

Lemma le8_zero : le8 (wz 0) = zeros 8.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CANSEC1"] "p;1p;2g005Wj11Tg006<j16Tg006Zj13Tg00;nj12Tg00<Nj10Tg008Wj15Tg00<mj24Tg00:k#1#1#1#6#3#2g00=G#0#0#0#0#0#0#0#0#5'4o"). Qed.
Lemma le4_zero : le4 (wz 0) = zeros 4.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CANSEC1"] "p;1p;2g005Wj11Tg006<j16Tg006Zj13Tg00;nj12Tg00<Nj10Tg008Wj15Tg00<mj24Tg00:k#1#1#1#6#3#2g00=G#0#0#0#0#5'4o"). Qed.

Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

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
Proof. reflexivity. Qed.

End CANSEC1.
