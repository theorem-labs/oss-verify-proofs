(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Pj_steps Pj_loc_defs Pj_loc_kit Pj_os_defs Pj_os_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import El_os_defs El_np_int.
From OSSVerify.simdjson.fuzz_dump.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Notation EL_NP_BOOL := 0x88638%Z (only parsing).

Definition np_b_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill u pp ep : Z) (pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NP_DEPTH)%Z -> (0x10b000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xea088 + 48) ->
  rw_cells usegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells usegs m (OS + 136) (ios_cellsX OS 0xd1680 0x1002 0 fill j148 j284) ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  (0 <= fill < 256)%Z -> (u = 0 \/ u = 1)%Z ->
  rw_cells usegs m 0xea088 [C8 (Z_to_bv 64 0x10a380)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (np_ul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS fill j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 u) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_NP_BOOL) fc None m (seg_rom usegs)).

Theorem np_b_proof : np_b_stmt.
Proof.
  unfold np_b_stmt. intros until canary. intros ST LO LOLO SPH TP SB PI IOS RO RO2 OS8 RF RU TPC SSP FRM LB DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(lo, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168); (0xea088, 0xea088 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  destruct DCC as (VT & WS & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  unfold ios_cellsX in IOS.

  retype_at IOS 1%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  lstep.
  carve_frame 96%nat ST.
  do 5 lstep.
  do 2 lstep.
  lstep.
  lit_words.
  lstep.
  lstep.
  if_false.
  do 2 lstep.
  do 2 lstep.
  do 6 lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  retype_at IOS 1%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  eapply evt_mono.
  - eapply (np_ul_proof ra sp gp tp _ _ _ s0 s1 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 lo OS fill u pp ep pb dum j148 j284 canary);
      [ exact ST | lia | lia | lia | exact TP | exact SB | exact PI | unfold ios_cellsX; exact IOS | lia | lia | exact OS8 | lia | lia | exact TPC
      | split; [exact SSP1 | exact SSP2] | exact FRM | do 15 eexists; exact LBC
      | split; [exact VT| split; [exact WS| split; [exact NPT| split; [exact NPV| split; [exact GNP| exact GCT]]]]]
      | assumption ].
  - intros ms' P. unfold np_ul_post in P |- *.
    destruct P as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & Ft & fc' & pb' & pp' & ep' & dum' & m' & E & MU1 & WM1 & REST).
    do 21 eexists. split; [exact E|]. split; [| split; [exact (wmono_trans _ _ _ _ WM WM1)| exact REST]].
    eapply munch_trans; [| exact MU1]. eapply munch_weaken; [| exact MU]. intros x Hx. exact Hx.
Qed.
