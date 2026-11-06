(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_arrlA Atp_arratA Atp_objkwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section AtKeyX.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma atkey_after_nf : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (spk sret RA : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jlo zb oc od : list byte)
      (x5 x6 x7 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    rw_cells bsegs m (spk + -144) (CB 40 jlo :: atkey_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk bsegs m (ae_lo E) (spk + -144) -> mem_inv bsegs m -> ae_lo E <= spk + -144 ->
    rw_cells bsegs m sret [CB 16 zb; CB 4 oc; CB 4 od] -> spk + 16 <= sret -> sret + 24 <= ae_hi E -> sret mod 8 = 0 ->
    shz m sret 24 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
       munch [(sret, sret + 24)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) spk ->
       rw_cells bsegs m' sret [CB 16 zb; C4 (Z_to_bv 64 20); CB 4 od] ->
       evt bsegs K (MS (mkR (wz RA) (wz spk) gp (wz TPV) y5 y6 y7 s0 s1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                      F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb9310) (wz (spk + -144)) gp (wz TPV) x5 x6 x7 xs0 (wz (sret + 16)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 xs4 xs5 xs6 (wz 2147450880) xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                   F (wz 0xb9310) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT NO OB O8 SHZO RA0 RA2 HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(sret, sret + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold atkey_saved in FR. cbn [app] in FR.

    chk0 SHZO (sret + 16). step. if_false. astep. lstep.
    name_mem m1.
    lazymatch goal with H : rw_cells bsegs m1 (spk + -144) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.

    do 13 step. step. release_frame FR1 ST1 spk. step.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
    lazymatch goal with H : stk bsegs m1 _ spk |- _ => rename H into ST1' end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 sret _ |- _ => rename H into OUT1 end.
    eapply (HK m1); [exact MU| exact WM| exact MI1| exact ST1'| exact OUT1].
  Qed.

  Lemma atkey_found : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (spk sret RA it Kp : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w16 w24 : word) (j0 oa ob oc od : list byte)
      (x5 x6 x7 xs0 xs1 xs2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    rw_cells bsegs m (spk + -144) ([CB 8 j0; C8 (wz sret); C8 w16; C8 w24; C8 (wz Kp)] ++ atkey_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk bsegs m (ae_lo E) (spk + -144) -> mem_inv bsegs m -> ae_lo E <= spk + -144 ->
    rw_cells bsegs m sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> spk + 16 <= sret -> sret + 24 <= ae_hi E -> sret mod 8 = 0 ->
    (forall m', munch [(sret, sret + 24)] m m' -> wmono bsegs m m' -> shz m' sret 24) -> 0 <= RA < 2^64 -> RA mod 2 = 0 -> 0 <= it -> it + 1 < 2^63 ->
    (forall (m' : mem) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
       munch [(sret, sret + 24)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) spk ->
       rw_cells bsegs m' sret [C8 (wz (ae_DOC E)); C8 (wz (it + 1)); C4 (Z_to_bv 64 0); CB 4 od] ->
       evt bsegs K (MS (mkR (wz RA) (wz spk) gp (wz TPV) y5 y6 y7 s0 s1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                      F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb94a0) (wz (spk + -144)) gp (wz TPV) x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 (wz (ae_DOC E)) (wz it) xs5 xs6 (wz 2147450880) xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                   F (wz 0xb9554) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT NO OB O8 SHZO RA0 RA2 IT0 ITH HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ PTRR _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(sret, sret + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold atkey_saved in FR. cbn [app] in FR.

    step. step. if_dead1 by NO LO LOW.
    chk0 SHZO sret. step. if_false. step.

    astep. chk0 SHZO (sret + 8). step. if_false. astep. step.

    astep. chk0 SHZO (sret + 16). step. if_false. lstep. step.
    name_mem mF.
    lazymatch goal with H : rw_cells bsegs mF (spk + -144) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs mF _ _ |- _ => rename H into ST1 end.
    do 13 step. step. release_frame FR1 ST1 spk. step.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
    lazymatch goal with H : stk bsegs mF _ spk |- _ => rename H into ST1' end.
    lazymatch goal with H : mem_inv bsegs mF |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs mF sret _ |- _ => rename H into OUT1 end.
    eapply (HK mF); [exact MU| exact WM| exact MI1| exact ST1'| exact OUT1].
  Qed.
End AtKeyX.
