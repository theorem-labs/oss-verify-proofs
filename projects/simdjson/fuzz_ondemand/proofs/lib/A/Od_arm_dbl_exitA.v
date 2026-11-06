(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_cpsA Od_arm_dbl_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Section ArmDblExitA.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_success : forall (Q : machine_state -> Prop) st c0 c104 c176
      xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DBLINVa E st c0 c104 c176 m1 ->
    (forall m, rw_cells asegs m (oa_S1 E) c0 -> exists j0 j8 j16 j24, rw_cells asegs m (oa_S1 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]) ->
    (forall m, rw_cells asegs m (oa_S1 E + 104) c104 -> exists j104 j112 j120, rw_cells asegs m (oa_S1 E + 104) [CB 8 j104; CB 8 j112; CB 8 j120]) ->
    (forall m, rw_cells asegs m (oa_S1 E + 176) c176 -> exists j176, rw_cells asegs m (oa_S1 E + 176) [CB 8 j176]) ->
    od_plus_k E Q st ->
    evt asegs Q (ODST E 0x99640 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV C0 C104 C176 HK.
    pose proof HH as (HP & HD & HE & HAL & HB).
    dbl_open_inv INV. od_env OK.
    assert (KP : forall st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 mm,
      od_arm_out bs idxs st st' ->
      rw_cells asegs mm (oa_S1 E) c0 -> rw_cells asegs mm (oa_S1 E + 104) c104 -> rw_cells asegs mm (oa_S1 E + 176) c176 ->
      (forall j0 j8 j16 j24 j104 j112 j120 j176,
         rw_cells asegs mm (oa_S1 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] -> rw_cells asegs mm (oa_S1 E + 104) [CB 8 j104; CB 8 j112; CB 8 j120] ->
         rw_cells asegs mm (oa_S1 E + 176) [CB 8 j176] -> ODINV E st' mm) ->
      evt asegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc mm)).
    { intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? mm AO H0 H104 H176 HI.
      destruct (C0 mm H0) as (j0 & j8 & j16 & j24 & G0). destruct (C104 mm H104) as (j104 & j112 & j120 & G104). destruct (C176 mm H176) as (j176 & G176).
      apply (HK st'); [exact AO | exact FRM | exact (HI _ _ _ _ _ _ _ _ G0 G104 G176)]. }
    unfold OD_PLUS in KP.
    dwalkv ltac:(fun pc => lazymatch pc with
      | 0x98e3c%Z => first [ eapply (KP (consume 1 st));
                             [ apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_scalar
                             | eassumption | eassumption | eassumption | intros; od_close_inv ]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem dbl_resume : dbl_resume_stmt E.
  Proof using OK.
    unfold dbl_resume_stmt.
    intros Q st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH HK FRM INV.
    pose proof HH as (HP & HD & HE & HAL & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    dwalkv ltac:(fun pc => lazymatch pc with
      | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| od_close_inv];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x99640%Z => first [ destruct (dbl_of_od E st _ INV2) as (k0 & k8 & k16 & k24 & k104 & k112 & k120 & k176 & DI);
                             eapply evt_eq; [| eapply (dbl_success Q st _ _ _); [exact HLAST | exact HH | exact FRM | exact DI | | | | exact HK]];
                             [ od_st_eq | intros mm Hm; eauto 8 | intros mm Hm; eauto 8 | intros mm Hm; eauto 8 ]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End ArmDblExitA.
