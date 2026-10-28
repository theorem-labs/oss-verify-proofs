(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= lia0.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow_cp | s2_load_shadow | s2_load_cp | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Definition numr_entry_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbd2dc xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Section NumR1.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Lemma seg_numr_entry : forall (Q : machine_state -> Prop) (s : st),
    rdelA_k E Q CP ->
    (forall neg p, (0 <= neg <= 1)%Z -> (0 + neg < LEN)%Z -> (0 + neg < p <= LEN)%Z -> numr_dot_k E Q CP s neg p) ->
    numr_entry_k E Q CP.
  Proof using OK SHZ HCP SHZC.
    intros Q s KX KD. unfold numr_entry_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK.
    s2_env OK.
    nopen HM.
    ngrun_to 0xbd304%Z.
    match goal with |- context [Z.b2z ?c] =>
      assert (HNEG : (0 <= Z.b2z c <= 1)%Z) by (destruct c; cbn; lia);
      set (neg := Z.b2z c) in *; clearbody neg end.
    pose proof (B_range bs neg BOK) as HB0.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun. if_cases K1; zify_cond K1; try (exfalso; lia).
      nexit KX.
    -
      assert (HS : (neg < LEN)%Z) by (nz_lt_by ltac:(lia)).
      ngrun_to 0xbd348%Z.
      kapply (numr_L1 E OK SHZ CP HCP SHZC Q (S (Z.to_nat (LEN))) neg); [nclose | lia | lia |].
      intros p'. intro_words. intros HP'.
      pose proof (B_range bs p' BOK) as HBP.
      ngrun.
      if_cases K2; zify_cond K2; try (exfalso; lia).
      ngrun.
      if_cases K3; zify_cond K3.
      + kapply (KD neg p' HNEG ltac:(lia) ltac:(lia)). nclose.
      + ngrun.
        if_cases K4; zify_cond K4;
          first [ (kapply (KD neg p' HNEG ltac:(lia) ltac:(lia)); nclose) | nexit KX ].
  Qed.
End NumR1.
