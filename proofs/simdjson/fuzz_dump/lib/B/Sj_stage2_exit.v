(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Definition s2_xpost (E : s2env) : machine_state -> Prop :=
  fun ms' => exists err x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 F' fc' m',
    ms' = MS (mkR (wz 0xcd124) (wz (e_spa E)) (e_gp E) (e_tp E) x5 x6 x7 (e_sp E) (wz (e_spa E)) (wz (e_FF E)) (wz 1312) x12 x13 x14 x15 x16 x17
                  x18 (wz (SHA (e_FF E))) x20 x21 x22 x23 x24 x25 (wz (e_FF E)) x27 x28 x29 x30 x31)
             F' (wz 0x64ecc) fc' None m' (seg_rom bsegs)
    /\ s2_errok E err /\ MEMX E err fc' m'.

Section Exit.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Lemma s2_exit : exit_k E (s2_xpost E).
  Proof using OK.
    unfold exit_k. intros until m1. intros HE H.
    s2_env OK.
    s2_open_memx H.
    grun_to 0xcd114%Z.
    zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
    grun_to 0x64ecc%Z.
    apply evt_done. unfold s2_xpost.
    do 25 eexists. split; [reflexivity|]. split; [exact HE|].
    s2_close_memx.
  Qed.

  Definition s2_epost (v : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E) v a1 a2 a3 a4 a5 a6 a7
                    (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
               F (ret_pc (e_ra E)) fc None m1 (seg_rom bsegs)
      /\ stk bsegs m1 (e_lo E) (bv_unsigned (e_sp E)).

  Lemma s2_epi : forall v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (jlo jhi : list byte),
    rw_cells bsegs m1 (e_spa E) [CB 272 jlo; C8 v; CB 32 jhi] ->
    rw_cells bsegs m1 (bv_unsigned (e_sp E) + -104) (saved_cells E) ->
    stk bsegs m1 (e_spa E + 312) (bv_unsigned (e_sp E) + -104) ->
    stk bsegs m1 (e_lo E) (e_spa E) ->
    evt bsegs (s2_epost v F fc m1)
      (MS (mkR x1 (wz (e_spa E)) (e_gp E) (e_tp E) x5 x6 x7 (e_sp E) (wz (e_spa E)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (wz 0xcd124) fc None m1 (seg_rom bsegs)).
  Proof using OK.
    intros until jhi. intros FR SAV GAP ST.
    s2_env OK. unfold saved_cells in SAV.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    do 18 step.
    apply evt_done. unfold s2_epost.
    do 14 eexists. split; [reflexivity|].
    eapply stk_release in FR; [ | exact ST | lia ]. cbn [cells_size csize Nat.add] in FR.
    assert (ST2 : stk bsegs m1 (e_lo E) (bv_unsigned (e_sp E) + -104)).
    { eapply (stk_merge bsegs m1 (e_lo E) (e_spa E + 312)); [ | exact GAP | lia ].
      replace (e_spa E + 312)%Z with (e_spa E + Z.of_nat 312)%Z by lia. exact FR. }
    eapply stk_release in SAV; [ | exact ST2 | lia ]. cbn [cells_size csize Nat.add] in SAV.
    replace (bv_unsigned (e_sp E) + -104 + Z.of_nat 104)%Z with (bv_unsigned (e_sp E)) in SAV by lia. exact SAV.
  Qed.
End Exit.
