(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_defs2 Sj_stage2_numr_defs3 Sj_stage2_numr_defs4 Sj_stage2_numr_loops Sj_stage2_numr6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow_cp | s2_load_shadow | s2_load_cp | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

  Ltac rfin3 KDA KDB KDC KBIG KW3 KEND :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0xbcbf0%Z => kapply KBIG; nclose
      | 0xbd044%Z => kapply KW3; nclose
      | 0xbd0c0%Z => first [ (n_tape2; s2_kvr_kapply KEND; nclose) | (kapply KEND; nclose) ]
      | _ => rfin KDA KDB KDC
      end end.
  Ltac rexp3 KDA KDB KDC KBIG KW3 KEND :=
    ngexp ltac:(fun pc => lazymatch pc with 0xbcc1c%Z => fail | 0x10ac6c%Z => fail | 0xbcbf0%Z => fail | 0xbd044%Z => fail | 0xbd0c0%Z => fail | _ => idtac end)
          ltac:(idtac; rfin3 KDA KDB KDC KBIG KW3 KEND).
  Ltac rgo3 KDA KDB KDC KBIG KW3 KEND := ngstep; rexp3 KDA KDB KDC KBIG KW3 KEND.

Section NumR3b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Lemma seg_numr_intbig : forall (Q : machine_state -> Prop) (s : st) neg,
    rdelAc_k E Q CP -> rdelB_k E Q CP -> rdelC_k E Q CP -> numr_intbig_k E Q CP s neg.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg KDA KDB KDC. unfold numr_intbig_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    rgo3 KDA KDB KDC KDA KDA KDA.
  Qed.

  Lemma seg_numr_intend : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= p <= LEN)%Z -> Z.of_nat (length (e_tws E)) = 3%Z -> rdelAc_k E Q CP -> rdelB_k E Q CP -> rdelC_k E Q CP -> numr_intend_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HP HL3 KDA KDB KDC. unfold numr_intend_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK.
    pose proof (B_range bs p BOK) as HB0. pose proof (sown_range (B bs p)) as HSW.
    s2_env OK.
    nopen HM.
    rgo3 KDA KDB KDC KDA KDA KDA.
  Qed.

End NumR3b.

Section NumR3c.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Lemma seg_numr_intw3 : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= p <= LEN)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> rdelAc_k E Q CP -> rdelB_k E Q CP -> (forall v r, num_word v -> rdelC_k (gapp E [v; r] []) Q CP) ->
    (forall v r, num_word v -> numr_intend_k (gapp E [v; r] []) Q CP s neg p) -> numr_intw3_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HP GLT KDA KDB KDC KEND. unfold numr_intw3_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    rgo3 KDA KDB KDC KDA KDA KEND.
  Qed.

  Lemma seg_numr_int : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= p <= LEN)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> rdelAc_k E Q CP -> rdelB_k E Q CP -> rdelC_k E Q CP -> (forall v r, num_word v -> rdelC_k (gapp E [v; r] []) Q CP) ->
    numr_int_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HP GLT KDA KDB KDC KDC3.
    pose proof (seg_numr_intbig E OK SHZ CP HCP SHZC Q s neg KDA KDB KDC) as KBIG.
    assert (KEND : forall v r, num_word v -> numr_intend_k (gapp E [v; r] []) Q CP s neg p).
    { intros v r Hv. refine (seg_numr_intend (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s neg p HP _ (rdelAc_k_gapp E Q CP _ _ KDA) (rdelB_k_gapp E Q CP _ _ KDB) (KDC3 v r Hv)).
      cbn [e_tws gapp s2_ghost]. rewrite length_app. cbn [length]. lia. }
    pose proof (seg_numr_intw3 Q s neg p HP GLT KDA KDB KDC3 KEND) as KW3.
    unfold numr_int_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK.
    pose proof (B_range bs p BOK) as HB0. pose proof (sown_range (B bs p)) as HSW. pose proof (B_range bs 0 BOK) as HBT.
    s2_env OK.
    nopen HM.
    rexp3 KDA KDB KDC3 KBIG KW3 KEND.
  Qed.
End NumR3c.
