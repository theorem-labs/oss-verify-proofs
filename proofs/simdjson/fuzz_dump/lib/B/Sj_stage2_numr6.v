(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_defs2 Sj_stage2_numr_defs3 Sj_stage2_numr_loops.
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

Ltac r_len3 := first [ (intros _; assumption) | (intros HH; exfalso; lia) | (intros _; cbn [e_tws gapp s2_ghost]; rewrite ?length_app; cbn [length]; lia) ].
Ltac rfin KDA KDB KDC :=
  lazymatch goal with |- evt _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 0xbcc1c%Z => nstep; gdec; rexp KDA KDB KDC
    | 0x10ac6c%Z =>
        let ra := greg_val R 1%Z in
        lazymatch ra with
        | Z_to_bv 64 0xb73b0%Z => kapply KDA; s2_close_memxj
        | Z_to_bv 64 0xbcc34%Z => kapply KDB; [ s2_close_memx | first [ lia | apply land9_range ] ]
        | Z_to_bv 64 0xbcc54%Z => first [ (n_tape2; s2_kvr_kapply KDC; [ ntape_norm; s2_close_mem0 | s2_gproj_goal; first [ lia | apply land9_range ] | s2_gproj_goal; first [ lia | (intros HH; exfalso; lia) ] | r_len3 ])
                                        | (kapply KDC; [ ntape_norm; s2_close_mem0 | first [ lia | apply land9_range ] | first [ lia | (intros HH; exfalso; lia) ] | r_len3 ]) ]
        end
    end end
with rexp KDA KDB KDC :=
  ngexp ltac:(fun pc => lazymatch pc with 0xbcc1c%Z => fail | 0x10ac6c%Z => fail | _ => idtac end) ltac:(idtac; rfin KDA KDB KDC).

Section NumR6.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Lemma seg_numr_delA : forall (Q : machine_state -> Prop), rdelAc_k E Q CP -> rdelA_k E Q CP.
  Proof using OK SHZ.
    intros Q KD. unfold rdelA_k. intros until m1. intros HM.
    s2_env OK. s2_open_memxj HM.
    ngrun_to 0x10ac6c%Z.
    kapply KD. s2_close_memxj.
  Qed.

  Lemma seg_numr_fin : forall (Q : machine_state -> Prop) (s : st) r tw,
    (r = 0 \/ r = 9)%Z -> (r = 0 -> tw = 3)%Z -> (tw = 3 -> Z.of_nat (length (e_tws E)) = 3)%Z -> rdelC_k E Q CP -> numr_fin_k E Q CP s r tw.
  Proof using OK SHZ HCP SHZC.
    intros Q s r tw HR HTW HL3 KD. unfold numr_fin_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    destruct HR as [-> | ->].
    - assert (tw = 3%Z) by (apply HTW; reflexivity). subst tw.
      repeat (ngrun_to 0x10ac6c%Z; gdec). ngrun_to 0x10ac6c%Z.
      kapply KD; [ s2_close_mem0 | apply land9_range | intros _; lia | intros _; apply HL3; reflexivity ].
    - repeat (ngrun_to 0x10ac6c%Z; gdec). ngrun_to 0x10ac6c%Z.
      kapply KD; [ s2_close_mem0 | lia | intros HH; exfalso; lia | intros HH; exfalso; lia ].
  Qed.

  Lemma seg_numr_write : forall (Q : machine_state -> Prop) (s : st) neg,
    Z.of_nat (length (e_tws E)) = 1%Z -> (forall v r, num_word v -> numr_fin_k (gapp E [v; r] []) Q CP s 0 3) -> numr_write_k E Q CP s neg.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg GLT KF. unfold numr_write_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    ngrun_to 0xbcbe0%Z.
    n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

  Lemma seg_numr_slowret : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 9 \/ r = 0)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> (forall vw rw, num_word vw -> numr_fin_k (gapp E [vw; rw] []) Q CP s r 3) -> numr_slowret_k E Q CP s r v.
  Proof using OK SHZ HCP SHZC.
    intros Q s r v HR GLT KF. unfold numr_slowret_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    ngrun_to 0xbcbe0%Z.
    n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

  Lemma seg_numr_fbret : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 0 \/ r = 1)%Z -> numr_fin_k E Q CP s 9 1 -> numr_write_k E Q CP s 0 -> numr_fbret_k E Q CP s r v.
  Proof using OK SHZ HCP SHZC.
    intros Q s r v HR KF KW. unfold numr_fbret_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    destruct HR as [-> | ->].
    - nstep. gdec. ngrun_to 0xbcbe0%Z. kapply KF. nclose.
    - nstep. gdec. ngrun_to 0xbcb48%Z. kapply KW. nclose.
  Qed.
End NumR6.

Section NumR6b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.

  Lemma seg_numr_retA : forall (Q : machine_state -> Prop), exit_k E Q -> rretA_k E Q.
  Proof using OK SHZ.
    intros Q KX. unfold rretA_k. intros until m1. intros HM.
    s2_env OK. s2_open_memxj HM.
    ngrun_to 0xcd104%Z. gexit KX.
  Qed.

  Lemma seg_numr_retB : forall (Q : machine_state -> Prop), exit_k E Q -> rretB_k E Q.
  Proof using OK SHZ.
    intros Q KX. unfold rretB_k. intros until m1. intros HM HERR.
    s2_env OK. s2_open_memx HM.
    ngrun_to 0xcd104%Z. eapply KX; cycle 1; [ s2_close_memx | left; exact HERR ].
  Qed.

  Lemma seg_numr_retC : forall (Q : machine_state -> Prop), exit_k E Q -> (Z.of_nat (length (e_tws E)) = 3%Z -> docend_k E Q (mkst 1 0 3 0 [])) -> rretC_k E Q.
  Proof using OK SHZ.
    intros Q KX KD0. unfold rretC_k. intros until m1. intros HM HR HTP HL3.
    pose proof (n_bound E OK) as HNB. s2_env OK. s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    - assert (tp = (e_TAPE E + 24)%Z) by (apply HTP; lia). subst tp. pose proof (KD0 (HL3 ltac:(lia))) as KD. unfold docend_k in KD. cbn [k depth W sb scopes] in KD.
      ngrun_to 0xbcc60%Z.
      kapply KD. s2_close_mem0.
    - ngrun_to 0xcd104%Z. eapply KX; cycle 1; [ s2_close_memx | left; clear - HR K0; lia ].
  Qed.
End NumR6b.
