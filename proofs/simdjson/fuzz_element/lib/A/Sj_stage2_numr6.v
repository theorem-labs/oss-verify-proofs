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
Local Ltac g_store_hook ::= s2_note_tape.

Definition rdelAc_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall err xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (1 <= err < 64)%Z -> MEMX E fc m1 ->
    evt asegs Q (S2R E 0x1064bc (Z_to_bv 64 (0xbd5ac)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 (Z_to_bv 64 (err)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
Definition rdelB_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall v tw xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (0 <= v < 64)%Z ->
    (v = 0 -> tw = 3)%Z -> (tw = 3 -> Z.of_nat (length (e_tws E)) = 3)%Z ->
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8 * tw)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0x1064bc (Z_to_bv 64 (0xc291c)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 (Z_to_bv 64 (v)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rdelC_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 24)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0x1064bc (Z_to_bv 64 (0xc2f24)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rretA_k (E : s2env) (Q : machine_state -> Prop) : Prop :=
  forall err xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (1 <= err < 64)%Z -> MEMX E fc m1 ->
    evt asegs Q (S2R E 0xbd5ac (Z_to_bv 64 (0xbd5ac)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 (Z_to_bv 64 (err)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
Definition rretB_k (E : s2env) (Q : machine_state -> Prop)  : Prop :=
  forall v tw xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (0 <= v < 64)%Z ->
    (v = 0 -> tw = 3)%Z -> (tw = 3 -> Z.of_nat (length (e_tws E)) = 3)%Z ->
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8 * tw)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xc291c (Z_to_bv 64 (0xc291c)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 (Z_to_bv 64 (v)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rretC_k (E : s2env) (Q : machine_state -> Prop)  : Prop :=
  forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 24)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xc2f24 (Z_to_bv 64 (0xc2f24)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Lemma land9_range_r : forall x, (0 <= Z.land x 9 < 64)%Z.
Proof.
  intros x. assert (E : Z.land (Z.land x 9) (Z.ones 4) = Z.land x 9) by (rewrite <- Z.land_assoc; reflexivity).
  rewrite Z.land_ones in E by lia. pose proof (Z.mod_pos_bound (Z.land x 9) (2 ^ 4) ltac:(lia)). lia.
Qed.

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
    intros Q KD. unfold rdelA_k. intros until m1. intros HERR HM.
    s2_env OK. s2_open_memx HM.
    ngrun_to 0x1064bc%Z.
    kapply (KD err); [exact HERR | s2_close_memx].
  Qed.

  Lemma seg_numr_join : forall (Q : machine_state -> Prop) (s : st), rdelC_k E Q CP -> numr_join_k E Q CP s.
  Proof using OK SHZ HCP SHZC.
    intros Q s KD. unfold numr_join_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    ngrun_to 0x1064bc%Z.
    kapply KD. s2_close_mem0.
  Qed.

  Lemma seg_numr_fin : forall (Q : machine_state -> Prop) (s : st) r tw,
    (r = 0 \/ r = 9)%Z -> (r = 0 -> tw = 3)%Z -> (tw = 3 -> Z.of_nat (length (e_tws E)) = 3)%Z -> rdelB_k E Q CP -> numr_fin_k E Q CP s r tw.
  Proof using OK SHZ HCP SHZC.
    intros Q s r tw HR HTW HL3 KD. unfold numr_fin_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    destruct HR as [-> | ->].
    - repeat (ngrun_to 0x1064bc%Z; gdec). ngrun_to 0x1064bc%Z.
      lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
        let v := greg_val R 23%Z in lazymatch v with Z_to_bv 64 ?ev => kapply (KD ev tw); [apply land9_range_r | intros _; apply HTW; reflexivity | exact HL3 | s2_close_mem0] end end.
    - repeat (ngrun_to 0x1064bc%Z; gdec). ngrun_to 0x1064bc%Z.
      kapply (KD 9%Z tw); [lia | intros HH; discriminate HH | exact HL3 | s2_close_mem0].
  Qed.

  Lemma seg_numr_write : forall (Q : machine_state -> Prop) (s : st) neg,
    Z.of_nat (length (e_tws E)) = 1%Z -> (forall v r, num_word v -> numr_fin_k (gapp E [v; r] []) Q CP s 0 3) -> numr_write_k E Q CP s neg.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg GLT KF. unfold numr_write_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    ngrun_to 0xc28c4%Z.
    n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

  Lemma seg_numr_slowret : forall (Q : machine_state -> Prop) (s : st) r v,
    Z.of_nat (length (e_tws E)) = 1%Z -> (forall vw rw, num_word vw -> numr_fin_k (gapp E [vw; rw] []) Q CP s r 3) -> numr_slowret_k E Q CP s r v.
  Proof using OK SHZ HCP SHZC.
    intros Q s r v GLT KF. unfold numr_slowret_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    ngrun_to 0xc28c4%Z.
    n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

  Lemma seg_numr_fbret : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 0 \/ r = 1)%Z -> numr_fin_k E Q CP s 9 1 -> numr_write_k E Q CP s 0 -> numr_fbret_k E Q CP s r v.
  Proof using OK SHZ HCP SHZC.
    intros Q s r v HR KF KW. unfold numr_fbret_k. intros until m1. intros HM.
    s2_env OK. nopen HM.
    destruct HR as [-> | ->].
    - repeat (ngrun_to 0xc28c4%Z; gdec). ngrun_to 0xc28c4%Z. kapply KF. nclose.
    - repeat (ngrun_to 0xc287c%Z; gdec). ngrun_to 0xc287c%Z. kapply KW. nclose.
  Qed.
End NumR6.

Section NumR6b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.

  Lemma seg_numr_retA : forall (Q : machine_state -> Prop), exit_k E Q -> rretA_k E Q.
  Proof using OK SHZ.
    intros Q KX. unfold rretA_k. intros until m1. intros HERR HM.
    s2_env OK. s2_open_memx HM.
    ngrun_to 0xcb1dc%Z.
    eapply (KX err); [left; exact HERR | s2_close_memx].
  Qed.

  Lemma seg_numr_retC : forall (Q : machine_state -> Prop), docend_k E Q (mkst 1 0 3 0 []) -> rretC_k E Q.
  Proof using OK SHZ.
    intros Q KD. unfold docend_k in KD. cbn [k depth W sb scopes] in KD. unfold rretC_k. intros until m1. intros HM.
    pose proof (n_bound E OK) as HNB. s2_env OK. s2_open_mem HM.
    ngrun_to 0xc2f40%Z.
    kapply KD. s2_close_mem0.
  Qed.

  Lemma seg_numr_retB : forall (Q : machine_state -> Prop), exit_k E Q -> (Z.of_nat (length (e_tws E)) = 3%Z -> docend_k E Q (mkst 1 0 3 0 [])) -> rretB_k E Q.
  Proof using OK SHZ.
    intros Q KX KD0. unfold rretB_k. intros until m1. intros HV HTW HL3 HM.
    pose proof (n_bound E OK) as HNB. s2_env OK. s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    - assert (tw = 3%Z) by (apply HTW; lia). subst tw. pose proof (KD0 (HL3 eq_refl)) as KD. unfold docend_k in KD. cbn [k depth W sb scopes] in KD.
      ngrun_to 0xc2f40%Z.
      kapply KD. s2_close_mem0.
    - ngrun_to 0xcb1dc%Z.
      eapply (KX v); [left; clear - HV K0; lia | s2_close_memx].
  Qed.
End NumR6b.
