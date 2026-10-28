(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto Sj_stage2_wkit Sj_stage2_hex4 Sj_stage2_strrm Sj_stage2_strr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_shadow_dig | s2_load_buf | s2_load_esc | s2_load_dig | s2_load_dig2 | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section StrR2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Hypothesis CC : a_cc E.
  Hypothesis HROOM16 : (e_lo E + 16 <= e_spa E)%Z.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Ltac gEnv h := subst h; cbn [gapp s2_ghost e_scap e_tcap e_bs e_idxs e_sbs e_tws e_lo e_sp e_spa e_SBUF e_TAPE e_IDX e_BUF e_THIS e_DOC e_OC e_IA e_FF] in *.

  Lemma seg_root_str : forall (Q : machine_state -> Prop),
    e_tok E 0 = c_quote -> Z.of_nat (length (e_tws E)) = 1%Z -> Z.of_nat (length (e_sbs E)) = 0%Z ->
    exit_k (gapp E [tword t_str (0%Z)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) 0 d -> Z.of_nat (length cb) = d ->
       docend_k (gapp (gapp E [tword t_str (0%Z)] []) [] (srec d cb)) Q (mkst 1 0 2 (0 + d + 5) [])) ->
    rootprim_k E Q 0xbe048.
  Proof using OK SHZ CC HROOM16.
    intros Q HQ GLT GLS KX KE. unfold rootprim_k. intros until m1. intros HM.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. pose proof (ok_tcap _ OK) as HTC. pose proof (ok_scap _ OK) as HSC.
    assert (HKN : (0 < e_n E)%Z) by lia.
    destruct (tok_string _ _ (ok_s1 _ OK) 0 ltac:(lia) HQ) as (j & HC & HJ1 & HJ2).
    pose proof (off_range _ _ (ok_s1 _ OK) 0 ltac:(lia)) as HO. pose proof (off_range _ _ (ok_s1 _ OK) (0 + 1) ltac:(lia)) as HO1.
    s2_env OK.
    pose proof HM as HMo. s2_open_mem HMo.
    wrun_note_to 0xbe0ec%Z.

    s2_str_word (0%Z). s2_tape1 (tword t_str (0%Z)). s2_ghost_bundle.
    set (E' := gapp E [tword t_str (0%Z)] []) in *.
    assert (OK' : env_ok E') by (apply env_ok_gapp; exact OK).
    assert (HGS' : Z.of_nat (length (e_sbs E')) = 0%Z) by (subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia).
    assert (HROOM : (0 <= 0 /\ 0 + (j - e_off E' 0) + 4 <= e_scap E')%Z) by (gEnv E'; lia).
    assert (KE' : forall d' cb, (0 <= d' <= j - e_off E' 0 - 1)%Z -> Z.of_nat (length cb) = d' -> docend_k (gapp E' [] (srec d' cb)) Q (mkst 1 0 2 (0 + d' + 5) [])).
    { intros d' cb Hd' Hcb. apply (KE d' cb); [|exact Hcb]. exists j. split; [exact HC | gEnv E'; lia]. }
    pose proof (strr_loop E' OK' SHZ CC Q (e_TAPE E' + 8 * 2)%Z (e_IDX E' + 4 * 1)%Z 0%Z [] KX HGS'
                  (e_off E' 0) j HROOM ltac:(gEnv E'; lia) eq_refl eq_refl eq_refl HROOM16 KE' (S (Z.to_nat (j - e_off E' 0))) (e_off E' 0 + 1)%Z 0%Z) as L.
    unfold Sj_stage2_strrm.headk in L.
    replace (e_SBUF E' + 0 + 4 + 0)%Z with (e_SBUF E' + 4)%Z in L by lia.
    replace (e_SBUF E' + 0 + 4)%Z with (e_SBUF E' + 4)%Z in L by lia.
    replace (e_SBUF E' + 0)%Z with (e_SBUF E')%Z in L by lia.
    replace (e_BUF E' + (e_off E' 0 + 1))%Z with (e_BUF E' + e_off E' 0 + 1)%Z in L by lia.
    replace (e_TAPE E' + 8 * 2)%Z with (e_TAPE E' + 16)%Z in L by lia.
    replace (e_IDX E' + 4 * 1)%Z with (e_IDX E' + 4)%Z in L by lia.
    eapply L; [apply PS_init; exact HC | gEnv E'; lia | ].
    wk_close.
  Qed.
End StrR2.
