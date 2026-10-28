(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_wkit Sj_stage2_objf Sj_stage2_strbm Sj_stage2_strb.
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

Section StrB2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Ltac gEnv h := subst h; cbn [gapp s2_ghost e_scap e_tcap e_bs e_idxs e_sbs e_tws e_lo e_sp e_spa e_SBUF e_TAPE e_IDX e_BUF e_THIS e_DOC e_OC e_IA e_FF] in *.

  Lemma seg_key_b : forall (Q : machine_state -> Prop) (s0 : st),
    INV ObjCont s0 -> e_tok E (k s0) = c_comma -> e_tok E (k s0 + 1) = c_quote -> Z.of_nat (length (e_tws E)) = W s0 -> Z.of_nat (length (e_sbs E)) = sb s0 ->
    exit_k (gapp E [tword t_str (sb s0)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s0 + 1) d -> Z.of_nat (length cb) = d ->
       keyend_k (gapp (gapp E [tword t_str (sb s0)] []) [] (srec d cb)) Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d (scopes s0)) ->
    keyb_k E Q (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
  Proof using OK SHZ.
    intros Q s0 HI HC0 HQ GLT GLS KX KE. unfold keyb_k. cbn [k depth W sb scopes].
    intros until m1. intros HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW.
    destruct (inv_sb _ _ _ _ HI) as [HSB0 _]. cbn [slackW slackS] in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
    assert (HKN : (k s0 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK | rewrite HC0; unfold c_comma; lia]).
    assert (HKN1 : (k s0 + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia | rewrite HQ; unfold c_quote; lia]).
    destruct (tok_string _ _ (ok_s1 _ OK) (k s0 + 1) ltac:(lia) HQ) as (j & HC & HJ1 & HJ2).
    pose proof (string_pre _ _ (ok_s1 _ OK) ObjCont s0 1 HI ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as HPRE.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s0 + 1) ltac:(lia)) as HO. pose proof (off_range _ _ (ok_s1 _ OK) (k s0 + 1 + 1) ltac:(lia)) as HO1.
    s2_env OK.
    pose proof HM as HMo. s2_open_mem HMo.
    wrun_note_to 0xcd578%Z.

    s2_str_word (sb s0). s2_tape1 (tword t_str (sb s0)). s2_ghost_bundle.
    set (E' := gapp E [tword t_str (sb s0)] []) in *.
    assert (OK' : env_ok E') by (apply env_ok_gapp; exact OK).
    assert (HGS' : Z.of_nat (length (e_sbs E')) = sb s0) by (subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia).
    assert (HROOM : (0 <= sb s0 /\ sb s0 + (j - e_off E' (k s0 + 1)) + 4 <= e_scap E')%Z) by (gEnv E'; lia).
    assert (KE' : forall d' cb, (0 <= d' <= j - e_off E' (k s0 + 1) - 1)%Z -> Z.of_nat (length cb) = d' -> keyend_k (gapp E' [] (srec d' cb)) Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d' (scopes s0)).
    { intros d' cb Hd' Hcb. apply (KE d' cb); [|exact Hcb]. exists j. split; [exact HC | gEnv E'; lia]. }
    pose proof (strb_loop E' OK' SHZ Q (depth s0) (e_TAPE E' + 8 * (W s0 + 1))%Z (e_IDX E' + 4 * (k s0 + 1))%Z (sb s0) (scopes s0) KX HGS'
                  (e_off E' (k s0 + 1)) j (k s0 + 1)%Z (W s0 + 1)%Z HROOM ltac:(gEnv E'; lia) eq_refl eq_refl KE' (S (Z.to_nat (j - e_off E' (k s0 + 1)))) (e_off E' (k s0 + 1) + 1)%Z 0%Z) as L.
    unfold Sj_stage2_strbm.headk in L.
    replace (e_SBUF E' + sb s0 + 4 + 0)%Z with (e_SBUF E' + sb s0 + 4)%Z in L by lia.
    replace (e_BUF E' + (e_off E' (k s0 + 1) + 1))%Z with (e_BUF E' + e_off E' (k s0 + 1) + 1)%Z in L by lia.
    eapply L; [apply PS_init; exact HC | gEnv E'; lia | ].
    subst E'. wk_close.
  Qed.
End StrB2.
