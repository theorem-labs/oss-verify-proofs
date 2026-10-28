(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto Sj_stage2_wkit Sj_stage2_objf Sj_stage2_stram Sj_stage2_stra.
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

Section StrA2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Ltac gEnv h := subst h; cbn [gapp s2_ghost e_scap e_tcap e_bs e_idxs e_sbs e_tws e_lo e_sp e_spa e_SBUF e_TAPE e_IDX e_BUF e_THIS e_DOC e_OC e_IA e_FF] in *.

  Lemma seg_key_a : forall (Q : machine_state -> Prop) (s : st),
    INV ObjBegin s -> (depth s + 1 < MAXDEPTH)%Z -> e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    (forall hv, exit_k (gapp E [hv; tword t_str (sb s)] []) Q) ->
    (forall d hv, string_ok (e_bs E) (e_idxs E) (k s) d -> keyend_k (gapp E [hv; tword t_str (sb s)] []) Q (k s) (depth s + 1) (W s + 2) (sb s) d ((false, W s) :: scopes s)) ->
    keya_k E Q s.
  Proof using OK SHZ.
    intros Q s HI HDP HQ GLT GLS KX KE. unfold keya_k.
    intros xra xt1 xt2 xa4 xa6 xa7 xs7 xs9 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j176 j272 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    destruct (inv_sb _ _ _ _ HI) as [HSB0 HSB]. cbn [slackW slackS] in *. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
    assert (HKN : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK | rewrite HQ; unfold c_quote; lia]).
    destruct (tok_string _ _ (ok_s1 _ OK) (k s) ltac:(lia) HQ) as (j & HC & HJ1 & HJ2).
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HO. pose proof (off_range _ _ (ok_s1 _ OK) (k s + 1) ltac:(lia)) as HO1.
    s2_env OK.
    s2_open_mem HM.

    grun_to 0xc0148%Z.
    s2_cur_mem ltac:(fun m =>
      pose proof (u32arr_store_ok asegs m (e_OC E) ocs (2 * (depth s + 1) + 1) (wa (e_OC E + 8 * (depth s + 1) + 4)) OCA ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as SOK2).
    zstep.
    s2_old_mem ltac:(fun m =>
      pose proof (u32arr_write asegs m (e_OC E) ocs (2 * (depth s + 1) + 1) (Z_to_bv 64 1) OCA ltac:(lia)) as OCA').
    replace (e_OC E + 4 * (2 * (depth s + 1) + 1))%Z with (e_OC E + 8 * (depth s + 1) + 4)%Z in OCA' by lia.
    store_done.

    s2_cur_mem ltac:(fun m => assert (HM2 : MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * k s)); CB 8 j176; C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272] ((false, W s) :: scopes s) fc m) by s2_close_auto;
      revert HM2; wk_clear m; intro HM2; pose proof HM2 as HMo; s2_open_mem HMo).
    wrun_note_to 0xc01dc%Z.

    s2_str_word (sb s). s2_tape_hole1 (tword t_str (sb s)). s2_ghost_bundle.
    set (E' := gapp E [bv_unsigned hv; tword t_str (sb s)] []) in *.
    specialize (KX (bv_unsigned hv)). fold E' in KX.
    assert (OK' : env_ok E') by (apply env_ok_gapp; exact OK).
    assert (HGS' : Z.of_nat (length (e_sbs E')) = sb s) by (subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia).
    assert (HROOM : (0 <= sb s /\ sb s + (j - e_off E' (k s)) + 4 <= e_scap E')%Z) by (gEnv E'; lia).
    assert (KE' : forall d', (0 <= d' <= j - e_off E' (k s) - 1)%Z -> keyend_k E' Q (k s) (depth s + 1) (W s + 2) (sb s) d' ((false, W s) :: scopes s)).
    { intros d' Hd'. apply (KE d' (bv_unsigned hv)). exists j. split; [exact HC | gEnv E'; lia]. }
    pose proof (stra_loop E' OK' SHZ Q (depth s + 1)%Z (e_TAPE E' + 8 * (W s + 2))%Z (e_IDX E' + 4 * k s)%Z (sb s) ((false, W s) :: scopes s) KX HGS'
                  (e_off E' (k s)) j (k s) (W s + 2)%Z HROOM ltac:(gEnv E'; lia) eq_refl eq_refl KE' (S (Z.to_nat (j - e_off E' (k s)))) (e_off E' (k s) + 1)%Z 0%Z) as L.
    unfold Sj_stage2_stram.headk in L.
    replace (e_SBUF E' + sb s + 4 + 0)%Z with (e_SBUF E' + sb s + 4)%Z in L by lia.
    replace (e_BUF E' + (e_off E' (k s) + 1))%Z with (e_BUF E' + e_off E' (k s) + 1)%Z in L by lia.
    eapply L; [apply PS_init; exact HC | gEnv E'; lia | ].
    replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z in * by lia.
    wk_close.
  Qed.
End StrA2.
