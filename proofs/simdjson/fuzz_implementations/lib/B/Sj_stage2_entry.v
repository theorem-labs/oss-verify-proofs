(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_tables2 Sj_stage2_exitw.
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

Section Entry.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition impl_cells0 (docv : word) : list cell :=
    [C8 (e_vptr E); C4 (wz (e_n E)); CB 4 (e_p12 E); C8 (wz (e_IDX E)); C4 (e_nxt0 E); CB 4 (e_p28 E); C8 (e_capv E); C8 (wz 1024);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (e_p50 E); C8 (wz (e_OC E)); C8 (wz (e_IA E)); C8 (wz (e_BUF E));
     C8 (wz (e_len E)); C8 docv].

  Definition fr_cells0 (js : list (list byte)) : list cell := map (CB 8) js.

  Definition MEM1 (docv : word) (fc : bv 32) (m1 : mem) : Prop :=
    frm0 fc /\
    (exists j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j208 j216 j224 j232 j240 j248 j256 j264 j272 j280 j288 j296 j304,
       rw_cells bsegs m1 (e_spa E)
         (fr_cells0 [j0; j8; j16; j24; j32; j40; j48; j56; j64; j72; j80; j88; j96; j104; j112; j120; j128; j136; j144; j152; j160; j168; j176; j184; j192; j200; j208; j216; j224; j232; j240; j248; j256; j264; j272; j280; j288; j296; j304])) /\
    rw_cells bsegs m1 (bv_unsigned (e_sp E) + -104) (saved_cells E) /\
    stk bsegs m1 (e_spa E + 312) (bv_unsigned (e_sp E) + -104) /\
    wr_at bsegs m1 (e_FF E) 8 /\
    rw_cells bsegs m1 (e_THIS E) (impl_cells0 docv) /\
    rw_cells bsegs m1 (e_DOC E) (doc_cells E) /\
    u32arr bsegs m1 (e_IDX E) (e_iws E) /\
    bytes_at bsegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
    wr_at bsegs m1 (e_TAPE E) (8 * e_tcap E) /\
    wr_at bsegs m1 (e_SBUF E) (e_scap E) /\
    (exists ocs, u32arr bsegs m1 (e_OC E) ocs /\ length ocs = 2048%nat) /\
    (exists ias, u8arr bsegs m1 (e_IA E) ias /\ length ias = 1024%nat) /\
    mem_inv bsegs m1 /\ munch (s2_W E) (e_m0 E) m1 /\ wmono bsegs (e_m0 E) m1 /\
    stk bsegs m1 (e_lo E) (e_spa E) /\
    tape_img E (e_tws E) (e_sbs E) m1.

  Lemma seg_entry_gen : forall (Q : machine_state -> Prop) docv
      x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM1 docv fc m1 ->
    (is_numstart (e_tok E 0) = false -> exit_kw E Q) ->
    (forall pc, pc = root_target (e_tok E 0) -> pc <> 0xdbc94%Z -> rootprim_k E Q pc) ->
    evt bsegs Q
      (S2R E 0xc5778 x1 x5 x6 x7 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (Z.shiftr (e_THIS E + 88) 3)) x11 x12 x13 (Z_to_bv 64 (e_THIS E + 88))
           (Z_to_bv 64 (e_FF E)) x16 x17 x18 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e_DOC E)) x22 x23
           (Z_to_bv 64 (e_THIS E)) x25 (Z_to_bv 64 (e_FF E)) x27 x28 x29 x30 x31 F fc m1).
  Proof using OK SHZ.
    intros Q docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m1 HM KXo KR.
    destruct HM as (FRM & (j0 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & j80 & j88 & j96 & j104 & j112 & j120 & j128 & j136 & j144 & j152 & j160 & j168 & j176 & j184 & j192 & j200 & j208 & j216 & j224 & j232 & j240 & j248 & j256 & j264 & j272 & j280 & j288 & j296 & j304 & FR)
                    & SAV & GAP & FFW & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & (ocs & OCA & OCL) & (ias & IAA & IAL) & MI & MU & WM & ST & TIMG).
    unfold fr_cells0 in FR. cbn [map] in FR. unfold saved_cells in SAV. unfold impl_cells0 in IMPL. unfold doc_cells in DOCC. unfold s2_W in MU.
    pose proof (padded_bytes_blen (e_bs E)) as PBL. pose proof (ok_bytes _ OK) as BOK.
    pose proof (n_bound E OK) as HN. s2_env OK.
    grun.
    if_true.
    grun.
    if_cases K0; zify_cond K0; [lia|].
    pose proof (off_bound E OK 0 ltac:(lia)) as HO0. pose proof (tok_range E OK 0) as HT0.
    grun_to 0xc5c68%Z.
    replace (Z.shiftr (e_TAPE E - e_TAPE E) 3) with 0%Z by (rewrite Z.sub_diag; reflexivity).
    s2_cur_mem ltac:(fun m =>
      pose proof (u32arr_store_ok bsegs m (e_OC E) ocs 0 (wa (e_OC E)) OCA ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK0).
    zstep.
    s2_old_mem ltac:(fun m => pose proof (u32arr_write bsegs m (e_OC E) ocs 0 (Z_to_bv 64 0) OCA ltac:(lia)) as OCA').
    replace (e_OC E + 4 * 0)%Z with (e_OC E) in OCA' by lia.
    store_done.
    grun_to 0xc5cb8%Z.
    s2_cur_mem ltac:(fun m =>
      pose proof (u32arr_store_ok bsegs m (e_OC E) _ 1 (wa (e_OC E + 4)) OCA' ltac:(rewrite upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK1).
    zstep.
    s2_old_mem ltac:(fun m => pose proof (u32arr_write bsegs m (e_OC E) _ 1 (Z_to_bv 64 0) OCA' ltac:(rewrite upd_length; lia)) as OCA'').
    replace (e_OC E + 4 * 1)%Z with (e_OC E + 4)%Z in OCA'' by lia.
    store_done.
    grun_to 0xc5cec%Z.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m 0 IDXA ltac:(lia)) as RD1;
      pose proof (tok_read E OK m 0 BUFRO ltac:(lia)) as RD2).
    replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in RD1 by lia.
    grun.
    fold (tok (e_bs E) (e_idxs E) 0) in *.
    if_cases K1; zify_cond K1.
    2:{
        assert (KX : exit_kw E Q).
        { apply KXo. unfold is_numstart, is_digit, c_minus.
          destruct (Z_lt_dec (e_tok E 0) 34) as [L|L].
          - replace (e_tok E 0 =? 45)%Z with false by (symmetry; apply Z.eqb_neq; lia).
            replace (48 <=? e_tok E 0)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
          - rewrite Z.mod_small in K1 by lia.
            replace (e_tok E 0 =? 45)%Z with false by (symmetry; apply Z.eqb_neq; lia).
            replace (e_tok E 0 <=? 57)%Z with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. reflexivity. }
        grun_to 0xdbc94%Z. gexitw KX. }
    assert (HR : (34 <= e_tok E 0 <= 123)%Z).
    { destruct (Z_lt_dec (e_tok E 0) 34) as [L|L].
      - replace ((e_tok E 0 + -34) mod 18446744073709551616)%Z with (e_tok E 0 + -34 + 18446744073709551616)%Z in K1; [lia|].
        symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia.
      - rewrite Z.mod_small in K1 by lia. lia. }
    pose proof (jt_range (e_tok E 0 - 34) ltac:(lia)) as HJR.
    grun_to 0xc5d6c%Z.
    s2_cur_mem ltac:(fun m =>
      pose proof (jt_read m (e_tok E 0 - 34) (wa (4 * (e_tok E 0 + -34) + 146912)) MI ltac:(lia) ltac:(unfold wa, T_JT; f_equal; lia)) as RJ).
    grun.
    replace (jt (e_tok E 0 - 34) + 146912)%Z with (root_target (e_tok E 0)) by (rewrite <- jt_target by lia; unfold T_JT; lia).

    assert (HCL : root_target (e_tok E 0) = 0xdbc94%Z \/
                  (root_target (e_tok E 0) <> 0xdbc94%Z /\ (0 <= root_target (e_tok E 0) < 2 ^ 64)%Z /\ (root_target (e_tok E 0) mod 2 = 0)%Z)).
    { unfold root_target.
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      first [ left; reflexivity | right; split; [discriminate | split; [lia | reflexivity]] ]. }
    destruct HCL as [HX | (HNX & HRG & HEV)].
    - assert (KX : exit_kw E Q).
      { apply KXo. unfold root_target in HX. unfold is_numstart, is_digit, c_minus.
        destruct (e_tok E 0 =? 34)%Z; [discriminate HX|].
        destruct ((e_tok E 0 =? 45) || (48 <=? e_tok E 0) && (e_tok E 0 <=? 57))%Z; [discriminate HX| reflexivity]. }
      rewrite HX. rewrite (ret_pc_even 0xdbc94%Z) by (first [lia | reflexivity]).
      gexitw KX.
    - rewrite (ret_pc_even _ HRG HEV).
      eapply (KR _ eq_refl HNX).
      s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil].
  Qed.

  Lemma seg_entry : forall (Q : machine_state -> Prop) docv
      x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM1 docv fc m1 ->
    exit_kw E Q ->
    (forall pc, pc = root_target (e_tok E 0) -> pc <> 0xdbc94%Z -> rootprim_k E Q pc) ->
    evt bsegs Q
      (S2R E 0xc5778 x1 x5 x6 x7 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (Z.shiftr (e_THIS E + 88) 3)) x11 x12 x13 (Z_to_bv 64 (e_THIS E + 88))
           (Z_to_bv 64 (e_FF E)) x16 x17 x18 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e_DOC E)) x22 x23
           (Z_to_bv 64 (e_THIS E)) x25 (Z_to_bv 64 (e_FF E)) x27 x28 x29 x30 x31 F fc m1).
  Proof using OK SHZ.
    intros Q docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m1 HM KX KR.
    apply (seg_entry_gen Q docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m1 HM (fun _ => KX) KR).
  Qed.

  Lemma seg_entry_num : forall (Q : machine_state -> Prop) docv
      x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM1 docv fc m1 ->
    is_numstart (e_tok E 0) = true ->
    rootprim_k E Q 0xc5d88 ->
    evt bsegs Q
      (S2R E 0xc5778 x1 x5 x6 x7 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (Z.shiftr (e_THIS E + 88) 3)) x11 x12 x13 (Z_to_bv 64 (e_THIS E + 88))
           (Z_to_bv 64 (e_FF E)) x16 x17 x18 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e_DOC E)) x22 x23
           (Z_to_bv 64 (e_THIS E)) x25 (Z_to_bv 64 (e_FF E)) x27 x28 x29 x30 x31 F fc m1).
  Proof using OK SHZ.
    intros Q docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m1 HM HN KR.
    apply (seg_entry_gen Q docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m1 HM); [intros HF; congruence|].
    intros pc HPC _. subst pc. unfold root_target.
    unfold is_numstart, is_digit, c_minus in HN.
    destruct (e_tok E 0 =? 34)%Z eqn:T34.
    { apply Z.eqb_eq in T34. rewrite T34 in HN. discriminate HN. }
    rewrite HN. exact KR.
  Qed.
End Entry.
