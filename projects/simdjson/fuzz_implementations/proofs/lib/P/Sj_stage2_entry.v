(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs Sj_tables Sj_tables2 Sj_stage2_auto2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_store_done_wr_v2.

Section Entry.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition impl_cells0 (docv : word) : list cell :=
    [C8 (e_vptr E); C4 (Z_to_bv 64 (e_n E)); CB 4 (e_p12 E); C8 (Z_to_bv 64 (e_IDX E)); C4 (e_nxt0 E); CB 4 (e_p28 E); C8 (e_capv E); C8 (Z_to_bv 64 1024);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (e_p50 E); C8 (Z_to_bv 64 (e_OC E)); C8 (Z_to_bv 64 (e_IA E)); C8 (Z_to_bv 64 (e_BUF E));
     C8 (Z_to_bv 64 (e_len E)); C8 docv].

  Definition MEM0 (docv : word) (fc : bv 32) (m1 : mem) : Prop :=
    frm0 fc /\ m1 = e_m0 E /\
    rw_cells psegs m1 (e_THIS E) (impl_cells0 docv) /\
    rw_cells psegs m1 (e_DOC E) (doc_cells E) /\
    u32arr psegs m1 (e_IDX E) (e_iws E) /\
    bytes_at psegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
    wr_at psegs m1 (e_TAPE E) (8 * e_tcap E) /\
    wr_at psegs m1 (e_SBUF E) (e_scap E) /\
    (exists ocs, u32arr psegs m1 (e_OC E) ocs /\ length ocs = 2048%nat) /\
    (exists ias, u8arr psegs m1 (e_IA E) ias /\ length ias = 1024%nat) /\
    mem_inv psegs m1 /\ stk psegs m1 (e_lo E) (e_SP E) /\
    (exists jlo jhi, rw_cells psegs m1 (e_SP E) [CB 80 jlo; CB 184 (e_j80 E); CB 104 jhi]) /\
    tape_img E (e_tws E) (e_sbs E) m1.

  Definition rootprim_k (Q : machine_state -> Prop) (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
           j0 j1 j2 j3 j4 j5 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (Z_to_bv 64 (e_IDX E + 4));
                         C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_SBUF E)); CB 8 j9] [] fc m1 ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 (Z_to_bv 64 (e_off E 0)) xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11
                       xt3 xt4 xt5 xt6 F fc m1).

  Lemma seg_entry : forall (Q : machine_state -> Prop) docv
      x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM0 docv fc m1 -> Z.of_nat (length (e_tws E)) = 1%Z ->
    exit_k E Q ->
    (e_tok E 0 = c_quote -> rootprim_k Q 0x44dd4) ->
    (is_numstart (e_tok E 0) = true -> rootprim_k Q 0x44630) ->
    (e_tok E 0 = c_f -> rootprim_k Q 0x451c8) -> (e_tok E 0 = c_n -> rootprim_k Q 0x44bc0) -> (e_tok E 0 = c_t -> rootprim_k Q 0x44c80) ->
    (e_tok E 0 = c_lbrace -> e_tok E 1 <> c_rbrace -> lab_k E Q 0x45cc0 (mkst 1 0 1 0 [])) ->
    (e_tok E 0 = c_lbrace -> e_tok E 1 = c_rbrace -> docend_k (empty_env E 123 1) Q (mkst 2 0 3 0 [])) ->
    (e_tok E 0 = c_lbrack -> e_tok E 1 <> c_rbrack -> arrbegin_k E Q (mkst 1 0 1 0 [])) ->
    (e_tok E 0 = c_lbrack -> e_tok E 1 = c_rbrack -> docend_k (empty_env E 91 1) Q (mkst 2 0 3 0 [])) ->
    evt psegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x44548) fc None m1 (seg_rom psegs)).
  Proof using OK.
    intros Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM GLT KX KRS KRN KRF KRNU KRT KOB KOE KAB KAE.
    destruct HM as (FRM & EM0 & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & (ocs & OCA & OCL) & (ias & IAA & IAL) & MI & ST & (jlo & jhi & FR) & TIMG).
    unfold impl_cells0 in IMPL. unfold doc_cells in DOCC.
    pose proof (munch_refl (s2_W E) m1) as MU. pose proof (wmono_refl psegs m1) as WM. rewrite EM0 in MU at 1. rewrite EM0 in WM at 1.
    unfold s2_W in MU.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    pose proof (padded_bytes_blen (e_bs E)) as PBL.
    apply (rw_cells_split_CB psegs m1 _ [] 80 jlo [CB 184 (e_j80 E); CB 104 jhi] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    apply (rw_cells_split_CB psegs m1 _ [_;_;_;_;_;_;_;_;_;_;_] 104 jhi [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    step. do 13 step. step. step.
    do 5 zstep. zstep. if_true. zstep. s2norm.
    if_cases K0; zify_cond K0; [lia|].
    pose proof (off_bound E OK 0 ltac:(lia)) as HO0. pose proof (tok_range E OK 0) as HT0.
    s2_cur_mem ltac:(fun m =>
      pose proof (u32arr_store_ok psegs m (e_OC E) ocs 0 (wa (e_OC E)) OCA ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK0).
    zstep. zstep. zstep.
    s2_old_mem ltac:(fun m => pose proof (u32arr_write psegs m (e_OC E) ocs 0 (Z_to_bv 64 0) OCA ltac:(lia)) as OCA').
    replace (e_OC E + 4 * 0)%Z with (e_OC E) in OCA' by lia.
    store_done.
    s2_cur_mem ltac:(fun m =>
      pose proof (u32arr_store_ok psegs m (e_OC E) _ 1 (wa (e_OC E + 4)) OCA' ltac:(rewrite upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK1).
    zstep.
    s2_old_mem ltac:(fun m => pose proof (u32arr_write psegs m (e_OC E) _ 1 (Z_to_bv 64 0) OCA' ltac:(rewrite upd_length; lia)) as OCA'').
    replace (e_OC E + 4 * 1)%Z with (e_OC E + 4)%Z in OCA'' by lia.
    store_done.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m 0 IDXA ltac:(lia)) as RD1;
      pose proof (tok_read E OK m 0 BUFRO ltac:(lia)) as RD2).
    replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in RD1 by lia.
    zstep. s2norm. zstep. zstep. s2norm. zstep. zstep. zstep.
    if_cases K1; zify_cond K1.
    2:{
        zstep. zstep. zstep. s2_err_exit KX.
        eapply (MEMX_of_MEMI E (e_nxt0 E) _ _ _ _ _ _ _ _ _ _ []); [s2_close_mem | reflexivity ..];
          [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
    assert (HR : (34 <= e_tok E 0 <= 123)%Z).
    { destruct (Z_lt_dec (e_tok E 0) 34) as [L|L].
      - replace ((e_tok E 0 + -34) mod 18446744073709551616)%Z with (e_tok E 0 + -34 + 18446744073709551616)%Z in K1; [lia|].
        symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia.
      - rewrite Z.mod_small in K1 by lia. lia. }
    zstep. zstep. s2norm. zstep. zstep. zstep.
    pose proof (jt_range (e_tok E 0 - 34) ltac:(lia)) as HJR.
    s2_cur_mem ltac:(fun m =>
      pose proof (jt_read m (e_tok E 0 - 34) (wa (4 * (e_tok E 0 + -34) + 82408)) MI ltac:(lia) ltac:(unfold wa, T_JT; f_equal; lia)) as RJ).
    zstep. s2norm. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (jt (e_tok E 0 - 34) + 82408)%Z with (root_target (e_tok E 0)) by (rewrite <- jt_target by lia; unfold T_JT; lia).
    unfold root_target.
    destruct (e_tok E 0 =? 34)%Z eqn:T34.
    { apply Z.eqb_eq in T34. zstep. eapply (KRS T34).
      s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
    destruct ((e_tok E 0 =? 45) || (48 <=? e_tok E 0) && (e_tok E 0 <=? 57))%Z eqn:TNUM.
    { zstep. eapply (KRN TNUM).
      s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
    destruct (e_tok E 0 =? 91)%Z eqn:T91.
    { apply Z.eqb_eq in T91. zstep.
      pose proof (off_bound E OK (e_n E - 1) ltac:(lia)) as HOl. pose proof (tok_range E OK (e_n E - 1)) as HTl.
      pose proof (off_bound E OK 1 ltac:(lia)) as HO1. pose proof (tok_range E OK 1) as HT1.
      s2_cur_mem ltac:(fun m =>
        pose proof (idx_read E OK m (e_n E - 1) IDXA ltac:(lia)) as RD3;
        pose proof (tok_read E OK m (e_n E - 1) BUFRO ltac:(lia)) as RD4;
        pose proof (idx_read E OK m 1 IDXA ltac:(lia)) as RD5;
        pose proof (tok_read E OK m 1 BUFRO ltac:(lia)) as RD6).
      zstep. zstep. zstep. s2norm. zstep. zstep. s2norm. zstep. zstep. s2norm. zstep. zstep.
      if_cases K2; zify_cond K2.
      2:{ zstep. zstep. zstep. s2_err_exit KX.
          eapply (MEMX_of_MEMI E (e_nxt0 E) _ _ _ _ _ _ _ _ _ _ []); [s2_close_mem | reflexivity ..];
            [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
      zstep. zstep. s2norm. zstep. zstep. s2norm. zstep. zstep.
      if_cases K3; zify_cond K3.
      2:{
        zstep. zstep.
        replace (Z_to_bv 64 (e_SBUF E)) with (Z_to_bv 64 (e_SBUF E + 0)) by (f_equal; lia).
        eapply (KAB T91 K3). cbn [scopes k W].
        eapply (MEMI_forget8 E _ [_;_;_;_;_;_] _ [_;_;_]); cycle 1;
          [eapply (MEMI_forget8 E _ [_;_;_;_;_;_;_;_] _ [_]); cycle 1;
             [s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil] | reflexivity]
          | reflexivity]. }

      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. s2norm. s2_note_store. s2_store_done_wr. zstep. s2norm. s2_note_store. s2_store_done_wr. zstep. zstep. zstep.
      s2_cur_mem ltac:(fun m =>
        apply (tape_img_app2 E _ _ m (cword 91 (1 + 2) 0) (tword (91 + 2) 1) (e_TAPE E + 8)%Z (e_TAPE E + 16)%Z OK) in TIMG;
        [ | exact NEWCH | exact NEWCH0 | lia | lia | lia | vm_compute; split; [discriminate | reflexivity] | vm_compute; split; [discriminate | reflexivity] ]).
      eapply (KAE T91 K3). cbn [k W].
      eapply (MEMI_forget8 _ _ [_;_;_;_;_;_;_;_] _ [_]); cycle 1;
        [s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil] | reflexivity]. }
    destruct (e_tok E 0 =? 102)%Z eqn:T102.
    { apply Z.eqb_eq in T102. zstep. eapply (KRF T102).
      s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
    destruct (e_tok E 0 =? 110)%Z eqn:T110.
    { apply Z.eqb_eq in T110. zstep. eapply (KRNU T110).
      s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
    destruct (e_tok E 0 =? 116)%Z eqn:T116.
    { apply Z.eqb_eq in T116. zstep. eapply (KRT T116).
      s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
    destruct (e_tok E 0 =? 123)%Z eqn:T123.
    { apply Z.eqb_eq in T123. zstep.
      pose proof (off_bound E OK (e_n E - 1) ltac:(lia)) as HOl. pose proof (tok_range E OK (e_n E - 1)) as HTl.
      pose proof (off_bound E OK 1 ltac:(lia)) as HO1. pose proof (tok_range E OK 1) as HT1.
      s2_cur_mem ltac:(fun m =>
        pose proof (idx_read E OK m (e_n E - 1) IDXA ltac:(lia)) as RD3;
        pose proof (tok_read E OK m (e_n E - 1) BUFRO ltac:(lia)) as RD4;
        pose proof (idx_read E OK m 1 IDXA ltac:(lia)) as RD5;
        pose proof (tok_read E OK m 1 BUFRO ltac:(lia)) as RD6).
      zstep. zstep. zstep. s2norm. zstep. zstep. s2norm. zstep. zstep. s2norm. zstep. zstep.
      if_cases K2; zify_cond K2.
      2:{ zstep. zstep. zstep. s2_err_exit KX.
          eapply (MEMX_of_MEMI E (e_nxt0 E) _ _ _ _ _ _ _ _ _ _ []); [s2_close_mem | reflexivity ..];
            [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }
      zstep. zstep. s2norm. zstep. zstep. s2norm. zstep.
      if_cases K3; zify_cond K3.
      {
        zstep. zstep. zstep.
        replace (Z_to_bv 64 (e_SBUF E)) with (Z_to_bv 64 (e_SBUF E + 0)) by (f_equal; lia).
        eapply (KOB T123 K3). cbn [scopes].
        eapply MEMJ_of_MEMI; [s2_close_mem | reflexivity ..];
          [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil]. }

      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. s2norm. s2_note_store. s2_store_done_wr. zstep. s2norm. s2_note_store. s2_store_done_wr. zstep. zstep. zstep.
      s2_cur_mem ltac:(fun m =>
        apply (tape_img_app2 E _ _ m (cword 123 (1 + 2) 0) (tword (123 + 2) 1) (e_TAPE E + 8)%Z (e_TAPE E + 16)%Z OK) in TIMG;
        [ | exact NEWCH | exact NEWCH0 | lia | lia | lia | vm_compute; split; [discriminate | reflexivity] | vm_compute; split; [discriminate | reflexivity] ]).
      eapply (KOE T123 K3). cbn [k W].
      eapply (MEMI_forget8 _ _ [_;_;_;_;_;_;_;_] _ [_]); cycle 1;
        [s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil] | reflexivity]. }

    zstep. s2_err_exit KX.
    eapply (MEMX_of_MEMI E (e_nxt0 E) _ _ _ _ _ _ _ _ _ _ []); [s2_close_mem | reflexivity ..];
      [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil].
  Qed.
End Entry.
