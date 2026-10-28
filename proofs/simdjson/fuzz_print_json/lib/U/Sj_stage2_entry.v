(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_tables2.
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
    rw_cells usegs m1 (e_THIS E) (impl_cells0 docv) /\
    rw_cells usegs m1 (e_DOC E) (doc_cells E) /\
    u32arr usegs m1 (e_IDX E) (e_iws E) /\
    bytes_at usegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
    wr_at usegs m1 (e_TAPE E) (8 * e_tcap E) /\
    wr_at usegs m1 (e_SBUF E) (e_scap E) /\
    (exists ocs, u32arr usegs m1 (e_OC E) ocs /\ length ocs = 2048%nat) /\
    (exists ias, u8arr usegs m1 (e_IA E) ias /\ length ias = 1024%nat) /\
    mem_inv usegs m1 /\ stk usegs m1 (e_lo E) (e_SP E) /\
    (exists jlo jhi, rw_cells usegs m1 (e_SP E) [CB 80 jlo; CB 184 (e_j80 E); CB 104 jhi]) /\
    tape_img E (e_tws E) (e_sbs E) m1.

  Lemma seg_entry_gen : forall (Q : machine_state -> Prop) docv
      x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM0 docv fc m1 ->
    (is_numstart (e_tok E 0) = false -> exit_k E Q) ->
    (forall pc, pc = root_target (e_tok E 0) -> pc <> 0x4be14%Z -> rootprim_k E Q pc) ->
    evt usegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x43550) fc None m1 (seg_rom usegs)).
  Proof using OK.
    intros Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM KXo KR.
    destruct HM as (FRM & EM0 & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & (ocs & OCA & OCL) & (ias & IAA & IAL) & MI & ST & (jlo & jhi & FR) & TIMG).
    unfold impl_cells0 in IMPL. unfold doc_cells in DOCC.
    pose proof (munch_refl (s2_W E) m1) as MU. pose proof (wmono_refl usegs m1) as WM. rewrite EM0 in MU at 1. rewrite EM0 in WM at 1.
    unfold s2_W in MU.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    pose proof (padded_bytes_blen (e_bs E)) as PBL. pose proof (ok_bytes _ OK) as BOK.
    apply (rw_cells_split_CB usegs m1 _ [] 80 jlo [CB 184 (e_j80 E); CB 104 jhi] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    apply (rw_cells_split_CB usegs m1 _ [_;_;_;_;_;_;_;_;_;_;_] 104 jhi [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    step. do 13 step.
    grun.
    if_true.
    grun.
    if_cases K0; zify_cond K0; [lia|].
    pose proof (off_bound E OK 0 ltac:(lia)) as HO0. pose proof (tok_range E OK 0) as HT0.
    pose proof (off_range _ _ (ok_s1 _ OK) 0 ltac:(lia)) as HOR0.
    s2_cur_mem ltac:(fun m =>
      pose proof (u32arr_store_ok usegs m (e_OC E) ocs 0 (wa (e_OC E)) OCA ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK0).
    grun.
    zstep.
    s2_old_mem ltac:(fun m => pose proof (u32arr_write usegs m (e_OC E) ocs 0 (Z_to_bv 64 0) OCA ltac:(lia)) as OCA').
    replace (e_OC E + 4 * 0)%Z with (e_OC E) in OCA' by lia.
    store_done.
    s2_cur_mem ltac:(fun m =>
      pose proof (u32arr_store_ok usegs m (e_OC E) _ 1 (wa (e_OC E + 4)) OCA' ltac:(rewrite upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK1).
    zstep.
    s2_old_mem ltac:(fun m => pose proof (u32arr_write usegs m (e_OC E) _ 1 (Z_to_bv 64 0) OCA' ltac:(rewrite upd_length; lia)) as OCA'').
    replace (e_OC E + 4 * 1)%Z with (e_OC E + 4)%Z in OCA'' by lia.
    store_done.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m 0 IDXA ltac:(lia)) as RD1;
      pose proof (tok_read E OK m 0 BUFRO ltac:(lia)) as RD2).
    replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in RD1 by lia.
    grun.
    fold (tok (e_bs E) (e_idxs E) 0) in *.
    if_cases K1; zify_cond K1.
    2:{
        assert (KX : exit_k E Q).
        { apply KXo. unfold is_numstart, is_digit, c_minus.
          destruct (Z_lt_dec (e_tok E 0) 34) as [L|L].
          - replace (e_tok E 0 =? 45)%Z with false by (symmetry; apply Z.eqb_neq; lia).
            replace (48 <=? e_tok E 0)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
          - rewrite Z.mod_small in K1 by lia.
            replace (e_tok E 0 =? 45)%Z with false by (symmetry; apply Z.eqb_neq; lia).
            replace (e_tok E 0 <=? 57)%Z with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. reflexivity. }
        grun_to 0x4be14%Z. eapply (KX 3%Z); [s2_errlit|]. s2_close_memx. }
    assert (HR : (34 <= e_tok E 0 <= 123)%Z).
    { destruct (Z_lt_dec (e_tok E 0) 34) as [L|L].
      - replace ((e_tok E 0 + -34) mod 18446744073709551616)%Z with (e_tok E 0 + -34 + 18446744073709551616)%Z in K1; [lia|].
        symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia.
      - rewrite Z.mod_small in K1 by lia. lia. }
    pose proof (jt_range (e_tok E 0 - 34) ltac:(lia)) as HJR.
    grun_to 0x4385c%Z.
    s2_cur_mem ltac:(fun m =>
      pose proof (jt_read m (e_tok E 0 - 34) (wa (4 * (e_tok E 0 + -34) + 79724)) MI ltac:(lia) ltac:(unfold wa, T_JT; f_equal; lia)) as RJ).
    grun.
    replace (jt (e_tok E 0 - 34) + 79724)%Z with (root_target (e_tok E 0)) by (rewrite <- jt_target by lia; unfold T_JT; lia).

    assert (HCL : root_target (e_tok E 0) = 0x4be14%Z \/
                  (root_target (e_tok E 0) <> 0x4be14%Z /\ (0 <= root_target (e_tok E 0) < 2 ^ 64)%Z /\ (root_target (e_tok E 0) mod 2 = 0)%Z)).
    { unfold root_target.
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      first [ left; reflexivity | right; split; [discriminate | split; [lia | reflexivity]] ]. }
    destruct HCL as [HX | (HNX & HRG & HEV)].
    - assert (KX : exit_k E Q).
      { apply KXo. unfold root_target in HX. unfold is_numstart, is_digit, c_minus.
        destruct (e_tok E 0 =? 34)%Z; [discriminate HX|].
        destruct ((e_tok E 0 =? 45) || (48 <=? e_tok E 0) && (e_tok E 0 <=? 57))%Z; [discriminate HX| reflexivity]. }
      rewrite HX. rewrite (ret_pc_even 0x4be14%Z) by (first [lia | reflexivity]).
      eapply (KX 3%Z); [s2_errlit|]. s2_close_memx.
    - rewrite (ret_pc_even _ HRG HEV).
      eapply (KR _ eq_refl HNX).
      s2_close_forget; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil | forgets_tac].
  Qed.

  Lemma seg_entry : forall (Q : machine_state -> Prop) docv
      x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM0 docv fc m1 ->
    exit_k E Q ->
    (forall pc, pc = root_target (e_tok E 0) -> pc <> 0x4be14%Z -> rootprim_k E Q pc) ->
    evt usegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x43550) fc None m1 (seg_rom usegs)).
  Proof using OK.
    intros Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM KX KR.
    apply (seg_entry_gen Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM (fun _ => KX) KR).
  Qed.

  Lemma seg_entry_num : forall (Q : machine_state -> Prop) docv
      x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM0 docv fc m1 ->
    is_numstart (e_tok E 0) = true ->
    rootprim_k E Q 0x43874 ->
    evt usegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x43550) fc None m1 (seg_rom usegs)).
  Proof using OK.
    intros Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM HN KR.
    apply (seg_entry_gen Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM); [intros HF; congruence|].
    intros pc HPC _. subst pc. unfold root_target.
    unfold is_numstart, is_digit, c_minus in HN.
    destruct (e_tok E 0 =? 34)%Z eqn:T34.
    { apply Z.eqb_eq in T34. rewrite T34 in HN. discriminate HN. }
    rewrite HN. exact KR.
  Qed.
End Entry.
