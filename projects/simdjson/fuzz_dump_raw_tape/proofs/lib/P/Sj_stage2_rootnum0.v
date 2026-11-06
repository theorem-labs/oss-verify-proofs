(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_tables Sj_tables2 Sj_stage2_auto2 Sj_stage2_entry.
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

Section EntryNum.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Lemma seg_entry_num : forall (Q : machine_state -> Prop) docv
      x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM0 E docv fc m1 ->
    is_numstart (e_tok E 0) = true ->
    rootprim_k E Q 0x3e104 ->
    evt psegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x3e01c) fc None m1 (seg_rom psegs)).
  Proof using OK.
    intros Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM HNUM KRN.
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
    assert (HNR : (e_tok E 0 = 45 \/ 48 <= e_tok E 0 <= 57)%Z).
    { unfold is_numstart, is_digit, c_minus in HNUM. apply orb_true_iff in HNUM. destruct HNUM as [H|H].
      - left. apply Z.eqb_eq in H. exact H.
      - right. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    if_cases K1; zify_cond K1.
    2:{ exfalso. clear - K1 HNR. lia. }
    assert (HR : (34 <= e_tok E 0 <= 123)%Z) by lia.
    zstep. zstep. s2norm. zstep. zstep. zstep.
    pose proof (jt_range (e_tok E 0 - 34) ltac:(lia)) as HJR.
    s2_cur_mem ltac:(fun m =>
      pose proof (jt_read m (e_tok E 0 - 34) (wa (4 * (e_tok E 0 + -34) + 79512)) MI ltac:(lia) ltac:(unfold wa, T_JT; f_equal; lia)) as RJ).
    zstep. s2norm. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (jt (e_tok E 0 - 34) + 79512)%Z with (root_target (e_tok E 0)) by (rewrite <- jt_target by lia; unfold T_JT; lia).
    assert (RT : root_target (e_tok E 0) = 254212%Z).
    { unfold root_target. destruct (e_tok E 0 =? 34)%Z eqn:T34; [apply Z.eqb_eq in T34; lia|].
      unfold is_numstart, is_digit, c_minus in HNUM. rewrite HNUM. reflexivity. }
    rewrite RT. zstep. eapply KRN.
    s2_close_mem; [rewrite !upd_length; exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil].
  Qed.
End EntryNum.
