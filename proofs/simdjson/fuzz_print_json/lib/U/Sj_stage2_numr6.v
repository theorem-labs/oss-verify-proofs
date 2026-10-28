(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard Sj_num_iface
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numkit3 Sj_stage2_numkit6 Sj_stage2_numr_defs Sj_stage2_numr_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_call_extra segs W m m' MU WM ::= s2_timg_call segs W m m' MU WM.
Local Ltac lia ::= r_lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_cp | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.
Local Ltac ngstep ::= ngstep_l.

Lemma crs_stop : forall t, nth_error (zbytes (crs t)) (Z.to_nat (blen t)) = Some (Z_to_bv 8 32).
Proof.
  intros t. unfold blen. rewrite Nat2Z.id.
  rewrite nth_error_zbytes by (unfold crs; rewrite length_app, repeat_length; lia).
  unfold crs. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Section NumR6.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Hypothesis RLMAX : (blen t <= 1048512)%Z.
  Notation rl := (blen t).
  Hypothesis HSLOWF : slowfu_stmt_g usegs 0x5f104 0x110000.
  Hypothesis HPFF : pffu_stmt_g usegs 0x5f1b4 0x110000.

  Hypothesis HROOM : (e_lo E + 368 + NUMU_STACK <= bv_unsigned (e_sp E))%Z.

  Lemma rootnum_call : forall (Q : machine_state -> Prop) (entry r1 r0 RA : Z) (nxt : word) (sc : list (bool * Z))
      c0 c1 c2 c3 c4 c5 c6 c7 c8 j72 xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    numwu_stmt_g usegs entry 0x110000 r1 r0 ->
    (0 <= RA < 2 ^ 64)%Z -> (RA mod 2 = 0)%Z ->
    csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat -> csize c4 = 8%nat ->
    csize c5 = 8%nat -> csize c6 = 8%nat -> csize c7 = 8%nat -> csize c8 = 8%nat ->
    MEMI E nxt [c0; c1; c2; c3; c4; c5; c6; c7; c8; CB 8 j72] sc fc m1 ->
    bytes_at usegs m1 CP (zbytes (crs t)) ->
    (forall (flag : bool) (v : word) yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
       MEMI E nxt [c0; c1; c2; c3; c4; c5; c6; c7; c8; C8 v] sc fc' m' ->
       bytes_at usegs m' CP (zbytes (crs t)) ->
       evt usegs Q (S2R E RA (Z_to_bv 64 (RA)) yt0 yt1 yt2 xs0 xs1 (Z_to_bv 64 ((if flag then r1 else r0))) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc' m')) ->
    evt usegs Q (S2R E entry (Z_to_bv 64 (RA)) xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 CP) (Z_to_bv 64 (bv_unsigned (e_sp E) + -296)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK TOK CP0 CPHI CPSEP RLMAX HROOM.
    intros Q entry r1 r0 RA nxt sc c0 c1 c2 c3 c4 c5 c6 c7 c8 j72 xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 HS HRA HRA2
      E0 E1 E2 E3 E4 E5 E6 E7 E8 HM CPRO K.
    pose proof (crs_blen t) as CBL0. pose proof (blen_nonneg t) as RL0.
    s2_env OK. unfold NUMU_STACK in HROOM.
    s2_open_mem HM.
    lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: CB 8 j72 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8] ++ [CB 8 j72] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FRlo FR]. apply rw_cells_app in FR. destruct FR as [FROUT FRhi].
    cbn [cells_size Nat.add] in FROUT, FRhi. rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8 in FROUT, FRhi. cbn [csize Nat.add] in FROUT, FRhi.
    replace (e_SP E + Z.of_nat 72)%Z with (bv_unsigned (e_sp E) + -296)%Z in * by lia.
    replace (bv_unsigned (e_sp E) + -296 + Z.of_nat 8)%Z with (bv_unsigned (e_sp E) + -288)%Z in * by lia.
    unfold numwu_stmt_g in HS.
    eapply evt_cut.
    { replace (Z_to_bv 64 CP) with (Z_to_bv 64 (CP + 0)) at 1 by (f_equal; lia).
      eapply HS with (A := CP) (off := 0%Z) (stop := blen t) (OUT := (bv_unsigned (e_sp E) + -296)%Z) (lo := e_lo E)
                     (txt := zbytes (crs t)) (b := Z_to_bv 8 32) (junk := j72);
        rewrite ?(u64_small (e_SP E)) by lia;
        [ exact MI | exact FRM | exact ST | unfold NUMU_STACK; lia | lia | s2_unhide; lia | exact CPRO | lia | lia | lia | lia
        | apply crs_stop
        | reflexivity
        | exact FROUT | lia | s2_unhide; lia ]. }
    cbv beta. intros ms' P. unfold numwu_post_g in P.
    destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F' & fc' & m' & v & flag & -> & FRM' & MUc & WMc & MIc & OUTc & STc).
    rewrite ?(u64_small (e_SP E)) in MUc, STc by lia. unfold NUMU_STACK in MUc.
    clear FROUT.
    transport_after_call usegs m1 m' MUc WMc.
    clear MUc WMc HS MI FRM.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia | exact HRA2]).
    eapply (K flag v); [| eassumption].
    unfold MEMI. split; [exact FRM'|]. split.
    { change ([c0; c1; c2; c3; c4; c5; c6; c7; c8; C8 v] ++ frame_hi E) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8] ++ [C8 v] ++ frame_hi E).
      apply rw_cells_app; split; [exact FRlo | apply rw_cells_app; split].
      - cbn [cells_size Nat.add]. rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8. cbn [Nat.add].
        replace (e_SP E + Z.of_nat 72)%Z with (bv_unsigned (e_sp E) + -296)%Z by lia. exact OUTc.
      - cbn [cells_size Nat.add]. rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8. cbn [csize Nat.add].
        replace (e_SP E + Z.of_nat 72 + Z.of_nat 8)%Z with (bv_unsigned (e_sp E) + -288)%Z by lia. unfold frame_hi. exact FRhi. }
    unfold impl_cells, doc_cells, s2_W.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eexists; split; [eassumption | split; eassumption]|].
    split; [eexists; split; [eassumption | split; eassumption]|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x474bc%Z => if_false | 0x46df8%Z => first [if_true | if_false] | 0x46e08%Z => first [if_true | if_false] end.

  Lemma seg_numr_slow : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> rdel_errA_k E CP Q -> rdel_errB_k E CP Q -> (forall v r, num_word v -> rdel_fin0_k (gapp E [v; r] []) CP Q) -> rdel_fin9_k E CP Q ->
    numr_tail_k E CP t Q 0x4731c.
  Proof using OK TOK CP0 CPHI CPSEP RLMAX HSLOWF HROOM.
    intros Q GLT KXA KXB KF0 KF9. unfold numr_tail_k. intros until m1. intros HM CPRO.
    pose proof (blen_nonneg (e_bs E)) as LEN0.
    s2_env OK. unfold RSL in HM. unfold NUMU_STACK in HROOM.
    s2_open_mem HM.
    ngrun_to 0x5f104%Z.
    eapply (rootnum_call Q 0x5f104 9 0 0x47328); cycle 12; [n_close | exact CPRO | | exact HSLOWF | lia | reflexivity | reflexivity ..].
    intros flag v yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' fc' m' HM' CPRO'.
    clear - OK KXA KXB KF0 KF9 HM' CPRO' CPHI CPSEP LEN0 GLT. pose proof (crs_blen t) as CBL0. s2_env OK. s2_open_mem HM'.
    destruct flag; ngexp r_cuts ltac:(idtac; r_leaf KXA KXB KF0 KF9).
  Qed.

  Lemma seg_numr_fb : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> rdel_errA_k E CP Q -> rdel_errB_k E CP Q -> (forall v r, num_word v -> rdel_fin0_k (gapp E [v; r] []) CP Q) -> rdel_fin9_k E CP Q ->
    numr_tail_k E CP t Q 0x46d6c ->
    numr_tail_k E CP t Q 0x475b0.
  Proof using OK TOK CP0 CPHI CPSEP RLMAX HPFF HROOM.
    intros Q GLT KXA KXB KF0 KF9 KW. unfold numr_tail_k. intros until m1. intros HM CPRO.
    s2_env OK. unfold RSL in HM. unfold NUMU_STACK in HROOM.
    s2_open_mem HM.
    ngrun_to 0x5f1b4%Z.
    eapply (rootnum_call Q 0x5f1b4 0 1 0x475bc); cycle 12; [n_close | exact CPRO | | exact HPFF | lia | reflexivity | reflexivity ..].
    intros flag v yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' fc' m' HM' CPRO'.
    clear - OK KXA KXB KF0 KF9 KW HM' CPRO' CPHI CPSEP GLT. pose proof (crs_blen t) as CBL0. s2_env OK. s2_open_mem HM'.
    destruct flag.
    -
      ngrun. if_true. ngexp r_cuts ltac:(idtac; r_leaf KXA KXB KF0 KF9).
    - ngrun. if_false. ngrun_to 0x46d6c%Z.
      eapply KW; [eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption].
  Qed.
End NumR6.
