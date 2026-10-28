(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage1_defs Sj_stage1_ws Sj_stage1_prim Sj_stage1_str Sj_stage1_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FOR.
  Variable E : s1env.
  Hypothesis OK : env_ok_u E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma u1_bottom : forall (f : nat), u1_for_stmt E f ->
    forall (st' : s1st) (idxc : Z) xra xa3 xa5 xt5 xt6 (m1 : mem),
    U1INV E m1 (s_out st') idxc (s_err st') -> err_ok (s_err st') ->
    (Z.of_nat (length (s_out st')) <= s_idx st' <= len + 4)%Z -> (Z.of_nat (length (s_out st')) <= len)%Z -> (1 <= s_idx st')%Z ->
    (len - s_idx st' <= Z.of_nat f)%Z ->
    evt usegs (u1_postR E (scan_loop bs f st'))
      (U1ST E 0x4195c xra (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st')))) xa3 xa5
            (Z_to_bv 64 (s_idx st' - 1)) (Z_to_bv 64 len) (Z_to_bv 64 (Z.b2z (s_unclosed st'))) xt5 xt6 m1).
  Proof using OK.
    intros f HFOR st' idxc xra xa3 xa5 xt5 xt6 m1 INV EOK HB HN H1 HF.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    u1_open_inv INV.
    zstep. s1norm. zstep. zstep.
    replace (Z_to_bv 64 (s_idx st' - 1 + 1)) with (Z_to_bv 64 (s_idx st')) in * by (f_equal; lia).
    assert (INV2 : U1INV E m (s_out st') (s_idx st') (s_err st')) by u1_close_inv.
    if_cases KGE; zify_cond KGE.
    -
      rewrite scan_loop_done by lia.
      unfold u1_postR. destruct st' as [idx' err' uncl' out']. cbn [s_idx s_err s_unclosed s_out] in *.
      apply (u1_tail E OK idx' err' uncl' out' idx'); [exact INV2| lia| exact EOK].
    - apply HFOR; try assumption; lia.
  Qed.

  Ltac upush_store i :=
    lazymatch goal with
    | IDXA : u32arr usegs ?m (e_IDX E) ?ws, IDXF : firstn (length ?out) ?ws = map wz ?out |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        let n := constr:(Z.of_nat (length out)) in
        pose proof (u32arr_store_ok usegs m (e_IDX E) ws n (wa (e_IDX E + 4 * n)) IDXA ltac:(lia) eq_refl) as SOK;
        step;
        pose proof (u32arr_write usegs m (e_IDX E) ws n (Z_to_bv 64 i) IDXA ltac:(lia)) as IDXA';
        store_done;
        assert (IDXF' : firstn (length (out ++ [i])) (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = map wz (out ++ [i]))
          by (rewrite Nat2Z.id; apply arr_push; [exact IDXF| lia]);
        assert (IDXL' : length (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = e_cap E) by (rewrite upd_length; assumption);
        clear IDXF
    end.

  Lemma u1_token : forall (f : nat), u1_for_stmt E f ->
    forall (st : s1st) (i : Z) xra xa5 xt5 xt6 (m1 : mem),
    U1INV E m1 (s_out st) i (s_err st) -> (0 <= s_idx st <= i)%Z -> (i < len)%Z -> (len - i <= Z.of_nat (S f))%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z -> err_ok (s_err st) ->
    evt usegs (u1_postR E (scan_loop bs f (scan_token bs i st)))
      (U1ST E 0x419ac xra (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st)))) (Z_to_bv 64 len) xa5
            (Z_to_bv 64 i) (Z_to_bv 64 len) (Z_to_bv 64 (Z.b2z (s_unclosed st))) xt5 xt6 m1).
  Proof using OK.
    intros f HFOR [idx err uncl out] i xra xa5 xt5 xt6 m1 INV Hidx Hi HF HN EOK.
    cbn [s_idx s_err s_unclosed s_out] in *.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    unfold scan_token. fold c. cbn [s_idx s_err s_unclosed s_out].
    u1_open_inv INV.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (ubuf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (utbl_read m1 _ c TBL CR) as RD2.
    pose proof (align4_ok (e_IDX E) (Z.of_nat (length out)) ALIGN ltac:(lia)) as AL.
    zstep. zstep. s1norm. zstep. if_cases G1; zify_cond G1; [|exfalso; lia].
    zstep. zstep. s1norm. zstep.
    if_cases K34; zify_cond K34.
    -
      rewrite (proj2 (Z.eqb_neq _ _) K34).
      zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
      zstep. zstep. s1norm. zstep. zstep. zstep. zstep. zstep.
      rewrite AL. replace (0 <? e_IDX E + 4 * Z.of_nat (length out))%Z with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [Z.b2z Z.ltb Z.compare Z.land Pos.land].

      assert (KBOT : forall r idxc' xra' xa3' xa5' xt5' xt6' m', (i <= r < len)%Z -> U1INV E m' (out ++ [i]) idxc' err ->
                evt usegs (u1_postR E (scan_loop bs f (mkS1 (r + 1) err uncl (out ++ [i]))))
                  (U1ST E 0x4195c xra' (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (out ++ [i])))) xa3' xa5'
                        (Z_to_bv 64 r) (Z_to_bv 64 len) (Z_to_bv 64 (Z.b2z uncl)) xt5' xt6' m')).
      { intros r idxc' xra' xa3' xa5' xt5' xt6' m' Hr INV2.
        eapply evt_eq; [| eapply (u1_bottom f HFOR (mkS1 (r + 1) err uncl (out ++ [i])) idxc' _ _ _ _ _ m' INV2)];
          [cbn [s_idx s_out s_err s_unclosed]; s1_st_eq | cbn [s_idx s_out s_err]; try assumption; rewrite ?length_app; cbn [length]; lia ..]. }
      zstep.
      if_cases K2; zify_cond K2.
      +
        assert (TO : t_op c = true) by (unfold t_op; rewrite (proj2 (Z.eqb_neq _ _) K2); reflexivity).
        rewrite TO.
        zstep. if_true.
        upush_store i.
        zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
        zstep. if_cases G4; zify_cond G4; [|exfalso; lia].
        step. unfold wz. rewrite (sx32_small len) by lia. step. unfold wz. rewrite (sx32_small i) by lia.
        zstep. zstep. zstep.
        eapply evt_eq; [| eapply (KBOT i i)]; [rewrite length_app; cbn [length]; s1_st_eq| lia| u1_close_inv].
      +
        assert (TO : t_op c = false) by (unfold t_op; rewrite (proj2 (Z.eqb_eq _ _) K2); reflexivity).
        rewrite TO.
        zstep. if_true.
        upush_store i.
        zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
        zstep. if_cases G4; zify_cond G4; [|exfalso; lia].
        step. unfold wz. rewrite (sx32_small i) by lia. step. unfold wz. rewrite (sx32_small len) by lia.
        zstep. zstep. s1norm. zstep. zstep.
        s1_cur_mem ltac:(fun mm => assert (INV2 : U1INV E mm (out ++ [i]) i err) by u1_close_inv).
        if_cases KL; zify_cond KL.
        *
          rewrite (prim_run_end bs (length bs) i) by lia.
          eapply evt_eq; [| eapply (KBOT i i)]; [rewrite length_app; cbn [length]; s1_st_eq| lia| exact INV2].
        * zstep. zstep. s1norm. zstep. zstep.
          pose proof (prim_run_bounds bs (length bs) i Hi) as PB.
          eapply evt_eq; [| eapply (u1_prim_loop E OK _ (length bs) i (out ++ [i]) i err _ _ _ _ _ INV2)];
            [s1_st_eq| lia| lia| unfold blen in *; lia|].
          intros idxc' xra' xa3' xa5' xt5' xt6' m1' INV3.
          eapply evt_eq; [| eapply (KBOT (prim_run bs (length bs) i) idxc')]; [s1_st_eq| lia| exact INV3].
    -
      rewrite (proj2 (Z.eqb_eq _ _) K34).
      destruct (str_loop bs (length bs) (i + 1) err) as [[i' err'] u] eqn:ESL.
      pose proof (str_loop_bounds bs _ _ _ _ _ _ ESL) as SB.
      pose proof (str_loop_err bs _ _ _ _ _ _ ESL EOK) as EOK'.

      assert (KDC8 : forall i2 err2 (u2 : bool) idxc' xra' xa5' xt5' xt6' m',
                 str_loop bs (length bs) (i + 1) err = (i2, err2, u2) -> U1INV E m' (out ++ [i]) idxc' err2 ->
                 evt usegs (u1_postR E (scan_loop bs f (mkS1 (i' + 1) err' (uncl || u) (out ++ [i]))))
                   (U1ST E 0x41958 xra' (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (out ++ [i])))) (Z_to_bv 64 (Z.b2z u2)) xa5'
                         (Z_to_bv 64 i2) (Z_to_bv 64 len) (Z_to_bv 64 (Z.b2z uncl)) xt5' xt6' m')).
      { intros i2 err2 u2 idxc' xra' xa5' xt5' xt6' m' EQ INV2.
        rewrite ESL in EQ. inversion EQ; subst i2 err2 u2. clear EQ.
        zstep. rewrite lor_b2z.
        eapply evt_eq; [| eapply (u1_bottom f HFOR (mkS1 (i' + 1) err' (uncl || u) (out ++ [i])) idxc' _ _ _ _ _ m' INV2)];
          [cbn [s_idx s_out s_err s_unclosed]; s1_st_eq | cbn [s_idx s_out s_err]; try assumption; rewrite ?length_app; cbn [length]; lia ..]. }
      zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
      zstep. rewrite AL. zstep. if_true.
      upush_store i.
      zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
      zstep. if_cases G4; zify_cond G4; [|exfalso; lia].
      step. unfold wz. rewrite (sx32_small i) by lia. step. unfold wz. rewrite (sx32_small len) by lia.
      zstep. zstep. s1norm. zstep. zstep. zstep.
      s1_cur_mem ltac:(fun mm => assert (INV2 : U1INV E mm (out ++ [i]) (i + 1) err) by u1_close_inv).
      zstep.
      if_cases KL; zify_cond KL.
      + eapply evt_eq; [| eapply (u1_str_loop E OK _ (length bs) (i + 1) err (out ++ [i]) _ _ _ _ _ _ _ INV2)];
          [s1_st_eq| lia| unfold blen in *; lia|].
        intros i2 err2 u2 idxc' xra' xa5' xt5' xt6' m1' EQ INV3.
        eapply evt_eq; [| eapply (KDC8 i2 err2 u2 idxc' _ _ _ _ m1' EQ INV3)]; s1_st_eq.
      +
        zstep. zstep.
        assert (EQ0 : str_loop bs (length bs) (i + 1) err = ((i + 1)%Z, err, true)) by (apply str_loop_done; lia).
        eapply evt_eq; [| eapply (KDC8 (i + 1)%Z err true (i + 1)%Z _ _ _ _ _ EQ0 INV2)]; s1_st_eq.
  Qed.

  Theorem u1_for : forall f, u1_for_stmt E f.
  Proof using OK.
    induction f as [|f IH]; intros [idx err uncl out] xra xa3 xa5 xt5 xt6 m1 INV Hidx HF HN EOK;
      cbn [s_idx s_err s_unclosed s_out] in *; [exfalso; lia|].
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    rewrite scan_loop_S. cbn [s_idx s_err s_unclosed s_out].
    rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hidx)). cbv zeta.
    pose proof (ws_run_bounds bs (length bs) idx (proj2 Hidx)) as WB.
    set (r := ws_run bs (length bs) idx) in *.
    apply (u1_ws_loop E OK _ (length bs) idx out err); try assumption; try (unfold blen in *; lia).
    -
      intros xt5' m1' Hr _ INV1. fold r in Hr, INV1 |- *.
      rewrite (proj2 (Z.leb_gt _ _) Hr).
      apply (u1_token f IH (mkS1 idx err uncl out) r); cbn [s_idx s_err s_unclosed s_out]; try assumption; lia.
    -
      intros xa3' xt5' m1' Hr INV1. fold r in Hr, INV1 |- *.
      rewrite (proj2 (Z.leb_le _ _) Hr).
      unfold u1_postR. cbn [s_out].
      apply (u1_tail E OK r err uncl out r); [exact INV1| lia| exact EOK].
  Qed.
End FOR.
