(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_stage1_defs Sj_stage1_ws Sj_stage1_prim Sj_stage1_str Sj_stage1_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma zx32_small_b : forall x, (0 <= x < 2^32)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. f_equal. rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia). apply Z.mod_small. lia. Qed.

Definition b1_for_stmt (E : s1env) (f : nat) : Prop :=
  forall (st : s1st) xa2 xs5 xs6 xt5 xt6 (m1 : mem),
    B1INV E m1 (s_out st) (s_idx st) (s_err st) -> (0 <= s_idx st < e_len E)%Z -> (e_len E - s_idx st <= Z.of_nat f)%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z -> err_ok (s_err st) ->
    evt bsegs (b1_postR E (scan_loop (e_bs E) f st))
      (B1ST E 0xb34d4 (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st)))) xa2 (Z_to_bv 64 (Z.b2z (s_unclosed st)))
            (Z_to_bv 64 (e_len E)) xs5 xs6 xt5 xt6 m1).

Section FOR.
  Variable E : s1env.
  Hypothesis OK : env_ok_b E.
  Hypothesis SHZ : b1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma b1_bottom : forall (f : nat), b1_for_stmt E f ->
    forall (st' : s1st) (idxc : Z) xa2 xs3 xs5 xs6 xt5 xt6 (m1 : mem),
    B1INV E m1 (s_out st') idxc (s_err st') -> idxc = (s_idx st' - 1)%Z -> err_ok (s_err st') ->
    (Z.of_nat (length (s_out st')) <= s_idx st' <= len + 4)%Z -> (Z.of_nat (length (s_out st')) <= len)%Z -> (1 <= s_idx st')%Z ->
    (len - s_idx st' <= Z.of_nat f)%Z ->
    evt bsegs (b1_postR E (scan_loop bs f st'))
      (B1ST E 0xb34c0 (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st')))) xa2 (Z_to_bv 64 (Z.b2z (s_unclosed st')))
            xs3 xs5 xs6 xt5 xt6 m1).
  Proof using OK SHZ.
    intros f HFOR st' idxc xa2 xs3 xs5 xs6 xt5 xt6 m1 INV -> EOK HB HN H1 HF.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, B1_STACK, B1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    b1_open_inv INV.
    step. unfold wz. rewrite (sx32_small (s_idx st' - 1)) by lia.
    step. unfold wz. rewrite (sx32_small len) by lia.
    zstep. s1norm. zstep.
    replace (Z_to_bv 64 (s_idx st' - 1 + 1)) with (Z_to_bv 64 (s_idx st')) in * by (f_equal; lia).
    s1_cur_mem ltac:(fun mm => assert (INV2 : B1INV E mm (s_out st') (s_idx st') (s_err st')) by b1_close_inv).
    zstep.
    if_cases KGE; zify_cond KGE.
    -
      rewrite scan_loop_done by lia.
      unfold b1_postR. destruct st' as [idx' err' uncl' out']. cbn [s_idx s_err s_unclosed s_out] in *.
      apply (b1_tail E OK SHZ idx' err' uncl' out' idx'); [exact INV2| lia| exact EOK].
    - apply HFOR; try assumption; lia.
  Qed.

  Ltac bpush_store i :=
    lazymatch goal with
    | IDXA : u32arr bsegs ?m (e_IDX E) ?ws, IDXF : firstn (length ?out) ?ws = map wz ?out |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        let n := constr:(Z.of_nat (length out)) in
        pose proof (u32arr_store_ok bsegs m (e_IDX E) ws n (wa (e_IDX E + 4 * n)) IDXA ltac:(lia) eq_refl) as SOK;
        step;
        pose proof (u32arr_write bsegs m (e_IDX E) ws n (Z_to_bv 64 i) IDXA ltac:(lia)) as IDXA';
        store_done;
        assert (IDXF' : firstn (length (out ++ [i])) (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = map wz (out ++ [i]))
          by (rewrite Nat2Z.id; apply arr_push; [exact IDXF| lia]);
        assert (IDXL' : length (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = e_cap E) by (rewrite upd_length; assumption);
        clear IDXF
    end.

  Ltac chk_idx x := b1_shz_idx SHZ x; zstep; rewrite shr3_div; zstep; zstep; rewrite sxb_z8; zstep; if_false.

  Lemma b1_token : forall (f : nat), b1_for_stmt E f ->
    forall (st : s1st) (i : Z) xs5 xs6 (m1 : mem),
    B1INV E m1 (s_out st) i (s_err st) -> (0 <= s_idx st <= i)%Z -> (i < len)%Z -> (len - i <= Z.of_nat (S f))%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z -> err_ok (s_err st) ->
    evt bsegs (b1_postR E (scan_loop bs f (scan_token bs i st)))
      (B1ST E 0xb3544 (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st)))) (Z_to_bv 64 len) (Z_to_bv 64 (Z.b2z (s_unclosed st)))
            (Z_to_bv 64 len) xs5 xs6 (Z_to_bv 64 i) (Z_to_bv 64 i) m1).
  Proof using OK SHZ.
    intros f HFOR [idx err uncl out] i xs5 xs6 m1 INV Hidx Hi HF HN EOK.
    cbn [s_idx s_err s_unclosed s_out] in *.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, B1_STACK, B1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    unfold scan_token. fold c. cbn [s_idx s_err s_unclosed s_out].
    b1_open_inv INV.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (buf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (tbl_read m1 _ c TBL CR) as RD2.
    pose proof (align4_ok (e_IDX E) (Z.of_nat (length out)) ALIGN ltac:(lia)) as AL.
    zstep. if_cases G1; zify_cond G1; [|exfalso; lia].
    zstep.
    b1_shz_buf SHZ (e_BUF E + i)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_false.
    zstep. s1norm. zstep.
    if_cases K34; zify_cond K34.
    -
      rewrite (proj2 (Z.eqb_neq _ _) K34).
      zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
      zstep. zstep. s1norm. zstep. zstep. zstep. zstep. zstep.
      rewrite AL. replace (0 <? e_IDX E + 4 * Z.of_nat (length out))%Z with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [Z.b2z Z.ltb Z.compare Z.land Pos.land].

      assert (KBOT : forall r xa2' xs3' xs5' xs6' xt5' xt6' m', (i <= r < len)%Z -> B1INV E m' (out ++ [i]) r err ->
                evt bsegs (b1_postR E (scan_loop bs f (mkS1 (r + 1) err uncl (out ++ [i]))))
                  (B1ST E 0xb34c0 (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (out ++ [i])))) xa2' (Z_to_bv 64 (Z.b2z uncl))
                        xs3' xs5' xs6' xt5' xt6' m')).
      { intros r xa2' xs3' xs5' xs6' xt5' xt6' m' Hr INV2.
        eapply (b1_bottom f HFOR (mkS1 (r + 1) err uncl (out ++ [i])) r _ _ _ _ _ _ m' INV2);
          cbn [s_idx s_out s_err]; try assumption; rewrite ?length_app; cbn [length]; lia. }
      zstep.
      if_cases K2; zify_cond K2.
      +
        assert (TO : t_op c = true) by (unfold t_op; rewrite (proj2 (Z.eqb_neq _ _) K2); reflexivity).
        rewrite TO.
        zstep. if_true.
        chk_idx (e_IDX E + 4 * Z.of_nat (length out))%Z.
        bpush_store i.
        zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
        zstep. if_cases G4; zify_cond G4; [|exfalso; lia].
        zstep. zstep.
        replace (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out) + 4)) with (wz (e_IDX E + 4 * Z.of_nat (length (out ++ [i])))) in *
          by (unfold wz; f_equal; rewrite length_app; cbn [length]; lia).
        zstep.
        eapply evt_eq; [| eapply (KBOT i)]; [unfold wz; s1_st_eq| lia| b1_close_inv].
      +
        assert (TO : t_op c = false) by (unfold t_op; rewrite (proj2 (Z.eqb_eq _ _) K2); reflexivity).
        rewrite TO.
        zstep. if_true.
        chk_idx (e_IDX E + 4 * Z.of_nat (length out))%Z.
        bpush_store i.
        zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
        zstep. if_cases G4; zify_cond G4; [|exfalso; lia].
        step. unfold wz. rewrite (sx32_small i) by lia. step. unfold wz. rewrite (sx32_small len) by lia.
        zstep. zstep. s1norm. zstep.
        replace (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out) + 4)) with (wz (e_IDX E + 4 * Z.of_nat (length (out ++ [i])))) in *
          by (unfold wz; f_equal; rewrite length_app; cbn [length]; lia).
        s1_cur_mem ltac:(fun mm => assert (INV2 : B1INV E mm (out ++ [i]) i err) by b1_close_inv).
        zstep.
        if_cases KL; zify_cond KL.
        *
          rewrite (prim_run_end bs (length bs) i) by lia.
          eapply evt_eq; [| eapply (KBOT i)]; [unfold wz; s1_st_eq| lia| exact INV2].
        * zstep. zstep. s1norm. zstep. zstep.
          pose proof (prim_run_bounds bs (length bs) i Hi) as PB.
          eapply evt_eq; [| eapply (b1_prim_loop E OK SHZ _ (length bs) i (out ++ [i]) err _ _ _ _ _ INV2)];
            [unfold wz; s1_st_eq| lia| lia| unfold blen in *; lia|].
          intros xa2' xs3' xs5' xs6' xt5' xt6' m1' INV3.
          eapply evt_eq; [| eapply (KBOT (prim_run bs (length bs) i))]; [unfold wz; s1_st_eq| lia| exact INV3].
    -
      rewrite (proj2 (Z.eqb_eq _ _) K34).
      destruct (str_loop bs (length bs) (i + 1) err) as [[i' err'] u] eqn:ESL.
      pose proof (str_loop_bounds bs _ _ _ _ _ _ ESL) as SB.
      pose proof (str_loop_err bs _ _ _ _ _ _ ESL EOK) as EOK'.

      assert (K43C : forall i2 err2 (u2 : bool) xa2' xs5' xs6' xt5' xt6' m',
                 str_loop bs (length bs) (i + 1) err = (i2, err2, u2) -> B1INV E m' (out ++ [i]) i2 err2 ->
                 evt bsegs (b1_postR E (scan_loop bs f (mkS1 (i' + 1) err' (uncl || u) (out ++ [i]))))
                   (B1ST E 0xb34bc (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (out ++ [i])))) xa2' (Z_to_bv 64 (Z.b2z uncl))
                         (Z_to_bv 64 (Z.b2z u2)) xs5' xs6' xt5' xt6' m')).
      { intros i2 err2 u2 xa2' xs5' xs6' xt5' xt6' m' EQ INV2.
        rewrite ESL in EQ. inversion EQ; subst i2 err2 u2. clear EQ.
        zstep. rewrite lor_b2z.
        eapply (b1_bottom f HFOR (mkS1 (i' + 1) err' (uncl || u) (out ++ [i])) i' _ _ _ _ _ _ m' INV2);
          cbn [s_idx s_out s_err]; try assumption; rewrite ?length_app; cbn [length]; lia. }
      zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
      zstep. rewrite AL. zstep. if_true.
      chk_idx (e_IDX E + 4 * Z.of_nat (length out))%Z.
      bpush_store i.
      zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
      zstep. if_cases G4; zify_cond G4; [|exfalso; lia].
      step. unfold wz. rewrite (sx32_small i) by lia. step. unfold wz. rewrite (sx32_small len) by lia.
      zstep. zstep. s1norm. zstep. zstep.
      replace (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out) + 4)) with (wz (e_IDX E + 4 * Z.of_nat (length (out ++ [i])))) in *
        by (unfold wz; f_equal; rewrite length_app; cbn [length]; lia).
      s1_cur_mem ltac:(fun mm => assert (INV2 : B1INV E mm (out ++ [i]) (i + 1) err) by b1_close_inv).
      zstep. zstep.
      if_cases KL; zify_cond KL.
      + eapply evt_eq; [| eapply (b1_str_loop E OK SHZ _ (length bs) (i + 1) err (out ++ [i]) _ _ _ _ _ _ INV2)];
          [unfold wz; s1_st_eq| lia| unfold blen in *; lia|].
        intros i2 err2 u2 xa2' xs5' xs6' xt5' xt6' m1' EQ INV3.
        eapply evt_eq; [| eapply (K43C i2 err2 u2 _ _ _ _ _ m1' EQ INV3)]; unfold wz; s1_st_eq.
      +
        zstep.
        assert (EQ0 : str_loop bs (length bs) (i + 1) err = ((i + 1)%Z, err, true)) by (apply str_loop_done; lia).
        eapply evt_eq; [| eapply (K43C (i + 1)%Z err true _ _ _ _ _ _ EQ0 INV2)]; unfold wz; s1_st_eq.
  Qed.

  Theorem b1_for : forall f, b1_for_stmt E f.
  Proof using OK SHZ.
    induction f as [|f IH]; intros [idx err uncl out] xa2 xs5 xs6 xt5 xt6 m1 INV Hidx HF HN EOK;
      cbn [s_idx s_err s_unclosed s_out] in *; [exfalso; lia|].
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, B1_STACK, B1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite scan_loop_S. cbn [s_idx s_err s_unclosed s_out].
    rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hidx)). cbv zeta.
    pose proof (ws_run_bounds bs (length bs) idx (proj2 Hidx)) as WB.
    set (r := ws_run bs (length bs) idx) in *.
    pose proof INV as INV'. b1_open_inv INV'.
    step. unfold wz. rewrite (sx32_small idx) by lia.
    apply (b1_ws_loop E OK SHZ _ (length bs) idx out err); try assumption; try (unfold blen in *; lia).
    intros xt5' xt6' m1' INV1. fold r in INV1 |- *.
    clear FRlo FRtb FRhi PARSER IDXA IDXL IDXF BUFRO MI MU WM ST PBL.
    pose proof INV1 as INV1'. b1_open_inv INV1'.
    step. unfold wz. rewrite (zx32_small_b r) by lia. zstep. s1norm. zstep.
    if_cases KR; zify_cond KR.
    -
      rewrite (proj2 (Z.leb_le _ _) KR).
      unfold b1_postR. cbn [s_out].
      apply (b1_tail E OK SHZ r err uncl out r); [exact INV1| lia| exact EOK].
    -
      assert (Hr : (r < len)%Z) by lia.
      rewrite (proj2 (Z.leb_gt _ _) Hr).
      eapply evt_eq; [| eapply (b1_token f IH (mkS1 idx err uncl out) r _ _ m1' INV1)]; cbn [s_idx s_err s_unclosed s_out];
        [s1_st_eq| lia ..| exact EOK].
  Qed.
End FOR.
