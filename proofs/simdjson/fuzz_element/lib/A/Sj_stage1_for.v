(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage1_defs Sj_stage1_ws Sj_stage1_prim Sj_stage1_str Sj_stage1_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FOR.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma a1_bottom : forall (f : nat), a1_for_stmt E f ->
    forall (st' : s1st) (out : list Z) (i : Z) xt1 xt2 xa0 xa1 xs10 xs11 xt3 (m1 : mem),
    s_out st' = out ++ [i] -> A1INV E m1 (out ++ [i]) ->
    (Z.of_nat (length out) + 1 <= s_idx st' <= len + 4)%Z -> (Z.of_nat (length out) + 1 <= len)%Z ->
    (len - s_idx st' <= Z.of_nat f)%Z -> err_ok (s_err st') ->
    evt asegs (a1_postR E (scan_loop bs f st'))
      (A1ST E 0xba8a4 (Z_to_bv 64 (s_err st')) xt1 xt2 xa0 xa1 (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out)))
            (Z_to_bv 64 (Z.b2z (s_unclosed st'))) (Z_to_bv 64 (s_idx st' - 1)) xs10 xs11 xt3 (Z_to_bv 64 (e_BUF E)) m1).
  Proof using OK SHZ.
    intros f HFOR st' out i xt1 xt2 xa0 xa1 xs10 xs11 xt3 m1 EO INV HB HN HF EOK.
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO : length (s_out st') = S (length out)) by (rewrite EO, length_app; cbn; lia).
    zstep. zstep. s1norm. zstep. s1norm. zstep. zstep.
    replace (Z_to_bv 64 (s_idx st' - 1 + 1)) with (Z_to_bv 64 (s_idx st')) by (f_equal; lia).
    replace (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out) + 4)) with (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st'))))
      by (f_equal; lia).
    if_cases KLT; zify_cond KLT.
    -
      apply HFOR; try lia; [rewrite EO; exact INV| exact EOK].
    -
      zstep. rewrite scan_loop_done by lia.
      unfold a1_postR. destruct st' as [idx' err' uncl' out']. cbn [s_idx s_err s_unclosed s_out] in *. subst out'.
      apply (a1_tail E OK SHZ); [exact INV| lia| exact EOK].
  Qed.

  Ltac apush_store i :=
    lazymatch goal with
    | IDXA : u32arr asegs ?m (e_IDX E) ?ws, IDXF : firstn (length ?out) ?ws = map wz ?out |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        let n := constr:(Z.of_nat (length out)) in
        pose proof (u32arr_store_ok asegs m (e_IDX E) ws n (wa (e_IDX E + 4 * n)) IDXA ltac:(lia) eq_refl) as SOK;
        step;
        pose proof (u32arr_write asegs m (e_IDX E) ws n (Z_to_bv 64 i) IDXA ltac:(lia)) as IDXA';
        store_done;
        assert (IDXF' : firstn (length (out ++ [i])) (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = map wz (out ++ [i]))
          by (rewrite Nat2Z.id; apply arr_push; [exact IDXF| lia]);
        assert (IDXL' : length (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = e_cap E) by (rewrite upd_length; assumption);
        clear IDXF
    end.

  Lemma a1_token : forall (f : nat), a1_for_stmt E f ->
    forall (st : s1st) (i : Z) xa0 xt3 (m1 : mem),
    A1INV E m1 (s_out st) -> (0 <= s_idx st <= i)%Z -> (i < len)%Z -> (len - i <= Z.of_nat (S f))%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z -> err_ok (s_err st) ->
    evt asegs (a1_postR E (scan_loop bs f (scan_token bs i st)))
      (A1ST E 0xba498 (Z_to_bv 64 (s_err st)) (Z_to_bv 64 (i + 2)) (Z_to_bv 64 len) xa0 (Z_to_bv 64 (e_BUF E + i))
            (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st)))) (Z_to_bv 64 (Z.b2z (s_unclosed st))) (Z_to_bv 64 i)
            (Z_to_bv 64 ((e_BUF E + i) / 8 + 2147450880)) (Z_to_bv 64 0) xt3 (Z_to_bv 64 (e_BUF E)) m1).
  Proof using OK SHZ.
    intros f HFOR [idx err uncl out] i xa0 xt3 m1 INV Hidx Hi HF HN EOK.
    cbn [s_idx s_err s_unclosed s_out] in *.
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    unfold scan_token. fold c. cbn [s_idx s_err s_unclosed s_out].
    a1_open_inv INV.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (buf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (tbl_read m1 _ c TBL CR) as RD2.
    a1_shz_buf SHZ (e_BUF E + i)%Z.
    zstep.
    if_cases KGE; zify_cond KGE; [|exfalso; lia].
    zstep. rewrite sxb_z8. zstep. if_false.
    zstep. s1norm. zstep.
    if_cases K34; zify_cond K34.
    -
      rewrite (proj2 (Z.eqb_neq _ _) K34).
      a1_shz_idx SHZ (e_IDX E + 4 * Z.of_nat (length out))%Z.
      zstep. zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. s1norm. zstep. if_false.
      zstep.
      apush_store i.
      assert (INV' : A1INV E m (out ++ [i])) by a1_close_inv.
      zstep.
      if_cases K2; zify_cond K2.
      +
        assert (TO : t_op c = true) by (unfold t_op; rewrite (proj2 (Z.eqb_neq _ _) K2); reflexivity).
        rewrite TO.
        replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + 1 - 1)) by (f_equal; lia).
        apply (a1_bottom f HFOR (mkS1 (i + 1) err uncl (out ++ [i])) out i); cbn [s_idx s_out s_err]; try reflexivity; try assumption; lia.
      +
        assert (TO : t_op c = false) by (unfold t_op; rewrite (proj2 (Z.eqb_eq _ _) K2); reflexivity).
        rewrite TO.
        assert (LB : (0 < length bs)%nat) by (unfold blen in *; lia).
        rewrite (prim_run_unfold bs (length bs) i LB).

        assert (KBOT : forall r xt1' xt2' xa0' xa1' xs10' xs11' xt3', (i <= r < len)%Z ->
                  evt asegs (a1_postR E (scan_loop bs f (mkS1 (r + 1) err uncl (out ++ [i]))))
                    (A1ST E 0xba8a4 (Z_to_bv 64 err) xt1' xt2' xa0' xa1' (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out)))
                          (Z_to_bv 64 (Z.b2z uncl)) (Z_to_bv 64 r) xs10' xs11' xt3' (Z_to_bv 64 (e_BUF E)) m)).
        { intros r xt1' xt2' xa0' xa1' xs10' xs11' xt3' Hr.
          replace (Z_to_bv 64 r) with (Z_to_bv 64 (r + 1 - 1)) by (f_equal; lia).
          apply (a1_bottom f HFOR (mkS1 (r + 1) err uncl (out ++ [i])) out i); cbn [s_idx s_out s_err]; try reflexivity; try assumption; lia. }
        step. unfold wz. rewrite (sx32_small len) by lia.
        zstep. s1norm. zstep.
        if_cases KL; zify_cond KL.
        *
          rewrite (proj2 (Z.ltb_ge _ _) KL). cbn [andb]. apply KBOT. lia.
        * rewrite (proj2 (Z.ltb_lt _ _) KL). cbn [andb].
          pose proof (B_range bs (i + 1) BOK) as CR1. set (c1 := B bs (i + 1)) in *.
          pose proof (tbl_range c1) as TR1.
          pose proof (buf_read m (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD3. fold c1 in RD3.
          pose proof (tbl_read m _ c1 TBL CR1) as RD4.
          pose proof (proj2 (proj2 (SHZ m MU WM))) as SHZB.
          pose proof (SHZB (e_BUF E + (i + 1))%Z ltac:(lia)) as RD5.
          zstep. zstep. s1norm. zstep. zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_false.
          zstep. s1norm. zstep.
          if_cases K30; zify_cond K30.
          -- rewrite (proj2 (Z.eqb_eq _ _) K30). rewrite andb_false_r. apply KBOT. lia.
          -- rewrite (proj2 (Z.eqb_neq _ _) K30). rewrite andb_true_r.
             zstep. zstep. s1norm. zstep. zstep.
             if_cases K3; zify_cond K3.
             ++ assert (TS : t_space_or_op c1 = true) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_neq _ _) K3); reflexivity).
                rewrite TS. cbn [negb]. apply KBOT. lia.
             ++ assert (TS : t_space_or_op c1 = false) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_eq _ _) K3); reflexivity).
                rewrite TS. cbn [negb].
                zstep. zstep. zstep. s1norm. zstep. zstep. s1norm. zstep.
                pose proof (prim_run_bounds bs (pred (length bs)) (i + 1) ltac:(lia)) as PB.
                eapply evt_eq; [| eapply (a1_prim_loop E OK _ (pred (length bs)) (i + 1) _ _ _ _ _ _ m BUFRO TBL SHZB); try (unfold blen in *; lia)].
                ** s1_st_eq.
                ** intros xt1' xa0' xa1' xt3'. apply KBOT. lia.
                **
                   intros xt1' xa0' xa1' xt3' ER. rewrite ER.
                   zstep. zstep. s1norm. zstep. s1norm. zstep. zstep.
                   if_cases KLT; zify_cond KLT; [exfalso; lia|].
                   zstep. rewrite scan_loop_done by (cbn [s_idx]; lia).
                   unfold a1_postR. cbn [s_out].
                   replace (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out) + 4)) with (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (out ++ [i]))))
                     by (f_equal; rewrite length_app; cbn [length]; lia).
                   apply (a1_tail E OK SHZ); [exact INV'| rewrite length_app; cbn [length]; lia| exact EOK].
    -
      rewrite (proj2 (Z.eqb_eq _ _) K34).
      a1_shz_idx SHZ (e_IDX E + 4 * Z.of_nat (length out))%Z.
      zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_false.
      apush_store i.
      assert (INV' : A1INV E m (out ++ [i])) by a1_close_inv.
      destruct (str_loop bs (length bs) (i + 1) err) as [[i' err'] u] eqn:ESL.
      pose proof (str_loop_bounds bs _ _ _ _ _ _ ESL) as SB.
      pose proof (str_loop_err bs _ _ _ _ _ _ ESL EOK) as EOK'.

      assert (K84C : forall i2 err2 (u2 : bool) xra' xt2' xa0' xa1' xs11' xt3' m',
                 str_loop bs (length bs) (i + 1) err = (i2, err2, u2) -> A1INV E m' (out ++ [i]) ->
                 evt asegs (a1_postR E (scan_loop bs f (mkS1 (i' + 1) err' (uncl || u) (out ++ [i]))))
                   (A1ST E 0xba89c xra' (Z_to_bv 64 err2) xt2' xa0' xa1' (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out)))
                         (Z_to_bv 64 (Z.b2z uncl)) (Z_to_bv 64 i2) (Z_to_bv 64 (Z.b2z u2)) xs11' xt3' (Z_to_bv 64 (e_BUF E)) m')).
      { intros i2 err2 u2 xra' xt2' xa0' xa1' xs11' xt3' m' EQ INV2.
        rewrite ESL in EQ. inversion EQ; subst i2 err2 u2. clear EQ.
        zstep. rewrite lor_b2z. zstep.
        replace (Z_to_bv 64 i') with (Z_to_bv 64 (i' + 1 - 1)) by (f_equal; lia).
        apply (a1_bottom f HFOR (mkS1 (i' + 1) err' (uncl || u) (out ++ [i])) out i); cbn [s_idx s_out s_err]; try reflexivity; try assumption; lia. }
      step. unfold wz. rewrite (sx32_small len) by lia.
      zstep. s1norm. zstep. zstep.
      if_cases KL; zify_cond KL.
      +
        zstep. zstep. zstep.
        apply (K84C (i + 1)%Z err true); [apply str_loop_done; lia| exact INV'].
      + apply (a1_str_loop E OK SHZ _ (length bs) (i + 1) err (out ++ [i])); try assumption; try (unfold blen in *; lia).
  Qed.

  Theorem a1_for : forall f, a1_for_stmt E f.
  Proof using OK SHZ.
    induction f as [|f IH]; intros [idx err uncl out] xt1 xt2 xa0 xa1 xs11 xt3 xt4 m1 INV Hidx HF HN EOK;
      cbn [s_idx s_err s_unclosed s_out] in *; [exfalso; lia|].
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite scan_loop_S. cbn [s_idx s_err s_unclosed s_out].
    rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hidx)). cbv zeta.
    pose proof (ws_run_bounds bs (length bs) idx (proj2 Hidx)) as WB.
    set (r := ws_run bs (length bs) idx) in *.
    pose proof INV as INV'. a1_open_inv INV'.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (proj2 (proj2 (SHZ m1 MU WM))) as SHZB.
    assert (HEAD : forall xt2' xa1', xt2' = Z_to_bv 64 len ->
                   evt asegs (a1_postR E (if (len <=? r)%Z then mkS1 r err uncl out else scan_loop bs f (scan_token bs r (mkS1 idx err uncl out))))
                     (A1ST E 0xba444 (Z_to_bv 64 err) (Z_to_bv 64 (idx + 2)) xt2' xa0 xa1' (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out)))
                           (Z_to_bv 64 (Z.b2z uncl)) (Z_to_bv 64 idx) (Z_to_bv 64 (e_BUF E)) xs11 xt3 xt4 m1)).
    { intros xt2' xa1' ->.
      apply (a1_ws_loop E OK _ (length bs) idx); try assumption; try (unfold blen in *; lia).
      -
        intros xt3' Hr _. fold r in Hr |- *.
        rewrite (proj2 (Z.leb_gt _ _) Hr).
        apply (a1_token f IH (mkS1 idx err uncl out) r); cbn [s_idx s_err s_unclosed s_out]; try assumption; lia.
      -
        intros xt1' xa1'' xs9' xs11' xt3' xt4' Hr. fold r in Hr.
        rewrite (proj2 (Z.leb_le _ _) Hr).
        unfold a1_postR. cbn [s_out].
        apply (a1_tail E OK SHZ); [exact INV| lia| exact EOK]. }
    zstep. s1norm. zstep. zstep.
    if_cases K0; zify_cond K0.
    - zstep. apply HEAD. reflexivity.
    - zstep. zstep. apply HEAD. f_equal. lia.
  Qed.
End FOR.
