(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage1.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage1_defs Sj_stage1_ws Sj_stage1_prim Sj_stage1_str Sj_stage1_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FOR.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma s1_bottom : forall (f : nat), s1_for_stmt E f ->
    forall (st' : s1st) (out : list Z) (i : Z) xra xt2 xs11 xt3 xt4 xt5 xt6 (m1 : mem),
    s_out st' = out ++ [i] -> S1INV E m1 (out ++ [i]) ->
    (Z.of_nat (length out) + 1 <= s_idx st' <= len + 4)%Z -> (Z.of_nat (length out) + 1 <= len)%Z ->
    (len - s_idx st' <= Z.of_nat f)%Z ->
    evt psegs (s1_postR E (scan_loop bs f st'))
      (S1ST E 0x433f8 xra xt2 (Z_to_bv 64 (s_err st')) (Z_to_bv 64 (Z.b2z (s_unclosed st')))
            (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out))) (Z_to_bv 64 (s_idx st' - 1)) xs11 xt3 xt4 xt5 xt6 m1).
  Proof using OK.
    intros f HFOR st' out i xra xt2 xs11 xt3 xt4 xt5 xt6 m1 EO INV HB HN HF.
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, S1_STACK, S1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO : length (s_out st') = S (length out)) by (rewrite EO, length_app; cbn; lia).
    zstep. s1norm. zstep. s1norm. zstep. zstep.
    replace (Z_to_bv 64 (s_idx st' - 1 + 1)) with (Z_to_bv 64 (s_idx st')) by (f_equal; lia).
    replace (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out) + 4)) with (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st'))))
      by (f_equal; lia).
    if_cases KLT; zify_cond KLT.
    -
      apply HFOR; try lia. rewrite EO. exact INV.
    -
      zstep. rewrite scan_loop_done by lia.
      unfold s1_postR. destruct st' as [idx' err' uncl' out']. cbn [s_idx s_err s_unclosed s_out] in *. subst out'.
      apply (s1_tail E OK); [exact INV| lia].
  Qed.

  Ltac push_store i :=
    lazymatch goal with
    | IDXA : u32arr psegs ?m (e_IDX E) ?ws, IDXF : firstn (length ?out) ?ws = map wz ?out |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        let n := constr:(Z.of_nat (length out)) in
        pose proof (u32arr_store_ok psegs m (e_IDX E) ws n (wa (e_IDX E + 4 * n)) IDXA ltac:(lia) eq_refl) as SOK;
        step;
        pose proof (u32arr_write psegs m (e_IDX E) ws n (Z_to_bv 64 i) IDXA ltac:(lia)) as IDXA';
        store_done;
        assert (IDXF' : firstn (length (out ++ [i])) (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = map wz (out ++ [i]))
          by (rewrite Nat2Z.id; apply arr_push; [exact IDXF| lia]);
        assert (IDXL' : length (upd ws (Z.to_nat n) (Z_to_bv 64 i)) = e_cap E) by (rewrite upd_length; assumption);
        clear IDXF
    end.

  Lemma s1_token : forall (f : nat), s1_for_stmt E f ->
    forall (st : s1st) (i : Z) xra xs11 xt5 xt6 (m1 : mem),
    S1INV E m1 (s_out st) -> (0 <= s_idx st <= i)%Z -> (i < len)%Z -> (len - i <= Z.of_nat (S f))%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z ->
    evt psegs (s1_postR E (scan_loop bs f (scan_token bs i st)))
      (S1ST E 0x43138 xra (Z_to_bv 64 (i + 2)) (Z_to_bv 64 (s_err st)) (Z_to_bv 64 (Z.b2z (s_unclosed st)))
            (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st)))) (Z_to_bv 64 i) xs11
            (Z_to_bv 64 len) (Z_to_bv 64 (e_BUF E + i)) xt5 xt6 m1).
  Proof using OK.
    intros f HFOR [idx err uncl out] i xra xs11 xt5 xt6 m1 INV Hidx Hi HF HN.
    cbn [s_idx s_err s_unclosed s_out] in *.
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, S1_STACK, S1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    unfold scan_token. fold c. cbn [s_idx s_err s_unclosed s_out].
    s1_open_inv INV.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (buf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (tbl_read m1 _ c TBL CR) as RD2.
    zstep.
    if_cases KGE; zify_cond KGE; [exfalso; lia|].
    zstep. s1norm. zstep.
    if_cases K34; zify_cond K34.
    -
      rewrite (proj2 (Z.eqb_neq _ _) K34).
      zstep. zstep. s1norm. zstep.
      push_store i.
      assert (INV' : S1INV E m (out ++ [i])) by s1_close_inv.
      zstep.
      if_cases K2; zify_cond K2.
      +
        assert (TO : t_op c = true) by (unfold t_op; rewrite (proj2 (Z.eqb_neq _ _) K2); reflexivity).
        rewrite TO.
        replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + 1 - 1)) by (f_equal; lia).
        apply (s1_bottom f HFOR (mkS1 (i + 1) err uncl (out ++ [i])) out i); cbn [s_idx s_out]; try reflexivity; try assumption; lia.
      +
        assert (TO : t_op c = false) by (unfold t_op; rewrite (proj2 (Z.eqb_eq _ _) K2); reflexivity).
        rewrite TO.
        assert (LB : (0 < length bs)%nat) by (unfold blen in *; lia).
        rewrite (prim_run_unfold bs (length bs) i LB).

        assert (KBOT : forall r xt2' xt3' xt4', (i <= r < len)%Z ->
                  evt psegs (s1_postR E (scan_loop bs f (mkS1 (r + 1) err uncl (out ++ [i]))))
                    (S1ST E 0x433f8 xra xt2' (Z_to_bv 64 err) (Z_to_bv 64 (Z.b2z uncl)) (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out)))
                          (Z_to_bv 64 r) xs11 xt3' xt4' xt5 xt6 m)).
        { intros r xt2' xt3' xt4' Hr.
          replace (Z_to_bv 64 r) with (Z_to_bv 64 (r + 1 - 1)) by (f_equal; lia).
          apply (s1_bottom f HFOR (mkS1 (r + 1) err uncl (out ++ [i])) out i); cbn [s_idx s_out]; try reflexivity; try assumption; lia. }
        zstep. s1norm. zstep. s1norm. zstep.
        if_cases KL; zify_cond KL.
        *
          rewrite (proj2 (Z.ltb_ge _ _) KL). cbn [andb]. apply KBOT. lia.
        * rewrite (proj2 (Z.ltb_lt _ _) KL). cbn [andb].
          pose proof (B_range bs (i + 1) BOK) as CR1. set (c1 := B bs (i + 1)) in *.
          pose proof (tbl_range c1) as TR1.
          pose proof (buf_read m (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD3. fold c1 in RD3.
          pose proof (tbl_read m _ c1 TBL CR1) as RD4.
          zstep. zstep. s1norm. zstep. zstep. s1norm. zstep.
          if_cases K30; zify_cond K30.
          -- rewrite (proj2 (Z.eqb_eq _ _) K30). rewrite andb_false_r. apply KBOT. lia.
          -- rewrite (proj2 (Z.eqb_neq _ _) K30). rewrite andb_true_r.
             zstep. zstep. s1norm. zstep. zstep.
             if_cases K3; zify_cond K3.
             ++ assert (TS : t_space_or_op c1 = true) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_neq _ _) K3); reflexivity).
                rewrite TS. cbn [negb]. apply KBOT. lia.
             ++ assert (TS : t_space_or_op c1 = false) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_eq _ _) K3); reflexivity).
                rewrite TS. cbn [negb].
                zstep. zstep. s1norm. zstep.
                pose proof (prim_run_bounds bs (pred (length bs)) (i + 1) ltac:(lia)) as PB.
                replace (Z_to_bv 64 (e_BUF E + (i + 2))) with (Z_to_bv 64 (e_BUF E + (i + 1) + 1)) by (f_equal; lia).
                replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + 1 - 1)) by (f_equal; lia).
                apply (s1_prim_loop E OK _ (pred (length bs)) (i + 1)); try assumption; try (unfold blen in *; lia).
                ** intros xt2' xt3'. apply KBOT. lia.
                **
                   intros xt2' xt3' ER. rewrite ER.
                   zstep. s1norm. zstep. s1norm. zstep. zstep.
                   if_cases KLT; zify_cond KLT; [exfalso; lia|].
                   zstep. rewrite scan_loop_done by (cbn [s_idx]; lia).
                   unfold s1_postR. cbn [s_out].
                   replace (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out) + 4)) with (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (out ++ [i]))))
                     by (f_equal; rewrite length_app; cbn [length]; lia).
                   apply (s1_tail E OK); [exact INV'| rewrite length_app; cbn [length]; lia].
    -
      rewrite (proj2 (Z.eqb_eq _ _) K34).
      push_store i.
      assert (INV' : S1INV E m (out ++ [i])) by s1_close_inv.
      destruct (str_loop bs (length bs) (i + 1) err) as [[i' err'] u] eqn:ESL.
      pose proof (str_loop_bounds bs _ _ _ _ _ _ ESL) as SB.

      assert (KFD0 : forall i2 err2 (u2 : bool) xt2' xa2' xt3' xt4' xt5' xt6' m',
                 str_loop bs (length bs) (i + 1) err = (i2, err2, u2) -> S1INV E m' (out ++ [i]) ->
                 evt psegs (s1_postR E (scan_loop bs f (mkS1 (i' + 1) err' (uncl || u) (out ++ [i]))))
                   (S1ST E 0x433f0 (Z_to_bv 64 err2) xt2' xa2' (Z_to_bv 64 (Z.b2z uncl)) (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out)))
                         (Z_to_bv 64 i2) (Z_to_bv 64 (Z.b2z u2)) xt3' xt4' xt5' xt6' m')).
      { intros i2 err2 u2 xt2' xa2' xt3' xt4' xt5' xt6' m' EQ INV2.
        rewrite ESL in EQ. inversion EQ; subst i2 err2 u2. clear EQ.
        zstep. rewrite lor_b2z. zstep.
        replace (Z_to_bv 64 i') with (Z_to_bv 64 (i' + 1 - 1)) by (f_equal; lia).
        apply (s1_bottom f HFOR (mkS1 (i' + 1) err' (uncl || u) (out ++ [i])) out i); cbn [s_idx s_out]; try reflexivity; try assumption; lia. }
      zstep. s1norm. zstep. zstep.
      if_cases KL; zify_cond KL.
      +
        zstep. zstep. zstep.
        apply (KFD0 (i + 1)%Z err true); [apply str_loop_done; lia| exact INV'].
      + apply (s1_str_loop E OK _ (length bs) (i + 1) err (out ++ [i])); try assumption; try (unfold blen in *; lia).
  Qed.

  Theorem s1_for : forall f, s1_for_stmt E f.
  Proof using OK.
    induction f as [|f IH]; intros [idx err uncl out] xra xt2 xs11 xt3 xt4 xt5 xt6 m1 INV Hidx HF HN;
      cbn [s_idx s_err s_unclosed s_out] in *; [exfalso; lia|].
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, S1_STACK, S1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite scan_loop_S. cbn [s_idx s_err s_unclosed s_out].
    rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hidx)). cbv zeta.
    pose proof (ws_run_bounds bs (length bs) idx (proj2 Hidx)) as WB.
    set (r := ws_run bs (length bs) idx) in *.
    pose proof INV as INV'. s1_open_inv INV'.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    assert (HEAD : evt psegs (s1_postR E (if (len <=? r)%Z then mkS1 r err uncl out else scan_loop bs f (scan_token bs r (mkS1 idx err uncl out))))
                     (S1ST E 0x43108 xra (Z_to_bv 64 (idx + 2)) (Z_to_bv 64 err) (Z_to_bv 64 (Z.b2z uncl))
                           (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out))) (Z_to_bv 64 idx) xs11 (Z_to_bv 64 len) xt4 xt5 xt6 m1)).
    { apply (s1_ws_loop E OK _ (length bs) idx); try assumption; try (unfold blen in *; lia).
      -
        intros xs11' Hr _. fold r in Hr |- *.
        rewrite (proj2 (Z.leb_gt _ _) Hr).
        apply (s1_token f IH (mkS1 idx err uncl out) r); cbn [s_idx s_err s_unclosed s_out]; try assumption; lia.
      -
        intros xt2' xs10' xs11' xt3' xt4' Hr. fold r in Hr.
        rewrite (proj2 (Z.leb_le _ _) Hr).
        unfold s1_postR. cbn [s_out].
        apply (s1_tail E OK); [exact INV| lia]. }
    zstep. s1norm. zstep. zstep.
    if_cases K0; zify_cond K0.
    - zstep. exact HEAD.
    - zstep. zstep. replace (Z_to_bv 64 (idx + 1)) with (Z_to_bv 64 len) by (f_equal; lia). exact HEAD.
  Qed.
End FOR.
