(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section TAIL.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma a1_epilogue : forall (code : Z) (out : list Z)
      x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (m : mem) (c0 c1 c2 c3 c320 : cell) (j296 j316 : list byte) (ws' : list word) (nxt' : word),
    rw_cells asegs m (bv_unsigned (e_sp E) + -432) [c0; c1; c2; c3] ->
    csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat ->
    rw_cells asegs m (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] ->
    rw_cells asegs m (bv_unsigned (e_sp E) + -144) (frame_hi_a E j296 j316 c320) -> csize c320 = 4%nat ->
    rw_cells asegs m (e_THIS E) (parser_cells E (wz (Z.of_nat (length out))) nxt' (wz (e_BUF E)) (wz len)) ->
    (code <> 13%Z -> nxt' = wz 0) ->
    u32arr asegs m (e_IDX E) ws' -> length ws' = e_cap E ->
    firstn (length out + 3) ws' = map wz (out ++ [len; len; 0%Z]) ->
    bytes_at asegs m (e_BUF E) (padded_bytes bs) ->
    mem_inv asegs m -> munch (a1_W E) (e_m0 E) m -> wmono asegs (e_m0 E) m ->
    stk asegs m (e_lo E) (bv_unsigned (e_sp E) + -432) ->
    evt asegs (a1_post E code out)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) x5 x6 x7 x8 x9 x10
               x11 (Z_to_bv 64 code) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 0xbc04c) (e_fc E) None m (seg_rom asegs)).
  Proof using OK.
    intros code out x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           m c0 c1 c2 c3 c320 j296 j316 ws' nxt' FRlo C0 C1 C2 C3 FRtb FRhi C320 PARSER NXT IDXA IDXL IDXF BUFRO MI MU WM ST.
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.

    pose proof (stk_release asegs m _ _ _ ST FRlo ltac:(lia)) as ST1.
    cbn [cells_size] in ST1. rewrite C0, C1, C2, C3 in ST1. cbn [Nat.add] in ST1.
    replace (bv_unsigned (e_sp E) + -432 + Z.of_nat 32)%Z with (bv_unsigned (e_sp E) + -400)%Z in ST1 by lia.
    pose proof (stk_release asegs m _ _ _ ST1 FRtb ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2.
    replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in ST2 by lia.
    pose proof (stk_release asegs m _ _ _ ST2 FRhi ltac:(lia)) as ST3.
    unfold frame_hi_a in ST3. cbn [cells_size] in ST3. rewrite C320 in ST3. cbn [csize Nat.add] in ST3.
    replace (bv_unsigned (e_sp E) + -144 + Z.of_nat 144)%Z with (bv_unsigned (e_sp E))%Z in ST3 by lia.

    unfold frame_hi_a in FRhi.
    change [C8 (wz (e_BUF E)); CB 8 j296; C8 (wz (e_THIS E)); C4 (wz len); CB 4 j316; c320; C4 (wz 0);
            C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
            C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)]
      with ([C8 (wz (e_BUF E)); CB 8 j296; C8 (wz (e_THIS E)); C4 (wz len); CB 4 j316; c320; C4 (wz 0)] ++
            [C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
             C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)]) in FRhi.
    apply rw_cells_app in FRhi. destruct FRhi as [_ FRsv].
    cbn [cells_size] in FRsv. rewrite C320 in FRsv. cbn [csize Nat.add] in FRsv.
    replace (bv_unsigned (e_sp E) + -144 + Z.of_nat 40)%Z with (bv_unsigned (e_sp E) + -104)%Z in FRsv by lia.
    zstep. do 13 zstep. zstep. zstep.
    apply evt_done. unfold s1_post_g.
    do 14 eexists. exists m, ws', nxt'.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
    split; [exact PARSER|]. split; [exact NXT|]. split; [exact IDXA|]. split; [exact IDXL|]. split; [exact IDXF| exact BUFRO].
  Qed.

  Lemma a1_tail : forall (idx err : Z) (uncl : bool) (out : list Z)
      x5 x6 x7 x10 x11 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (m1 : mem),
    A1INV E m1 out -> (Z.of_nat (length out) <= len)%Z -> err_ok err ->
    evt asegs (a1_post E (s1_code (mkS1 idx err uncl out)) out)
      (MS (mkR (Z_to_bv 64 err) (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) x5 x6 x7 (Z_to_bv 64 (e_IDX E)) (Z_to_bv 64 0) x10
               x11 (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out))) (Z_to_bv 64 (Z.b2z uncl)) x14 x15 x16 x17
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 len) (Z_to_bv 64 2147450880)
               x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 0xba928) (e_fc E) None m1 (seg_rom asegs)).
  Proof using OK SHZ.
    intros idx err uncl out x5 x6 x7 x10 x11 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1 INV Hn EOK.
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    pose proof (err_ok_range err EOK) as ERR64.
    a1_open_inv INV.
    set (n := Z.of_nat (length out)) in *.

    zstep.

    a1_shz_idx SHZ (e_IDX E + 4 * n)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true.
    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok asegs m (e_IDX E) ws n (wa (e_IDX E + 4 * n)) IDXA ltac:(lia) eq_refl) as SOK).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
      pose proof (u32arr_write asegs m (e_IDX E) ws n (Z_to_bv 64 len) IDXA ltac:(lia)) as IDXA1 end.
    store_done.

    zstep.
    a1_shz_idx SHZ (e_IDX E + 4 * n + 4)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8.
    step. unfold wz. rewrite (sx32_small len) by lia.
    zstep. if_true.
    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok asegs m (e_IDX E) _ (n + 1) (wa (e_IDX E + 4 * (n + 1))) IDXA1 ltac:(rewrite upd_length; lia) eq_refl) as SOK1).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
      pose proof (u32arr_write asegs m (e_IDX E) _ (n + 1) (Z_to_bv 64 len) IDXA1 ltac:(rewrite upd_length; lia)) as IDXA2 end.
    store_done.

    zstep.
    a1_shz_idx SHZ (e_IDX E + 4 * n + 8)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true.
    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok asegs m (e_IDX E) _ (n + 2) (wa (e_IDX E + 4 * (n + 2))) IDXA2 ltac:(rewrite !upd_length; lia) eq_refl) as SOK2).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
      pose proof (u32arr_write asegs m (e_IDX E) _ (n + 2) (Z_to_bv 64 0) IDXA2 ltac:(rewrite !upd_length; lia)) as IDXA3 end.
    store_done.
    assert (IDXF3 : firstn (length out + 3) (upd (upd (upd ws (Z.to_nat n) (Z_to_bv 64 len)) (Z.to_nat (n + 1)) (Z_to_bv 64 len)) (Z.to_nat (n + 2)) (Z_to_bv 64 0))
                    = map wz (out ++ [len; len; 0%Z])).
    { replace (Z.to_nat n) with (length out) by lia. replace (Z.to_nat (n + 1)) with (length out + 1)%nat by lia.
      replace (Z.to_nat (n + 2)) with (length out + 2)%nat by lia. apply arr_push3; [exact IDXF| lia]. }
    assert (IDXL3 : length (upd (upd (upd ws (Z.to_nat n) (Z_to_bv 64 len)) (Z.to_nat (n + 1)) (Z_to_bv 64 len)) (Z.to_nat (n + 2)) (Z_to_bv 64 0)) = e_cap E)
      by (rewrite !upd_length; exact IDXL).
    assert (EN : Z.shiftr (e_IDX E + 4 * n - e_IDX E) 2 = n).
    { replace (e_IDX E + 4 * n - e_IDX E)%Z with (n * 2 ^ 2)%Z by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. }

    zstep.
    a1_shz_this SHZ (e_THIS E + 8)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true.
    zstep. zstep. rewrite EN. zstep. s1norm. zstep. zstep. zstep.
    if_cases KN; zify_cond KN.
    - zstep.
      a1_shz_this SHZ (e_THIS E + 24)%Z.
      zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true.
      zstep. zstep. zstep. zstep.
      if_cases K5; zify_cond K5; [| exfalso; lia].
      zstep. zstep.
      assert (NE : (length out =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
      destruct uncl; cbn [Z.b2z Z.land Pos.land].
      +
        if_true. zstep. zstep. zstep.
        step. unfold wz. rewrite (sx32_small 15) by lia.
        assert (EC : s1_code (mkS1 idx err true out) = 15%Z) by (unfold s1_code; cbn [s_out s_unclosed]; rewrite NE; reflexivity).
        rewrite EC.
        eapply (a1_epilogue 15 out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (c2 := CB 8 j16) (c3 := CB 8 j24) (nxt' := Z_to_bv 64 0);
          try eassumption; try reflexivity.
      + if_false. zstep.
        step. unfold wz. rewrite (sx32_small err) by lia.
        assert (EC : s1_code (mkS1 idx err false out) = err) by (unfold s1_code; cbn [s_out s_unclosed s_err]; rewrite NE; reflexivity).
        rewrite EC.
        eapply (a1_epilogue err out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (c2 := CB 8 j16) (c3 := CB 8 j24) (nxt' := Z_to_bv 64 0);
          try eassumption; try reflexivity.
    -
      assert (EC : s1_code (mkS1 idx err uncl out) = 13%Z).
      { unfold s1_code. cbn [s_out]. replace (length out =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). reflexivity. }
      rewrite EC.
      zstep.
      eapply (a1_epilogue 13 out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (c2 := CB 8 j16) (c3 := CB 8 j24) (nxt' := nxt);
        try eassumption; try reflexivity.
      intros X; exfalso; apply X; reflexivity.
  Qed.
End TAIL.
