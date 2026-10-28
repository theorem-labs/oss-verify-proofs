(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section TAIL.
  Variable E : s1env.
  Hypothesis OK : env_ok_u E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma u1_epilogue : forall (code : Z) (out : list Z)
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (m : mem) (c0 c1 c2 c3 : cell) (nptr : word) (idxc err : Z) (ws' : list word) (nxt' : word),
    rw_cells usegs m (bv_unsigned (e_sp E) + -432) [c0; c1; c2; c3] -> csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat ->
    rw_cells usegs m (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] ->
    rw_cells usegs m (bv_unsigned (e_sp E) + -144) (uframe_hi E nptr idxc err) ->
    rw_cells usegs m (e_THIS E) (parser_cells E (wz (Z.of_nat (length out))) nxt' (wz (e_BUF E)) (wz len)) ->
    (code <> 13%Z -> nxt' = wz 0) ->
    u32arr usegs m (e_IDX E) ws' -> length ws' = e_cap E ->
    firstn (length out + 3) ws' = map wz (out ++ [len; len; 0%Z]) ->
    bytes_at usegs m (e_BUF E) (padded_bytes bs) ->
    mem_inv usegs m -> munch (u1_W E) (e_m0 E) m -> wmono usegs (e_m0 E) m ->
    stk usegs m (e_lo E) (bv_unsigned (e_sp E) + -432) ->
    evt usegs (u1_post E code out)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) x5 x6 x7 x8 x9 (Z_to_bv 64 code)
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 0x430bc) (e_fc E) None m (seg_rom usegs)).
  Proof using OK.
    intros code out x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           m c0 c1 c2 c3 nptr idxc err ws' nxt' FRlo C0 C1 C2 C3 FRtb FRhi PARSER NXT IDXA IDXL IDXF BUFRO MI MU WM ST.
    destruct OK as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold uframe_hi in FRhi.
    do 13 zstep. zstep. zstep.
    pose proof (stk_release usegs m _ _ _ ST FRlo ltac:(lia)) as ST1.
    cbn [cells_size] in ST1. rewrite C0, C1, C2, C3 in ST1. cbn [Nat.add] in ST1.
    replace (bv_unsigned (e_sp E) + -432 + Z.of_nat 32)%Z with (bv_unsigned (e_sp E) + -400)%Z in ST1 by lia.
    pose proof (stk_release usegs m _ _ _ ST1 FRtb ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2.
    replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in ST2 by lia.
    pose proof (stk_release usegs m _ _ _ ST2 FRhi ltac:(lia)) as ST3.
    cbn [cells_size csize Nat.add] in ST3.
    replace (bv_unsigned (e_sp E) + -144 + Z.of_nat 144)%Z with (bv_unsigned (e_sp E))%Z in ST3 by lia.
    apply evt_done. unfold s1_post_g.
    do 14 eexists. exists m, ws', nxt'.
    split; [cbv delta [mkR]; reflexivity|].
    do 9 (split; [eassumption|]). exact BUFRO.
  Qed.

  Lemma u1_tail : forall (idx err : Z) (uncl : bool) (out : list Z) (idxc : Z)
      x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 (m1 : mem),
    U1INV E m1 out idxc err -> (Z.of_nat (length out) <= len)%Z -> err_ok err ->
    evt usegs (u1_post E (s1_code (mkS1 idx err uncl out)) out)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) x5 x6 x7 (Z_to_bv 64 (e_THIS E)) x9
               (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out))) (Z_to_bv 64 (e_IDX E)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 0) x19 (Z_to_bv 64 len) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (Z.b2z uncl)) x29 x30 x31)
          (e_F E) (Z_to_bv 64 0x41d54) (e_fc E) None m1 (seg_rom usegs)).
  Proof using OK.
    intros idx err uncl out idxc x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 m1 INV Hn EOK.
    pose proof (err_ok_range err EOK) as ERR64.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    u1_open_inv INV.
    set (n := Z.of_nat (length out)) in *.
    pose proof (align4_ok (e_IDX E) n ALIGN ltac:(lia)) as AL.
    zstep. if_cases G1; zify_cond G1; [|exfalso; lia].
    zstep. rewrite AL. zstep. if_true. zstep.

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok usegs m (e_IDX E) ws n (wa (e_IDX E + 4 * n)) IDXA ltac:(lia) eq_refl) as SOK).
    step.
    pose proof (u32arr_write usegs m1 (e_IDX E) ws n (Z_to_bv 64 len) IDXA ltac:(lia)) as IDXA1.
    store_done.
    zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
    zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
    zstep. zstep.

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok usegs m (e_IDX E) _ (n + 1) (wa (e_IDX E + 4 * (n + 1))) IDXA1 ltac:(rewrite upd_length; lia) eq_refl) as SOK).
    step. unfold wz. rewrite (sx32_small len) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
      pose proof (u32arr_write usegs m (e_IDX E) _ (n + 1) (Z_to_bv 64 len) IDXA1 ltac:(rewrite upd_length; lia)) as IDXA2 end.
    store_done.
    zstep. if_cases G4; zify_cond G4; [|exfalso; lia].

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok usegs m (e_IDX E) _ (n + 2) (wa (e_IDX E + 4 * (n + 2))) IDXA2 ltac:(rewrite !upd_length; lia) eq_refl) as SOK).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
      pose proof (u32arr_write usegs m (e_IDX E) _ (n + 2) (Z_to_bv 64 0) IDXA2 ltac:(rewrite !upd_length; lia)) as IDXA3 end.
    store_done.
    assert (IDXF3 : firstn (length out + 3) (upd (upd (upd ws (Z.to_nat n) (Z_to_bv 64 len)) (Z.to_nat (n + 1)) (Z_to_bv 64 len)) (Z.to_nat (n + 2)) (Z_to_bv 64 0))
                    = map wz (out ++ [len; len; 0%Z])).
    { replace (Z.to_nat n) with (length out) by lia. replace (Z.to_nat (n + 1)) with (length out + 1)%nat by lia.
      replace (Z.to_nat (n + 2)) with (length out + 2)%nat by lia. apply arr_push3; [exact IDXF| lia]. }
    assert (IDXL3 : length (upd (upd (upd ws (Z.to_nat n) (Z_to_bv 64 len)) (Z.to_nat (n + 1)) (Z_to_bv 64 len)) (Z.to_nat (n + 2)) (Z_to_bv 64 0)) = e_cap E)
      by (rewrite !upd_length; exact IDXL).
    assert (EN : Z.shiftr (e_IDX E + 4 * n - e_IDX E) 2 = n).
    { replace (e_IDX E + 4 * n - e_IDX E)%Z with (n * 2 ^ 2)%Z by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. }
    zstep. zstep. rewrite EN. zstep. s1norm. zstep. zstep. zstep.
    if_cases KN; zify_cond KN.
    - zstep. zstep. zstep. zstep.
      if_cases K5; zify_cond K5; [| exfalso; lia].
      zstep. zstep.
      assert (NE : (length out =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
      destruct uncl; cbn [Z.b2z Z.land Pos.land].
      + if_false. zstep. zstep.
        assert (EC : s1_code (mkS1 idx err true out) = 15%Z) by (unfold s1_code; cbn [s_out s_unclosed]; rewrite NE; reflexivity).
        rewrite EC.
        eapply (u1_epilogue 15 out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (c2 := CB 8 j16) (c3 := CB 8 j24) (nxt' := Z_to_bv 64 0); try eassumption; try reflexivity.
      + if_true. zstep. unfold wz. rewrite (sx32_small err) by lia. zstep. zstep.
        if_cases G5; zify_cond G5; [exfalso; lia|].
        assert (EC : s1_code (mkS1 idx err false out) = err) by (unfold s1_code; cbn [s_out s_unclosed s_err]; rewrite NE; reflexivity).
        rewrite EC.
        eapply (u1_epilogue err out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (c2 := CB 8 j16) (c3 := CB 8 j24) (nxt' := Z_to_bv 64 0); try eassumption; try reflexivity.
    -
      zstep.
      assert (EC : s1_code (mkS1 idx err uncl out) = 13%Z).
      { unfold s1_code. cbn [s_out]. replace (length out =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). reflexivity. }
      rewrite EC.
      eapply (u1_epilogue 13 out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (c2 := CB 8 j16) (c3 := CB 8 j24) (nxt' := nxt); try eassumption; try reflexivity.
      intros X; exfalso; apply X; reflexivity.
  Qed.
End TAIL.
