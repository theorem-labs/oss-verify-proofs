(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpg.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section TAIL.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma s1_epilogue : forall (code : Z) (out : list Z)
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (m : mem) (c0 c1 : cell) (j280 j300 : list byte) (ws' : list word) (nxt' : word),
    rw_cells psegs m (bv_unsigned (e_sp E) + -416) [c0; c1] -> csize c0 = 8%nat -> csize c1 = 8%nat ->
    rw_cells psegs m (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] ->
    rw_cells psegs m (bv_unsigned (e_sp E) + -144) (frame_hi E j280 j300) ->
    rw_cells psegs m (e_THIS E) (parser_cells E (wz (Z.of_nat (length out))) nxt' (wz (e_BUF E)) (wz len)) ->
    (code <> 13%Z -> nxt' = wz 0) ->
    u32arr psegs m (e_IDX E) ws' -> length ws' = e_cap E ->
    firstn (length out + 3) ws' = map wz (out ++ [len; len; 0%Z]) ->
    bytes_at psegs m (e_BUF E) (padded_bytes bs) ->
    mem_inv psegs m -> munch (s1_W E) (e_m0 E) m -> wmono psegs (e_m0 E) m ->
    stk psegs m (e_lo E) (bv_unsigned (e_sp E) + -416) ->
    evt psegs (s1_post E code out)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (e_sp E) + -416)) (e_gp E) (e_tp E) x5 x6 x7 x8 x9 (Z_to_bv 64 code)
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 0x2a5ec) (e_fc E) None m (seg_rom psegs)).
  Proof using OK.
    intros code out x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           m c0 c1 j280 j300 ws' nxt' FRlo C0 C1 FRtb FRhi PARSER NXT IDXA IDXL IDXF BUFRO MI MU WM ST.
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, S1_STACK, S1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold frame_hi in FRhi.
    do 13 zstep. zstep. zstep.

    pose proof (stk_release psegs m _ _ _ ST FRlo ltac:(lia)) as ST1.
    cbn [cells_size] in ST1. rewrite C0, C1 in ST1. cbn [Nat.add] in ST1.
    replace (bv_unsigned (e_sp E) + -416 + Z.of_nat 16)%Z with (bv_unsigned (e_sp E) + -400)%Z in ST1 by lia.
    pose proof (stk_release psegs m _ _ _ ST1 FRtb ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2.
    replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in ST2 by lia.
    pose proof (stk_release psegs m _ _ _ ST2 FRhi ltac:(lia)) as ST3.
    cbn [cells_size csize Nat.add] in ST3.
    replace (bv_unsigned (e_sp E) + -144 + Z.of_nat 144)%Z with (bv_unsigned (e_sp E))%Z in ST3 by lia.
    apply evt_done. unfold s1_post.
    do 14 eexists. exists m, ws', nxt'.
    split; [cbv delta [mkR]; reflexivity|].
    do 9 (split; [eassumption|]). exact BUFRO.
  Qed.

  Lemma s1_tail : forall (idx err : Z) (uncl : bool) (out : list Z)
      x1 x5 x6 x7 x9 x10 x13 x14 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (m1 : mem),
    S1INV E m1 out -> (Z.of_nat (length out) <= len)%Z ->
    evt psegs (s1_post E (s1_code (mkS1 idx err uncl out)) out)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (e_sp E) + -416)) (e_gp E) (e_tp E) x5 x6 x7 (Z_to_bv 64 (e_THIS E)) x9 x10
               (Z_to_bv 64 (e_IDX E)) (Z_to_bv 64 err) x13 x14 (Z_to_bv 64 (Z.b2z uncl))
               (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length out))) x17 (Z_to_bv 64 0) (Z_to_bv 64 len)
               x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 0x2980c) (e_fc E) None m1 (seg_rom psegs)).
  Proof using OK.
    intros idx err uncl out x1 x5 x6 x7 x9 x10 x13 x14 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1 INV Hn.
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, S1_STACK, S1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    s1_open_inv INV.
    set (n := Z.of_nat (length out)) in *.

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok psegs m (e_IDX E) ws n (wa (e_IDX E + 4 * n)) IDXA ltac:(lia) eq_refl) as SOK).
    step.
    s1_cur_mem ltac:(fun m => idtac).
    pose proof (u32arr_write psegs m1 (e_IDX E) ws n (Z_to_bv 64 len) IDXA ltac:(lia)) as IDXA1.
    store_done.
    assert (EN : Z.shiftr (e_IDX E + 4 * n - e_IDX E) 2 = n).
    { replace (e_IDX E + 4 * n - e_IDX E)%Z with (n * 2 ^ 2)%Z by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. }
    zstep. s1norm. zstep. zstep. rewrite EN. zstep. s1norm.

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok psegs m (e_IDX E) _ (n + 1) (wa (e_IDX E + 4 * (n + 1))) IDXA1 ltac:(rewrite upd_length; lia) eq_refl) as SOK).
    step. unfold wz. rewrite (sx32_small len) by lia.
    s1_cur_mem ltac:(fun m => idtac).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
      pose proof (u32arr_write psegs m (e_IDX E) _ (n + 1) (Z_to_bv 64 len) IDXA1 ltac:(rewrite upd_length; lia)) as IDXA2 end.
    store_done.

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok psegs m (e_IDX E) _ (n + 2) (wa (e_IDX E + 4 * (n + 2))) IDXA2 ltac:(rewrite !upd_length; lia) eq_refl) as SOK).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
      pose proof (u32arr_write psegs m (e_IDX E) _ (n + 2) (Z_to_bv 64 0) IDXA2 ltac:(rewrite !upd_length; lia)) as IDXA3 end.
    store_done.
    assert (IDXF3 : firstn (length out + 3) (upd (upd (upd ws (Z.to_nat n) (Z_to_bv 64 len)) (Z.to_nat (n + 1)) (Z_to_bv 64 len)) (Z.to_nat (n + 2)) (Z_to_bv 64 0))
                    = map wz (out ++ [len; len; 0%Z])).
    { replace (Z.to_nat n) with (length out) by lia. replace (Z.to_nat (n + 1)) with (length out + 1)%nat by lia.
      replace (Z.to_nat (n + 2)) with (length out + 2)%nat by lia. apply arr_push3; [exact IDXF| lia]. }
    assert (IDXL3 : length (upd (upd (upd ws (Z.to_nat n) (Z_to_bv 64 len)) (Z.to_nat (n + 1)) (Z_to_bv 64 len)) (Z.to_nat (n + 2)) (Z_to_bv 64 0)) = e_cap E)
      by (rewrite !upd_length; exact IDXL).

    zstep. zstep. zstep.
    if_cases KN; zify_cond KN.
    -
      assert (EC : s1_code (mkS1 idx err uncl out) = 13%Z).
      { unfold s1_code. cbn [s_out]. replace (length out =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). reflexivity. }
      rewrite EC.
      eapply (s1_epilogue 13 out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (nxt' := nxt); try eassumption; try reflexivity.
      intros X; exfalso; apply X; reflexivity.
    - zstep. zstep. zstep. zstep.
      if_cases K5; zify_cond K5; [| exfalso; lia].
      zstep. zstep.
      assert (NE : (length out =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
      destruct uncl; cbn [Z.b2z Z.land Pos.land].
      +
        if_false. zstep. zstep. zstep.
        assert (EC : s1_code (mkS1 idx err true out) = 15%Z) by (unfold s1_code; cbn [s_out s_unclosed]; rewrite NE; reflexivity).
        rewrite EC.
        eapply (s1_epilogue 15 out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (nxt' := Z_to_bv 64 0); try eassumption; try reflexivity.
      + if_true. zstep.
        assert (EC : s1_code (mkS1 idx err false out) = err) by (unfold s1_code; cbn [s_out s_unclosed s_err]; rewrite NE; reflexivity).
        rewrite EC.
        eapply (s1_epilogue err out) with (c0 := CB 8 j0) (c1 := CB 8 j8) (nxt' := Z_to_bv 64 0); try eassumption; try reflexivity.
  Qed.
End TAIL.
