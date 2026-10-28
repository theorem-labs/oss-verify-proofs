(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_stage1_defs Sj_stage1_tail Sj_stage1_for.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition frame_mid_b (E : s1env) (j304 j312 j320 j328 j332 j336 j340 : list byte) : list cell :=
  [CB 8 j304; CB 8 j312; CB 8 j320; CB 4 j328; CB 4 j332; CB 4 j336; CB 4 j340;
   C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition b1_consts (m : mem) : Prop :=
  ro_cells bsegs m 1572552 [C8 (Z_to_bv 64 1612152)] /\ ro_cells bsegs m 1612152 [C8 (Z_to_bv 64 2147450880)].

Definition b1_W1 (E : s1env) : list ivl :=
  [ (bv_unsigned (e_sp E) + - 448, bv_unsigned (e_sp E)); (e_THIS E, e_THIS E + 96) ]%Z.

Lemma b1_W1_sub : forall E, sub_fp (b1_W1 E) (b1_W E).
Proof. intros E x. unfold b1_W1, s1_W_g. cbn [outside]. intros (H1 & H2 & _). split; [exact H1|]. split; [exact H2| exact I]. Qed.

Definition b1_mid (E : s1env) (nsi nxt : word) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (u5 u6 u7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
         (j0 j16 j24 j32 j40 jt j304 j312 j320 j328 j332 j336 j340 : list byte),
    ms = MS (mkR (Z_to_bv 64 B1_MEMCPY_RA) (Z_to_bv 64 (bv_unsigned (e_sp E) + -448)) (e_gp E) (e_tp E) u5 u6 u7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 0)
                 (Z_to_bv 64 (bv_unsigned (e_sp E) + -400)) (Z_to_bv 64 B1_TABLE) (Z_to_bv 64 256) x13 x14 x15 x16 x17
                 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 2147450880) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
                 (e_s10 E) (e_s11 E) x28 x29 x30 x31)
            (e_F E) (Z_to_bv 64 0x84728) (e_fc E) None m1 (seg_rom bsegs)
    /\ munch (b1_W1 E) (e_m0 E) m1 /\ wmono bsegs (e_m0 E) m1 /\ mem_inv bsegs m1
    /\ stk bsegs m1 (e_lo E) (bv_unsigned (e_sp E) + -448)
    /\ rw_cells bsegs m1 (bv_unsigned (e_sp E) + -448) [CB 16 j0; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40]
    /\ rw_cells bsegs m1 (bv_unsigned (e_sp E) + -400) [CB 256 jt]
    /\ rw_cells bsegs m1 (bv_unsigned (e_sp E) + -144) (frame_mid_b E j304 j312 j320 j328 j332 j336 j340)
    /\ rw_cells bsegs m1 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E))).

Section TOP.
  Variable E : s1env.
  Hypothesis OK : env_ok_b E.
  Hypothesis SHZ : b1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma b1_walk1 : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (nsi nxt bufo leno : word),
    mem_inv bsegs (e_m0 E) -> b1_consts (e_m0 E) ->
    stk bsegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E)) ->
    rw_cells bsegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt bufo leno) ->
    evt bsegs (b1_mid E nsi nxt)
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E)
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 len) (Z_to_bv 64 0) a4 a5 a6 a7
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
          (e_F E) (Z_to_bv 64 B1_ENTRY) (e_fc E) None (e_m0 E) (seg_rom bsegs)).
  Proof using OK SHZ.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno MI (G1 & G2) ST PARSER.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, B1_STACK, B1_GTOP, B1_ENTRY in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    assert (LO0 : (0 <= e_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl (b1_W E) (e_m0 E)) as MU. pose proof (wmono_refl bsegs (e_m0 E)) as WM.
    pose proof (munch_refl (b1_W1 E) (e_m0 E)) as MUt.
    unfold s1_W_g in MU. cbn [Z.opp] in MU. unfold b1_W1 in MUt. cbn [Z.opp] in MUt. unfold parser_cells in PARSER.
    set (m := e_m0 E) in MI, G1, G2, ST, PARSER, MU at 2, MUt at 2, WM at 2 |- *.
    clearbody m.
    step.
    carve_frame 448%nat ST.
    apply (rw_cells_split_CB bsegs m _ [] 448 junk [] [16;8;8;8;8;256;8;8;8;4;4;4;4;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    zstep. zstep. zstep. zstep. clear G1 G2. zstep.

    zstep.
    b1_shz_this SHZ (e_THIS E + 72)%Z.
    zstep. rewrite shr3_div. zstep. zstep. s1norm. zstep. if_true.
    zstep. zstep.

    zstep.
    b1_shz_this SHZ (e_THIS E + 80)%Z.
    zstep. rewrite shr3_div. zstep. zstep. s1norm. zstep. if_true.
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.

    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?ct :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: ct :: rest) with ([c0; c1; c2; c3; c4] ++ [ct] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FRlo FR]. apply rw_cells_app in FR. destruct FR as [FRtb FRhi].
    cbn [cells_size csize Nat.add] in FRtb, FRhi.
    replace (bv_unsigned (e_sp E) + -448 + Z.of_nat 48)%Z with (bv_unsigned (e_sp E) + -400)%Z in * by lia.
    replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in * by lia.
    apply evt_done. unfold b1_mid, frame_mid_b, parser_cells, B1_MEMCPY_RA, B1_TABLE.
    do 26 eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MUt|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FRlo|]. split; [exact FRtb|]. split; [exact FRhi| exact PARSER].
  Qed.

  Theorem b1_walk2 : forall u5 u6 u7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (nsi nxt : word) (ws0 : list word)
      (j0 j16 j24 j32 j40 j304 j312 j320 j328 j332 j336 j340 : list byte),
    mem_inv bsegs (e_m0 E) ->
    stk bsegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E) + -448) ->
    rw_cells bsegs (e_m0 E) (bv_unsigned (e_sp E) + -448) [CB 16 j0; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40] ->
    rw_cells bsegs (e_m0 E) (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] ->
    rw_cells bsegs (e_m0 E) (bv_unsigned (e_sp E) + -144) (frame_mid_b E j304 j312 j320 j328 j332 j336 j340) ->
    rw_cells bsegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz len)) ->
    u32arr bsegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E ->
    bytes_at bsegs (e_m0 E) (e_BUF E) (padded_bytes bs) ->
    evt bsegs (b1_post E (fst (stage1 bs)) (snd (stage1 bs)))
      (MS (mkR (Z_to_bv 64 B1_MEMCPY_RA) (Z_to_bv 64 (bv_unsigned (e_sp E) + -448)) (e_gp E) (e_tp E) u5 u6 u7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 0)
               v x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 len) (Z_to_bv 64 2147450880) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
               (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 B1_MEMCPY_RA) (e_fc E) None (e_m0 E) (seg_rom bsegs)).
  Proof using OK SHZ.
    intros u5 u6 u7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 nsi nxt ws0 j0 j16 j24 j32 j40 j304 j312 j320 j328 j332 j336 j340
           MI ST FRlo FRtb FRhi PARSER IDXA IDXL BUFRO.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, B1_STACK, B1_GTOP, B1_MEMCPY_RA in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    pose proof (padded_bytes_blen bs) as PBL.
    pose proof (munch_refl (b1_W E) (e_m0 E)) as MU. pose proof (wmono_refl bsegs (e_m0 E)) as WM.
    unfold s1_W_g in MU. cbn [Z.opp] in MU. unfold parser_cells in PARSER. unfold frame_mid_b in FRhi.
    set (m := e_m0 E) in MI, ST, FRlo, FRtb, FRhi, PARSER, IDXA, BUFRO, MU at 2, WM at 2 |- *.
    clearbody m.
    zstep.
    zstep.
    b1_shz_this SHZ (e_THIS E + 16)%Z.
    zstep. rewrite shr3_div. zstep. zstep. s1norm. zstep. if_true.
    zstep. zstep. s1norm. zstep. zstep. zstep. zstep. zstep. zstep.
    assert (IDXF : firstn (length (@nil Z)) ws0 = map wz []) by reflexivity.
    assert (EOK0 : err_ok 0) by (left; reflexivity).
    replace (wz (e_IDX E)) with (wz (e_IDX E + 4 * Z.of_nat (length (@nil Z)))) in FRhi by (unfold wz; f_equal; cbn [length Z.of_nat]; lia).
    s1_cur_mem ltac:(fun mm => assert (INV0 : B1INV E mm [] 0 0) by b1_close_inv).
    unfold stage1, stage1_st. cbn [fst snd].
    zstep.
    if_cases KZ; zify_cond KZ.
    -
      zstep. zstep.
      rewrite scan_loop_S. cbn [s_idx s1_init].
      replace (0 <? len)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      eapply evt_eq; [| eapply (b1_tail E OK SHZ 0 SUCCESS false [] 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0)];
        [cbn [length Z.b2z]; s1_st_eq| cbn; lia| exact EOK0].
    - zstep. if_cases KB; zify_cond KB; [|exfalso; lia].
      do 17 zstep. s1norm.
      rewrite !lxor_ones64 by lia.
      eapply evt_eq; [| eapply (b1_for E OK SHZ (S (length bs)) s1_init _ _ _ _ _ _ INV0)];
        [cbn [s_idx s_out s_err s_unclosed s1_init length Z.b2z]; unfold SUCCESS, wz; s1_st_eq
        | cbn [s_idx s_out s_err s1_init length]; unfold blen in *; try lia; try exact EOK0 ..].
  Qed.
End TOP.
