(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage1_defs Sj_stage1_tail Sj_stage1_for.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition frame_mid_a (E : s1env) (j288 j296 j304 j312 j316 j320 j324 : list byte) : list cell :=
  [CB 8 j288; CB 8 j296; CB 8 j304; CB 4 j312; CB 4 j316; CB 4 j320; CB 4 j324;
   C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition a1_consts (m : mem) : Prop :=
  ro_cells asegs m 1483312 [C8 (Z_to_bv 64 1522744)] /\ ro_cells asegs m 1522744 [C8 (Z_to_bv 64 2147450880)].

Definition a1_W1 (E : s1env) : list ivl :=
  [ (bv_unsigned (e_sp E) + - 432, bv_unsigned (e_sp E)); (e_THIS E, e_THIS E + 96) ]%Z.

Lemma a1_W1_sub : forall E, sub_fp (a1_W1 E) (a1_W E).
Proof. intros E x. unfold a1_W1, s1_W_g. cbn [outside]. intros (H1 & H2 & _). split; [exact H1|]. split; [exact H2| exact I]. Qed.

Definition a1_mid (E : s1env) (nsi nxt : word) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (u5 u6 u7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
         (j0 j8 j16 j24 jt j288 j296 j304 j312 j316 j320 j324 : list byte),
    ms = MS (mkR (Z_to_bv 64 A1_MEMCPY_RA) (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) u5 u6 u7 (e_s0 E) (Z_to_bv 64 0)
                 (Z_to_bv 64 (bv_unsigned (e_sp E) + -400)) (Z_to_bv 64 A1_TABLE) (Z_to_bv 64 256) x13 x14 x15 x16 x17
                 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 2147450880) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
                 (Z_to_bv 64 (e_BUF E)) (e_s11 E) x28 x29 x30 x31)
            (e_F E) (Z_to_bv 64 0x812f8) (e_fc E) None m1 (seg_rom asegs)
    /\ munch (a1_W1 E) (e_m0 E) m1 /\ wmono asegs (e_m0 E) m1 /\ mem_inv asegs m1
    /\ stk asegs m1 (e_lo E) (bv_unsigned (e_sp E) + -432)
    /\ rw_cells asegs m1 (bv_unsigned (e_sp E) + -432) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]
    /\ rw_cells asegs m1 (bv_unsigned (e_sp E) + -400) [CB 256 jt]
    /\ rw_cells asegs m1 (bv_unsigned (e_sp E) + -144) (frame_mid_a E j288 j296 j304 j312 j316 j320 j324)
    /\ rw_cells asegs m1 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E))).

Section TOP.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma a1_walk1 : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (nsi nxt bufo leno : word),
    mem_inv asegs (e_m0 E) -> a1_consts (e_m0 E) ->
    stk asegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E)) ->
    rw_cells asegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt bufo leno) ->
    evt asegs (a1_mid E nsi nxt)
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E)
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 len) (Z_to_bv 64 0) a4 a5 a6 a7
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
          (e_F E) (Z_to_bv 64 A1_ENTRY) (e_fc E) None (e_m0 E) (seg_rom asegs)).
  Proof using OK SHZ.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno MI (G1 & G2) ST PARSER.
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP, A1_ENTRY in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    assert (LO0 : (0 <= e_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl (a1_W E) (e_m0 E)) as MU. pose proof (wmono_refl asegs (e_m0 E)) as WM.
    pose proof (munch_refl (a1_W1 E) (e_m0 E)) as MUt.
    unfold s1_W_g in MU. cbn [Z.opp] in MU. unfold a1_W1 in MUt. cbn [Z.opp] in MUt. unfold parser_cells in PARSER.
    set (m := e_m0 E) in MI, G1, G2, ST, PARSER, MU at 2, MUt at 2, WM at 2 |- *.
    clearbody m.
    step.
    carve_frame 432%nat ST.
    apply (rw_cells_split_CB asegs m _ [] 432 junk [] [8;8;8;8;256;8;8;8;4;4;4;4;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    zstep. zstep. zstep. zstep. clear G1 G2. zstep.

    zstep.
    a1_shz_this SHZ (e_THIS E + 72)%Z.
    zstep. rewrite shr3_div. zstep. zstep. s1norm. zstep. if_true.
    zstep. zstep.

    zstep.
    a1_shz_this SHZ (e_THIS E + 80)%Z.
    zstep. rewrite shr3_div. zstep. zstep. s1norm. zstep. if_true.
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.

    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?ct :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: ct :: rest) with ([c0; c1; c2; c3] ++ [ct] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FRlo FR]. apply rw_cells_app in FR. destruct FR as [FRtb FRhi].
    cbn [cells_size csize Nat.add] in FRtb, FRhi.
    replace (bv_unsigned (e_sp E) + -432 + Z.of_nat 32)%Z with (bv_unsigned (e_sp E) + -400)%Z in * by lia.
    replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in * by lia.
    apply evt_done. unfold a1_mid, frame_mid_a, parser_cells, A1_MEMCPY_RA, A1_TABLE.
    do 25 eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MUt|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FRlo|]. split; [exact FRtb|]. split; [exact FRhi| exact PARSER].
  Qed.

  Theorem a1_walk2 : forall u5 u6 u7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (nsi nxt : word) (ws0 : list word)
      (j0 j8 j16 j24 j288 j296 j304 j312 j316 j320 j324 : list byte),
    mem_inv asegs (e_m0 E) ->
    stk asegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E) + -432) ->
    rw_cells asegs (e_m0 E) (bv_unsigned (e_sp E) + -432) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] ->
    rw_cells asegs (e_m0 E) (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] ->
    rw_cells asegs (e_m0 E) (bv_unsigned (e_sp E) + -144) (frame_mid_a E j288 j296 j304 j312 j316 j320 j324) ->
    rw_cells asegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz len)) ->
    u32arr asegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E ->
    bytes_at asegs (e_m0 E) (e_BUF E) (padded_bytes bs) ->
    evt asegs (a1_post E (fst (stage1 bs)) (snd (stage1 bs)))
      (MS (mkR (Z_to_bv 64 A1_MEMCPY_RA) (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) u5 u6 u7 (e_s0 E) (Z_to_bv 64 0)
               v x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 len) (Z_to_bv 64 2147450880) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
               (Z_to_bv 64 (e_BUF E)) (e_s11 E) x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 A1_MEMCPY_RA) (e_fc E) None (e_m0 E) (seg_rom asegs)).
  Proof using OK SHZ.
    intros u5 u6 u7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 nsi nxt ws0 j0 j8 j16 j24 j288 j296 j304 j312 j316 j320 j324
           MI ST FRlo FRtb FRhi PARSER IDXA IDXL BUFRO.
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP, A1_MEMCPY_RA in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    pose proof (padded_bytes_blen bs) as PBL.
    pose proof (munch_refl (a1_W E) (e_m0 E)) as MU. pose proof (wmono_refl asegs (e_m0 E)) as WM.
    unfold s1_W_g in MU. cbn [Z.opp] in MU. unfold parser_cells in PARSER. unfold frame_mid_a in FRhi.
    set (m := e_m0 E) in MI, ST, FRlo, FRtb, FRhi, PARSER, IDXA, BUFRO, MU at 2, WM at 2 |- *.
    clearbody m.
    zstep.
    zstep.
    a1_shz_this SHZ (e_THIS E + 16)%Z.
    zstep. rewrite shr3_div. zstep. zstep. s1norm. zstep. if_true.
    zstep. zstep. s1norm. zstep. zstep. zstep.
    assert (IDXF : firstn (length (@nil Z)) ws0 = map wz []) by reflexivity.
    assert (EOK0 : err_ok 0) by (left; reflexivity).
    unfold stage1, stage1_st. cbn [fst snd].
    zstep.
    if_cases KZ; zify_cond KZ.
    -
      s1_cur_mem ltac:(fun mm => assert (INV0 : A1INV E mm []) by a1_close_inv).
      zstep. zstep. zstep.
      rewrite scan_loop_S. cbn [s_idx s1_init].
      replace (0 <? len)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      replace (Z_to_bv 64 (e_IDX E)) with (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (@nil Z)))) at 2 by (f_equal; cbn; lia).
      apply (a1_tail E OK SHZ 0 SUCCESS false []); [exact INV0| cbn; lia| exact EOK0].
    - s1_cur_mem ltac:(fun mm => assert (INV0 : A1INV E mm []) by a1_close_inv).
      do 14 zstep.
      eapply evt_eq; [| eapply (a1_for E OK SHZ (S (length bs)) s1_init _ _ _ _ _ _ _ _ INV0); cbn [s_idx s_out s_err s1_init length]; unfold blen in *; try lia; exact EOK0].
      cbn [s_idx s_out s_err s_unclosed s1_init length Z.b2z]. unfold SUCCESS. s1_st_eq.
  Qed.
End TOP.
