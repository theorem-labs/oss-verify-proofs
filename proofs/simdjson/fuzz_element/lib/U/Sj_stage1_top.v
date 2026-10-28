(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage1_defs Sj_stage1_tail Sj_stage1_for.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section TOP.
  Hypothesis HMEMCPY : umemcpy_stmt.
  Variable E : s1env.
  Hypothesis OK : env_ok_u E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Theorem u1_stage1_spec : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (nsi nxt bufo leno : word) (ws0 : list word),
    mem_inv usegs (e_m0 E) ->
    stk usegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E)) ->
    rw_cells usegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt bufo leno) ->
    u32arr usegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E ->
    bytes_at usegs (e_m0 E) (e_BUF E) (padded_bytes bs) ->
    evt usegs (u1_post E (fst (stage1 bs)) (snd (stage1 bs)))
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E)
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 len) (Z_to_bv 64 0) a4 a5 a6 a7
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
          (e_F E) (Z_to_bv 64 U1_ENTRY) (e_fc E) None (e_m0 E) (seg_rom usegs)).
  Proof using HMEMCPY OK.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno ws0 MI ST PARSER IDXA IDXL BUFRO.
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP, U1_ENTRY in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blen_nonneg bs) as LEN0.
    assert (LO0 : (0 <= e_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (padded_bytes_blen bs) as PBL.
    pose proof (munch_refl (u1_W E) (e_m0 E)) as MU. pose proof (wmono_refl usegs (e_m0 E)) as WM.
    unfold s1_W_g in MU. cbn [Z.opp] in MU. unfold parser_cells in PARSER.
    set (m := e_m0 E) in MI, ST, PARSER, IDXA, BUFRO, MU at 2, WM at 2 |- *.
    clearbody m.
    step.
    carve_frame 432%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 432 junk [] [8;8;8;8;256;8;8;8;4;4;4;4;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step. do 4 step. step. step. do 6 step.
    change [CB 8 j; CB 8 j0; CB 8 j1; CB 8 j2; CB 256 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 4 j7; CB 4 j8; CB 4 j9; CB 4 j10;
            C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
            C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)]
      with ([CB 8 j; CB 8 j0; CB 8 j1; CB 8 j2] ++ [CB 256 j3] ++ [CB 8 j4; CB 8 j5; CB 8 j6; CB 4 j7; CB 4 j8; CB 4 j9; CB 4 j10;
            C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
            C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)]) in FR.
    apply rw_cells_app in FR. destruct FR as [FRlo FR]. apply rw_cells_app in FR. destruct FR as [FRtb FRhi].
    cbn [cells_size csize Nat.add] in FRtb, FRhi.
    replace (bv_unsigned (e_sp E) + -432 + Z.of_nat 32)%Z with (bv_unsigned (e_sp E) + -400)%Z in * by lia.
    replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in * by lia.
    pose proof (utable_at _ MI) as TB. unfold U1_TABLE in TB.
    pose proof HMEMCPY as HM. unfold umemcpy_stmt, memcpy_stmt_g in HM.
    eapply evt_cut.
    { eapply HM with (src := TABLE_BYTES) (junk := j3); rewrite ?unsigned_lit by lia;
      [ exact TB | reflexivity | exact FRtb | lia | exact MI ]. }
    cbv beta. intros ms' P. unfold memcpy_post_g in P.
    destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc & MIc & DSTc & SRCc).
    rewrite !unsigned_lit in MUc, DSTc by lia. change (bv_unsigned (Z_to_bv 64 256)) with 256%Z in *. change (Z.to_nat 256) with 256%nat in DSTc.
    clear TB SRCc.
    transport_after_call usegs m0 m3 MUc WMc.
    clear MUc WMc MI HM. clear m0.
    replace (ret_pc (Z_to_bv 64 268948)) with (Z_to_bv 64 268948) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. s1norm. do 7 zstep. zstep.
    assert (IDXF : firstn (length (@nil Z)) ws0 = map wz []) by reflexivity.
    assert (INV0 : U1INV E m [] 0 0) by u1_close_inv.
    assert (EOK0 : err_ok 0) by (left; reflexivity).
    unfold stage1, stage1_st. cbn [fst snd].
    if_cases KZ; zify_cond KZ.
    -
      zstep. zstep. zstep.
      rewrite scan_loop_S. cbn [s_idx s1_init].
      replace (0 <? len)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      eapply evt_eq; [| eapply (u1_tail E OK 0 SUCCESS false [] 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m INV0)];
        [cbn [length Z.b2z]; s1_st_eq| cbn; lia| exact EOK0].
    - zstep. if_cases KB; zify_cond KB; [|exfalso; lia].
      do 19 zstep. s1norm.
      rewrite !lxor_ones64 by lia.
      eapply evt_eq; [| eapply (u1_for E OK (S (length bs)) s1_init _ _ _ _ _ m INV0)];
        [cbn [s_idx s_out s_err s_unclosed s1_init length Z.b2z]; unfold SUCCESS; s1_st_eq
        | cbn [s_idx s_out s_err s1_init length]; unfold blen in *; try lia; try exact EOK0 ..].
  Qed.
End TOP.
