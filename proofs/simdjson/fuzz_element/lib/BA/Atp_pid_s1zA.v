(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage1_defs Sj_stage1_tail Sj_stage1_top Sj_stage1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Record env_okz (E : s1env) : Prop := mkEnvOkz {
  okz_nil : e_bs E = [];
  okz_glo : (A1_GTOP <= e_lo E)%Z;
  okz_room : (e_lo E + A1_STACK <= bv_unsigned (e_sp E))%Z;
  okz_this : (0 <= e_THIS E /\ e_THIS E + 96 <= e_lo E)%Z;
  okz_idx : (0 <= e_IDX E /\ e_IDX E + 4 * Z.of_nat (e_cap E) <= e_lo E)%Z;
  okz_cap : (3 <= Z.of_nat (e_cap E))%Z;
  okz_this_idx : (e_THIS E + 96 <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (e_cap E) <= e_THIS E)%Z
}.

Definition a1z_shz (E : s1env) : Prop :=
  forall m' : mem, munch (a1_W E) (e_m0 E) m' -> wmono asegs (e_m0 E) m' ->
    shz m' (e_THIS E) 96 /\ shz m' (e_IDX E) (4 * (e_len E + 3)) /\ True.

Definition a1z_post (E : s1env) (code : Z) (out : list Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : mem) (ws' : list word) (nxt' : word),
    ms' = MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E) (wz code) a1 a2 a3 a4 a5 a6 a7
                  (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
             (e_F E) (ret_pc (e_ra E)) (e_fc E) None m' (seg_rom asegs)
    /\ munch (a1_W E) (e_m0 E) m' /\ wmono asegs (e_m0 E) m' /\ mem_inv asegs m'
    /\ stk asegs m' (e_lo E) (bv_unsigned (e_sp E))
    /\ rw_cells asegs m' (e_THIS E) (parser_cells E (wz (Z.of_nat (length out))) nxt' (wz (e_BUF E)) (wz (e_len E)))
    /\ (code <> 13%Z -> nxt' = wz 0)
    /\ u32arr asegs m' (e_IDX E) ws' /\ length ws' = e_cap E
    /\ firstn (length out + 3) ws' = map wz (out ++ [e_len E; e_len E; 0%Z]).

Section S1Z.
  Variable E : s1env.
  Hypothesis OK : env_okz E.
  Hypothesis SHZ : a1z_shz E.

  Hypothesis IDXG : (0 < e_IDX E)%Z /\ (e_IDX E mod 4 = 0)%Z.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma a1z_walk1 : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (nsi nxt bufo leno : word),
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
    destruct OK' as [NIL GLO ROOM [TH0 TH1] [IX0 IX1] CAPOK S_TI].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP, A1_ENTRY in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LZ : len = 0%Z) by (rewrite NIL; reflexivity).
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

  Theorem a1z_walk2 : forall u5 u6 u7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (nsi nxt : word) (ws0 : list word)
      (j0 j8 j16 j24 j288 j296 j304 j312 j316 j320 j324 : list byte),
    mem_inv asegs (e_m0 E) ->
    stk asegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E) + -432) ->
    rw_cells asegs (e_m0 E) (bv_unsigned (e_sp E) + -432) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] ->
    rw_cells asegs (e_m0 E) (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] ->
    rw_cells asegs (e_m0 E) (bv_unsigned (e_sp E) + -144) (frame_mid_a E j288 j296 j304 j312 j316 j320 j324) ->
    rw_cells asegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz len)) ->
    u32arr asegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E ->
    evt asegs (a1z_post E 13 [])
      (MS (mkR (Z_to_bv 64 A1_MEMCPY_RA) (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) u5 u6 u7 (e_s0 E) (Z_to_bv 64 0)
               v x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 len) (Z_to_bv 64 2147450880) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
               (Z_to_bv 64 (e_BUF E)) (e_s11 E) x28 x29 x30 x31)
          (e_F E) (Z_to_bv 64 A1_MEMCPY_RA) (e_fc E) None (e_m0 E) (seg_rom asegs)).
  Proof using OK SHZ IDXG.
    intros u5 u6 u7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 nsi nxt ws0 j0 j8 j16 j24 j288 j296 j304 j312 j316 j320 j324
           MI ST FRlo FRtb FRhi PARSER IDXA IDXL.
    pose proof OK as OK'.
    destruct OK' as [NIL GLO ROOM [TH0 TH1] [IX0 IX1] CAPOK S_TI].
    destruct IDXG as [IDXP ALIGN].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP, A1_MEMCPY_RA in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LZ : len = 0%Z) by (rewrite NIL; reflexivity).
    pose proof (munch_refl (a1_W E) (e_m0 E)) as MU. pose proof (wmono_refl asegs (e_m0 E)) as WM.
    unfold s1_W_g in MU. cbn [Z.opp] in MU. unfold parser_cells in PARSER. unfold frame_mid_a in FRhi.
    unfold wz in PARSER.
    set (m := e_m0 E) in MI, ST, FRlo, FRtb, FRhi, PARSER, IDXA, MU at 2, WM at 2 |- *.
    clearbody m.
    zstep.
    zstep.
    a1_shz_this SHZ (e_THIS E + 16)%Z.
    zstep. rewrite shr3_div. zstep. zstep. s1norm. zstep. if_true.
    zstep. zstep. s1norm. zstep. zstep. zstep.
    zstep.
    if_cases KZ; zify_cond KZ; [| exfalso; lia].

    zstep. zstep. zstep.

    zstep.
    a1_shz_idx SHZ (e_IDX E)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true.

    s1_cur_mem ltac:(fun mm => pose proof (u32arr_store_ok asegs mm (e_IDX E) ws0 0 (wa (e_IDX E)) IDXA ltac:(lia) ltac:(f_equal; lia)) as SOK).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u32arr_write asegs mm (e_IDX E) ws0 0 (Z_to_bv 64 len) IDXA ltac:(lia)) as IDXA1;
      replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in IDXA1 by lia end.
    store_done.
    zstep.
    a1_shz_idx SHZ (e_IDX E + 4)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8.
    step. unfold wz. rewrite (sx32_small len) by lia.
    zstep. if_true.

    s1_cur_mem ltac:(fun mm => pose proof (u32arr_store_ok asegs mm (e_IDX E) _ 1 (wa (e_IDX E + 4)) IDXA1 ltac:(rewrite upd_length; lia) ltac:(f_equal; lia)) as SOK1).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u32arr_write asegs mm (e_IDX E) _ 1 (Z_to_bv 64 len) IDXA1 ltac:(rewrite upd_length; lia)) as IDXA2;
      replace (e_IDX E + 4 * 1)%Z with (e_IDX E + 4)%Z in IDXA2 by lia end.
    store_done.
    zstep.
    a1_shz_idx SHZ (e_IDX E + 8)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true.

    s1_cur_mem ltac:(fun mm => pose proof (u32arr_store_ok asegs mm (e_IDX E) _ 2 (wa (e_IDX E + 8)) IDXA2 ltac:(rewrite !upd_length; lia) ltac:(f_equal; lia)) as SOK2).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u32arr_write asegs mm (e_IDX E) _ 2 (Z_to_bv 64 0) IDXA2 ltac:(rewrite !upd_length; lia)) as IDXA3;
      replace (e_IDX E + 4 * 2)%Z with (e_IDX E + 8)%Z in IDXA3 by lia end.
    store_done.
    assert (IDXF3 : firstn (length (@nil Z) + 3) (upd (upd (upd ws0 (Z.to_nat 0) (Z_to_bv 64 len)) (Z.to_nat 1) (Z_to_bv 64 len)) (Z.to_nat 2) (Z_to_bv 64 0))
                    = map wz ([] ++ [len; len; 0%Z])).
    { change (Z.to_nat 0) with (length (@nil Z)). change (Z.to_nat 1) with (length (@nil Z) + 1)%nat.
      change (Z.to_nat 2) with (length (@nil Z) + 2)%nat. apply arr_push3; [reflexivity| cbn; lia]. }
    assert (IDXL3 : length (upd (upd (upd ws0 (Z.to_nat 0) (Z_to_bv 64 len)) (Z.to_nat 1) (Z_to_bv 64 len)) (Z.to_nat 2) (Z_to_bv 64 0)) = e_cap E)
      by (rewrite !upd_length; exact IDXL).

    zstep.
    a1_shz_this SHZ (e_THIS E + 8)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true.
    zstep. zstep. replace (e_IDX E - e_IDX E)%Z with 0%Z by lia. change (Z.shiftr 0 2) with 0%Z. zstep. s1norm. zstep. zstep. zstep.
    if_cases KN; zify_cond KN; [exfalso; lia|].

    zstep.

    s1_cur_mem ltac:(fun mm =>
      pose proof (stk_release asegs mm _ _ _ ST FRlo ltac:(lia)) as ST1;
      cbn [cells_size csize Nat.add] in ST1;
      replace (bv_unsigned (e_sp E) + -432 + Z.of_nat 32)%Z with (bv_unsigned (e_sp E) + -400)%Z in ST1 by lia;
      pose proof (stk_release asegs mm _ _ _ ST1 FRtb ltac:(lia)) as ST2;
      cbn [cells_size csize Nat.add] in ST2;
      replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in ST2 by lia;
      pose proof (stk_release asegs mm _ _ _ ST2 FRhi ltac:(lia)) as ST3;
      cbn [cells_size csize Nat.add] in ST3;
      replace (bv_unsigned (e_sp E) + -144 + Z.of_nat 144)%Z with (bv_unsigned (e_sp E))%Z in ST3 by lia).

    lazymatch type of FRhi with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with ([c0; c1; c2; c3; c4; c5; c6] ++ rest) in FRhi end.
    apply rw_cells_app in FRhi. destruct FRhi as [_ FRsv].
    cbn [cells_size csize Nat.add] in FRsv.
    replace (bv_unsigned (e_sp E) + -144 + Z.of_nat 40)%Z with (bv_unsigned (e_sp E) + -104)%Z in FRsv by lia.
    zstep. do 13 zstep. zstep. zstep.
    s1_cur_mem ltac:(fun mm => apply evt_done; unfold a1z_post; do 14 eexists; exists mm; eexists _, nxt).
    split; [cbv delta [mkR]; reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ST3|].
    split; [unfold parser_cells; cbn [length Z.of_nat]; unfold wz; eassumption|].
    split; [intros X; exfalso; apply X; reflexivity|].
    split; [exact IDXA3|]. split; [exact IDXL3|]. cbn [length Nat.add app] in IDXF3 |- *. exact IDXF3.
  Qed.
End S1Z.

Definition a1z_res (E : s1env) (m' : mem) : Prop :=
  exists (ws' : list word) (nxt' : word),
    rw_cells asegs m' (e_THIS E) (parser_cells E (wz 0) nxt' (wz (e_BUF E)) (wz (e_len E)))
    /\ u32arr asegs m' (e_IDX E) ws' /\ length ws' = e_cap E
    /\ firstn 3 ws' = map wz [e_len E; e_len E; 0].

Section Stage1zCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCP : memcpy_icontract_f RT e_asan_memcpy.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, A1_GTOP, A1_STACK, S1_LEN_MAX in *; lia.

Definition a1z_live (Σ : rts RT) (E : s1env) : Prop :=
  In (e_THIS E, 96) (rt_live RT Σ) /\ In (e_IDX E, 4 * Z.of_nat (e_cap E)) (rt_live RT Σ)
  /\ e_THIS E mod 8 = 0 /\ e_IDX E mod 8 = 0 /\ e_len E + 4 <= Z.of_nat (e_cap E).

Lemma a1z_art_step : forall Σ (E : s1env) (m m' : mem), a1z_live Σ E -> ART RT Σ m ->
  rt_sp0 RT Σ - STACK_WIN <= bv_unsigned (e_sp E) - 448 -> bv_unsigned (e_sp E) <= USTACK_TOP ->
  munch (a1_W E) m m' -> wmono asegs m m' -> ART RT Σ m'.
Proof using AF.
  intros Σ E m m' (INT & INI & _) HA SPLO SPHI MU WM.
  apply (art_client_write RT AF Σ m m' (bv_unsigned (e_sp E) - 448) HA SPLO); [| exact WM].
  intros a Ha. apply MU. unfold s1_W_g. cbn [outside].
  split; [intros Hin; apply Ha; left; lia|].
  split; [intros Hin; apply Ha; right; right; left; exists (e_THIS E), 96; split; [exact INT| lia]|].
  split; [intros Hin; apply Ha; right; right; left; exists (e_IDX E), (4 * Z.of_nat (e_cap E)); split; [exact INI| lia]| exact I].
Qed.

Lemma a1z_shz_art : forall Σ (E : s1env), a1z_live Σ E -> ART RT Σ (e_m0 E) ->
  rt_sp0 RT Σ - STACK_WIN <= bv_unsigned (e_sp E) - 448 -> bv_unsigned (e_sp E) <= USTACK_TOP -> 0 <= e_len E -> a1z_shz E.
Proof using AF.
  intros Σ E LV HA SPLO SPHI LEN0 m' MU WM.
  pose proof (a1z_art_step Σ E _ m' LV HA SPLO SPHI MU WM) as HA'.
  destruct LV as (INT & INI & T8 & I8 & CAP4).
  split; [| split; [| exact I]].
  - eapply shz_sub; [exact (shz_live RT AF Σ m' _ _ HA' INT T8)| lia|]. change (96 / 8) with 12. lia.
  - eapply shz_sub; [exact (shz_live RT AF Σ m' _ _ HA' INI I8)| lia|].
    pose proof (Z.div_mod (4 * Z.of_nat (e_cap E)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (4 * Z.of_nat (e_cap E)) 8 ltac:(lia)). lia.
Qed.

Lemma a1z_idxg : forall Σ (E : s1env) m, a1z_live Σ E -> ART RT Σ m -> (0 < e_IDX E)%Z /\ (e_IDX E mod 4 = 0)%Z.
Proof using AF.
  intros Σ E m (INT & INI & T8 & I8 & CAP4) HA.
  pose proof (af_live_range RT AF Σ m _ _ HA INI) as (I0 & _).
  split; [exact I0|].
  pose proof (Z.div_mod (e_IDX E) 8 ltac:(lia)) as D. rewrite I8 in D.
  replace (e_IDX E) with ((2 * (e_IDX E / 8)) * 4) by lia. apply Z.mod_mul. lia.
Qed.

Definition stage1z_cps : Prop :=
  forall (Σ : rts RT) PMc (E : s1env) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno : word) (ws0 : list word),
  fdfs_only PMc -> mat_stable PMc ->
  env_okz E -> a1z_live Σ E ->
  rt_sp0 RT Σ - STACK_WIN <= e_lo E -> e_lo E + 448 + RT_STACK <= bv_unsigned (e_sp E) ->
  bv_unsigned (e_sp E) + 16 <= USTACK_TOP -> bv_unsigned (e_sp E) mod 16 = 0 ->
  ART RT Σ (e_m0 E) -> mem_inv asegs (e_m0 E) -> stk asegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E)) ->
  rw_cells asegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt bufo leno) ->
  u32arr asegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E -> frm0 (e_fc E) ->
  cps_f
    (ASTA RT Σ PMc (eq (entry_st (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E)
                          (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 0) a4 a5 a6 a7
                          (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E)
                          t3 t4 t5 t6 (e_F E) (e_fc E) A1_ENTRY (e_m0 E))))
    (ASTA RT Σ PMc (fun ms => exists m',
        ret_st (e_ra E) (e_sp E) (e_gp E) (e_tp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E)
               (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) (Z_to_bv 64 13) m' ms
        /\ frm0 (ms_fcsr ms) /\ rt_after RT Σ (bv_unsigned (e_sp E)) (e_lo E) (e_m0 E) m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (e_sp E)) (a1_FP E) (e_m0 E) m'
        /\ a1z_res E m')).

Theorem stage1z_ok : stage1z_cps.
Proof using AF MCP.
  intros Σ PMc E t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno ws0 FDO MST OK LV LOW LOR SPT SPA ART0 MI0 ST0 PARSER0 IDXA0 IDXL FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ _ ART0) as SP0R. pose proof (af_sp0_win RT AF Σ _ ART0) as SP0W.
  pose proof OK as OK'. destruct OK' as [NIL GLO ROOM [TH0 TH1] [IX0 IX1] CAPOK S_TI].
  assert (LEN0 : 0 <= e_len E) by (unfold blen; lia).
  set (usp := bv_unsigned (e_sp E)) in *.
  pose proof (af_client_consts RT AF Σ _ ART0) as (G1 & G2 & _).
  pose proof (a1z_shz_art Σ E LV ART0 ltac:(ul) ltac:(ul) LEN0) as SHZ0.
  pose proof (a1z_idxg Σ E _ LV ART0) as IDXG.

  pose proof (a1z_walk1 E OK SHZ0 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno MI0 (conj G1 G2) ST0 PARSER0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & MID & Hc1'). clear Hc1.
  destruct MID as (m1 & u5 & u6 & u7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31
                   & j0 & j8 & j16 & j24 & jt & j288 & j296 & j304 & j312 & j316 & j320 & j324
                   & -> & MU1 & WM1 & MI1 & ST1 & FRlo1 & FRtb1 & FRhi1 & PARSER1).
  fold usp in MU1, ST1, FRlo1, FRtb1, FRhi1, Hc1'.
  pose proof (a1z_art_step Σ E _ m1 LV ART0 ltac:(ul) ltac:(ul) (munch_weaken _ _ _ _ (a1_W1_sub E) MU1) WM1) as ART1.
  pose proof LV as (INT & INI & T8 & I8 & CAP4).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -432)) = usp + -432) by (apply unsigned_lit; ul).

  apply (MCP Σ PMc (Z_to_bv 64 A1_MEMCPY_RA) (Z_to_bv 64 (usp + -432)) (e_gp E) (e_tp E) u5 u6 u7 (e_s0 E) (Z_to_bv 64 0)
           (Z_to_bv 64 (usp + -400)) (Z_to_bv 64 A1_TABLE) (Z_to_bv 64 256) x13 x14 x15 x16 x17
           (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 2147450880) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
           (Z_to_bv 64 (e_BUF E)) (e_s11 E) x28 x29 x30 x31 (e_F E) (e_fc E) m1 (usp + -400) A1_TABLE TABLE_BYTES (e_lo E) FDO MST);
    try reflexivity; try assumption; [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - ul.
  - unfold A1_TABLE. lia.
  - apply table_at_a. exact MI1.
  - change (Z.of_nat (length TABLE_BYTES)) with 256. split.
    + intros _. split.
      * apply (acc_lit RT AF Σ m1 _ _ ART1). unfold A1_TABLE, ACC_LITS. repeat (first [left; reflexivity | right]).
      * right; right; right. unfold A1_TABLE, SEGTOP_A. lia.
    + left. unfold A1_TABLE. ul.
  - change (Z.of_nat (length TABLE_BYTES)) with 256. unfold checked_dst. rewrite EU2. split; [| split].
    + intros _. split; [apply (af_acc_stack RT AF Σ m1 _ _ ART1); ul|]. right; right; left. ul.
    + intros i Hi. left. ul.
    + exact (rw_cells_wr_at asegs m1 _ _ 256 FRtb1 ltac:(cbn; lia)).
  - right. change (Z.of_nat (length TABLE_BYTES)) with 256. unfold A1_TABLE. ul.
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -432) with (usp + (-27) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c2 (Hc2 & FC2). unfold icpt_post in Hc2.
    destruct (ASTA_unpack_f RT Σ _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BS2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (w5 & w6 & w7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. change (Z.of_nat (length TABLE_BYTES)) with 256 in PRES2.
    unfold A1_MEMCPY_RA in Hc2'. rewrite (ret_pc_even 0xba3c4) in Hc2' by lia.

    assert (STK2 : forall x, usp + -432 <= x < usp -> ~ (usp + -400 <= x < usp + -400 + 256) ->
                     aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -432) x /\ ~ (usp + -400 <= x < usp + -400 + 256))
      by (intros x Hx Hn; split; [left; ul| exact Hn]).
    assert (LIV2 : forall p n x, In (p, n) (rt_live RT Σ) -> p + n <= e_lo E -> p <= x < p + n ->
                     aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -432) x /\ ~ (usp + -400 <= x < usp + -400 + 256))
      by (intros p n x Hin Hlo Hx; split; [right; right; left; exists p, n; split; [exact Hin| exact Hx]| ul]).
    assert (FRlo2 : rw_cells asegs m2 (usp + -432) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FRlo1); [| exact WM2]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply STK2; lia. }
    assert (FRhi2 : rw_cells asegs m2 (usp + -144) (frame_mid_a E j288 j296 j304 j312 j316 j320 j324)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FRhi1); [| exact WM2]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold frame_mid_a in Hx. cbn [cells_size csize Nat.add] in Hx. apply STK2; lia. }
    assert (FRtb2 : rw_cells asegs m2 (usp + -400) [CB 256 TABLE_BYTES]).
    { apply (rw_cells_CB_intro m2 _ TABLE_BYTES BS2).
      apply (wr_at_transport asegs m1 m2 _ _ (rw_cells_wr_at asegs m1 _ _ 256 FRtb1 ltac:(cbn; lia)) WM2). }
    assert (PARSER2 : rw_cells asegs m2 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E)))).
    { apply (rw_cells_agree asegs m1 m2 _ _ PARSER1); [| exact WM2]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold parser_cells in Hx. cbn [cells_size csize Nat.add] in Hx. apply (LIV2 _ _ x INT); lia. }
    assert (AG01 : agree_on (fun x => ~ (usp + -432 <= x < usp) /\ ~ (e_THIS E <= x < e_THIS E + 96)) (e_m0 E) m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x [H1 H2]. unfold a1_W1. cbn [outside]. fold usp.
      split; [lia|]. split; [exact H2| exact I]. }
    assert (IDXA2 : u32arr asegs m2 (e_IDX E) ws0).
    { apply (u32arr_agree m1 m2); [| | exact WM2].
      + apply (u32arr_agree (e_m0 E) m1 _ _ IDXA0); [| exact WM1]. eapply agree_sub; [exact AG01|].
        intros x Hx. cbv beta in *. rewrite IDXL in Hx. split; [ul| destruct S_TI; lia].
      + apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. cbv beta in Hx. rewrite IDXL in Hx. apply (LIV2 _ _ x INI); lia. }

    set (E2 := env_at E F2 fc2 m2).
    assert (OK2 : env_okz E2) by (destruct OK; constructor; assumption).
    assert (LV2 : a1z_live Σ E2) by exact LV.
    assert (SHZ2 : a1z_shz E2) by (apply (a1z_shz_art Σ E2 LV2 ART2); [change (bv_unsigned (e_sp E2)) with usp; ul| change (bv_unsigned (e_sp E2)) with usp; ul| exact LEN0]).
    pose proof (a1z_walk2 E2 OK2 SHZ2 IDXG w5 w6 w7 (Z_to_bv 64 (usp + -400)) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 nsi nxt ws0
                  j0 j8 j16 j24 j288 j296 j304 j312 j316 j320 j324 MI2 ST2 FRlo2 FRtb2 FRhi2 PARSER2 IDXA2 IDXL) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3); intros ms POST; unfold a1z_post in POST;
                         destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _); exact FRM2].
    eapply ASTA_conseq; [exact Hc3|]. intros ms POST.
    unfold a1z_post in POST.
    destruct POST as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m' & ws' & nxt'
                      & -> & MU3 & WM3 & MI3 & ST3 & PARSER3 & NXT3 & IDXA3 & IDXL3 & IDXF3).
    change (e_m0 E2) with m2 in MU3, WM3. change (bv_unsigned (e_sp E2)) with usp in ST3.
    exists m'. split; [| split; [exact FRM2| split; [| split]]].
    + unfold ret_st. do 16 eexists. reflexivity.
    + split; [| split; [exact MI3| split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))| exact ST3]]].
      apply (a1z_art_step Σ E2 m2 m' LV2 ART2); [change (bv_unsigned (e_sp E2)) with usp; ul| change (bv_unsigned (e_sp E2)) with usp; ul| exact MU3| exact WM3].
    + intros a Ha Hout. unfold a1_FP in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & _).
      pose proof (aclient_split_c RT AF Σ _ usp (bv_unsigned a) ART0 Ha) as SPL.
      assert (NFR : ~ (usp + -432 <= bv_unsigned a < usp)) by ul.
      rewrite (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
      * unfold a1_W1. cbn [outside]. fold usp. split; [lia|]. split; [exact HO1| exact I].
      * apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
      * lia.
      * unfold s1_W_g. cbn [outside]. change (bv_unsigned (e_sp E2)) with usp. change (e_THIS E2) with (e_THIS E).
        change (e_IDX E2) with (e_IDX E). change (e_cap E2) with (e_cap E).
        split; [lia|]. split; [exact HO1|]. split; [exact HO2| exact I].
    + exists ws', nxt'. split; [exact PARSER3|]. split; [exact IDXA3|]. split; [exact IDXL3|].
      cbn [length Nat.add app] in IDXF3. change (e_len E2) with (e_len E) in IDXF3. exact IDXF3.
Qed.

End Stage1zCPS.
