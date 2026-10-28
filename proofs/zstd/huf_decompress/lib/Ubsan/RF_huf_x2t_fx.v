(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk
  RF_huf_bdt_model RF_huf_x1t_model RF_huf_x2t_model RF_huf_x2t_c1 RF_huf_x2t_kit_fill RF_huf_x2t_skc RF_huf_x2t_lv2
  RF_huf_x2t_gen RF_huf_x2t_fxb RF_huf_x2t_fxc.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Step MState.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
  ?omerge_length, ?ox2_length, ?upd_bytes_length in *.

Lemma fx_mulhu52 : forall k, 0 <= k < 2^31 -> ((k ≪ 32) mod 18446744073709551616 * 223338299392) ≫ 64 = 52 * k.
Proof.
  intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
  replace (k * 4294967296 * 223338299392) with (52 * k * 18446744073709551616) by lia.
  apply Z.div_mul. lia.
Qed.

Local Ltac fpn U :=
  repeat match type of U with
         | context [Z.lxor ?o 9223372036854775808 <? 9223372036854775808] => rewrite (gn_lx63 o) in U by lia
         end;
  repeat match type of U with
         | context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b)) in U by (rewrite ?Z.mod_small by lia; lia)
         end;
  cbn in U.

Local Ltac fck U := exfalso; rewrite ?gn_shl2 in U; rewrite ?signed_small2 in U by lia;
  rewrite ?fx_mulhu52 in U by lia; rewrite ?zx32_small2 in U by lia; rewrite ?unsigned_lit in U by lia;
  rewrite ?gn_shl2 in U;
  first [ (match type of U with context [Z.lxor] => idtac end; fpn U; first [discriminate | lia])
        | lia | (rewrite ?Z.mod_small in U by lia; lia) | (cbn in U; first [discriminate | lia]) ].

Local Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : stk segs m ?lo2 ?hi2 |- _ =>
      first [ apply (stk_write segs m lo2 hi2 a bs) in H; [ | lia | simpl_sizes; simpl_arr_sizes; lia ]
            | clear H ]
  end.

Local Ltac rdw RS RVA RVE w rs0 rv WK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let R1 := fresh "RD" in let R2 := fresh "RD" in let R3 := fresh "RD" in
    try (match goal with H : u32arr usegs mc (WK + 676) _ |- _ =>
    pose proof (u32arr_read usegs mc (WK + 676) _ w _ (wa (WK + 676 + 4 * w)) H
                  (nth_map_Znth2 rs0 w ltac:(lia)) ltac:(lia) eq_refl) as R1 end);
    try (match goal with H : u32arr usegs mc (WK + 676) _ |- _ =>
    pose proof (u32arr_read usegs mc (WK + 676) _ (w + 1) _ (wa (WK + 676 + 4 * (w + 1))) H
                  (nth_map_Znth2 rs0 (w + 1) ltac:(lia)) ltac:(lia) eq_refl) as R2 end);
    try (match goal with H : u32arr usegs mc WK ?ws |- _ =>
    assert (R3 : ov_read_bytes usegs mc (wa (WK + 4 * w)) 4 = Some (le4 (Z_to_bv 64 (Znth w rv))))
      by (eapply (u32arr_read usegs mc WK ws w); [exact H | | lia | reflexivity];
          rewrite <- (RVE w) by (first [assumption | lia]); apply nth_error_nth'; lia) end)
  end.

Lemma fx_zx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Local Ltac xnorm := repeat (first [ rewrite fx_zx32_small by lia | rewrite sx32_small by lia | rewrite unsigned_lit by lia
                                  | rewrite swrap32_small by lia | rewrite zb_lxor_ones by lia | rewrite Z.add_0_r ]).

Local Ltac dec_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  tryif (match c with context [?v] => is_var v end) then fail else
  let b := eval vm_compute in c in change c with b; cbv iota end.

Local Ltac fgo stops RS RVA RVE w rs0 rv WK := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (fun o => Z.eqb pc (PHUF_RDT_X2 + o)) stops) in
      lazymatch b with false => first [ zstep | rdw RS RVA RVE w rs0 rv WK; zstep ] end
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      xnorm; rewrite ?gn_shl2;
      first [ dec_if
            | let d := eval vm_compute in ((a - PHUF_RDT_X2 =? 388) || (b - PHUF_RDT_X2 =? 388))%bool in
              lazymatch d with true =>
                first [ let d2 := eval vm_compute in (a - PHUF_RDT_X2 =? 388) in lazymatch d2 with true =>
                          let U := fresh "U" in if_cases U; zify_cond U; [ fck U | ] end
                      | let U := fresh "U" in if_cases U; zify_cond U; [ | fck U ]
                      | fail 2 ] end
            | let U := fresh "B" in if_cases U; zify_cond U; try (rewrite ?Z.mod_small in U by lia); try (exfalso; lia) ]
  end).


Definition x2_frame (DT WK T nbb wEnd w : Z)
    (p80 q136 q144 q152 q160 q176 q184 q192 q200 q208 q216 q224 q240 q248 q264 q272 : word) (j : list byte) : list cell :=
  [C8 (Z_to_bv 64 wEnd); C8 (Z_to_bv 64 (nbb - T)); C8 (Z_to_bv 64 223338299392); C8 (Z_to_bv 64 (- (DT + 4) - 1)); C8 p80;
   C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (nbb - wEnd + 1)); C8 (Z_to_bv 64 nbb); C8 (Z_to_bv 64 WK);
   C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 (WK + 676)); C8 q136; C8 q144; C8 q152; C8 q160;
   C8 (Z_to_bv 64 (2 * nbb - w)); C8 q176; C8 q184; C8 q192; C8 q200; C8 q208; C8 q216; C8 q224;
   C8 (Z_to_bv 64 (DT + 4)); C8 q240; C8 q248; C8 (Z_to_bv 64 (wEnd - 1)); C8 q264; C8 q272; CB 8 j].

Definition x2A_inv (m m1 : fmem) (sp : word) (DT SY WK T nbb wEnd lo : Z) (js jt : list byte) (sorted : list (option Z))
    (ncells : nat) (p80 : word) (w : Z) (dt : list (option deltX2)) : Prop :=
  u8arr usegs m1 (DT + 4) (ox2 jt dt) /\ length dt = ncells
  /\ bytes_at usegs m1 SY (omerge js sorted)
  /\ (exists q136 q144 q152 q160 q176 q184 q192 q200 q208 q216 q224 q240 q248 q264 q272 j,
        rw_cells usegs m1 (bv_unsigned sp + 48)
          (x2_frame DT WK T nbb wEnd w p80 q136 q144 q152 q160 q176 q184 q192 q200 q208 q216 q224 q240 q248 q264 q272 j))
  /\ stk usegs m1 lo (bv_unsigned sp)
  /\ munch [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, bv_unsigned sp); (bv_unsigned sp + 136, bv_unsigned sp + 288)] m m1
  /\ wmono usegs m m1 /\ mem_inv usegs m1.

Section FX.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT SY WK T nbb wEnd lo : Z) (sorted : list (option Z)) (js jt : list byte) (ncells : nat)
    (rs0 rv : list Z) (p80 : word).
  Variable POST : machine_state -> Prop.
  Notation SP := (bv_unsigned sp).
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis HDT2 : DT mod 2 = 0.
  Hypothesis HNC : Z.of_nat ncells <= 4096.
  Hypothesis HSYE : SY = WK + 736.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= WK \/ WK + 2124 <= DT + 4.
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ WK + 2124 <= lo /\ lo <= SP - 48 /\ SP + 400 <= 2^47.
  Hypothesis HT : 1 <= T <= 12.
  Hypothesis HNBB : 2 <= nbb <= 13.
  Hypothesis HWE : 2 <= wEnd <= nbb.
  Hypothesis HTT : nbb - 1 <= T.
  Hypothesis LRS : length rs0 = 15%nat.
  Hypothesis HRSV : forall w, 1 <= w <= wEnd - 1 -> 0 <= Znth w rs0 <= Znth (w + 1) rs0 /\ Znth (w + 1) rs0 <= 256.
  Hypothesis LRV : length rv = 156%nat.
  Variable PRV : Z -> Prop.
  Hypothesis HPRV0 : forall w, 1 <= w <= wEnd - 1 -> PRV w.
  Hypothesis HPRVC : forall c w2, nbb - wEnd + 1 <= c <= T - (nbb - wEnd + 1) -> 1 <= w2 <= wEnd - 1 -> PRV (rv_idx c w2).
  Hypothesis HRV0 : forall w, 1 <= w <= wEnd - 1 ->
    0 <= Znth w rv /\ Znth w rv + 2 ^ (T - (nbb - w)) * (Znth (w + 1) rs0 - Znth w rs0) <= 4096.
  Hypothesis HRVC : forall c w2, nbb - wEnd + 1 <= c <= T - (nbb - wEnd + 1) -> 1 <= w2 <= wEnd - 1 ->
    0 <= Znth (rv_idx c w2) rv < 2^31.
  Hypothesis RSA0 : u32arr usegs m (WK + 676) (map (Z_to_bv 64) rs0).
  Hypothesis RVA0 : rv_at m WK rv PRV.
  Notation AINV m1 dt w := (x2A_inv m m1 sp DT SY WK T nbb wEnd lo js jt sorted ncells p80 w dt).

  Definition fx_loop_stmt : Prop :=
    forall f w dt m1 r (x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 : word),
    fill_x2 f dt w wEnd T rv sorted rs0 nbb = Ok r -> wEnd - w < Z.of_nat f -> 1 <= w < wEnd -> AINV m1 dt w ->
    (forall m2 dt' (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30
                    y31 : word),
       r = dt' -> AINV m2 dt' wEnd ->
       evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22
                               y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X2 + 2000)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp x5 x6 x7 x8 (Z_to_bv 64 T) x10 (Z_to_bv 64 (nbb - w + (nbb - T)))
                            (Z_to_bv 64 w) x13 x14 x15 x16 x17 (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) x20 x21 x22
                            (Z_to_bv 64 (- (WK + 676) - 1)) x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (nbb - w)))
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 1012)) fc None m1 (seg_rom usegs)).

  Lemma fx_loop_core : fx_two_stmt sp gp tp F fc m DT SY WK T nbb wEnd lo sorted js jt ncells rs0 rv p80 POST ->
    fx_latch_stmt sp gp tp F fc m DT SY WK T nbb wEnd lo sorted js jt ncells p80 POST ->
    fx_loop_stmt.
  Proof.
    intros FXT FXL. unfold fx_two_stmt, x2b_frame in FXT. unfold fx_latch_stmt, x2c_frame in FXL. unfold fx_loop_stmt.
    induction f as [|f IH]; intros w dt m1 r x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30
      HF Hf Hw INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & (q136 & q144 & q152 & q160 & q176 & q184 & q192 & q200 & q208 & q216 & q224 & q240 &
                     q248 & q264 & q272 & j & FR) & STK & MU & WM & MI).
    unfold x2_frame in FR.
    rewrite fx2_step in HF by lia.
    apply bind_Ok_inv in HF as (b & L1 & HF). apply load_Ok in L1 as (L1 & ->).
    apply bind_Ok_inv in HF as (e & L2 & HF). apply load_Ok in L2 as (L2 & ->).
    apply bind_Ok_inv in HF as (dt1 & HD & HF).
    destruct (HRSV w ltac:(lia)) as (RB1 & RB2).
    pose proof (u32arr_transport usegs _ m m1 _ _ RSA0 MU WM
                  ltac:(rewrite length_map, LRS; cbn; lia)) as RS1.
    pose proof (rv_at_transport _ m m1 WK rv PRV RVA0 MU WM ltac:(cbn; lia)) as RV1.
    destruct RV1 as (rvw & LRW & RVA & RVE).
    pose proof (HRV0 w ltac:(lia)) as RV0w.
    assert (RVW : 0 <= Znth w rv <= 4096).
    { destruct RV0w as (RA & RB). split; [exact RA|].
      assert (0 <= 2 ^ (T - (nbb - w)) * (Znth (w + 1) rs0 - Znth w rs0)) by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg|]; lia).
      lia. }
    pose proof (HPRV0 w ltac:(lia)) as PW.
    replace (rv_idx 0 w) with w in HD by (unfold rv_idx; lia).
    assert (TAIL : forall dt2 m2 (r136 r176 r184 r192 r200 r208 r216 r240 r248 r264 r272 : word) (j2 : list byte)
                     (y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 : word),
        fill_x2 f dt2 (w + 1) wEnd T rv sorted rs0 nbb = Ok r -> length dt2 = ncells ->
        u8arr usegs m2 (DT + 4) (ox2 jt dt2) -> bytes_at usegs m2 SY (omerge js sorted) ->
        rw_cells usegs m2 (SP + 48)
          (x2_frame DT WK T nbb wEnd w p80 r136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (nbb - w + (nbb - T)))
             (Z_to_bv 64 (nbb - w)) r176 r184 r192 r200 r208 r216 (Z_to_bv 64 w) r240 r248 r264 r272 j2) ->
        stk usegs m2 lo SP ->
        munch [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, SP); (SP + 136, SP + 288)] m m2 ->
        wmono usegs m m2 -> mem_inv usegs m2 ->
        evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp y5 y6 y7 y8 (Z_to_bv 64 T) y10 y11 y12 y13 y14 y15 y16 y17
                                (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) y20 y21 y22 (Z_to_bv 64 (- (WK + 676) - 1)) y24 y25
                                y26 y27 y28 y29 y30 y31)
                           F (Z_to_bv 64 (PHUF_RDT_X2 + 968)) fc None m2 (seg_rom usegs))).
    { intros dt2 m2 r136 r176 r184 r192 r200 r208 r216 r240 r248 r264 r272 j2
        y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31
        HF2 LD2 ARR2 SYB2 FR2 STK2 MU2 WM2 MI2.
      unfold x2_frame in FR2.
      eapply (FXL w dt2 m2); [lia | exact ARR2 | exact LD2 | exact SYB2 | exact FR2 | exact STK2 | exact MU2 | exact WM2 | exact MI2 | |].
      - intros Hlt m3 s136 s144 s152 s160 s176 s184 s192 s200 s208 s216 s224 s240 s248 s264 s272 j3
          z5 z6 z7 z8 z10 z13 z14 z15 z16 z17 z20 z21 z22 z24 z25 z26 z27 z28 z29 z30 ARR3 SYB3 FR3 STK3 MU3 WM3 MI3.
        apply (IH (w + 1) dt2 m3 r z5 z6 z7 z8 z10 z13 z14 z15 z16 z17 z20 z21 z22 z24 z25 z26 z27 z28 z29 z30 HF2
                 ltac:(lia) ltac:(lia)); [| exact CONT].
        refine (conj ARR3 (conj LD2 (conj SYB3 (conj _ (conj STK3 (conj MU3 (conj WM3 MI3))))))).
        exists s136, s144, s152, s160, s176, s184, s192, s200, s208, s216, s224, s240, s248, s264, s272, j3. exact FR3.
      - intros Heq m3 s136 s144 s152 s160 s176 s184 s192 s200 s208 s216 s224 s240 s248 s264 s272 j3
          z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
          ARR3 SYB3 FR3 STK3 MU3 WM3 MI3.
        assert (RR : r = dt2).
        { destruct f as [|f']; [cbn in HF2; congruence|]. rewrite fx2_stop in HF2 by lia. congruence. }
        apply (CONT m3 dt2 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
                 RR).
        refine (conj ARR3 (conj LD2 (conj SYB3 (conj _ (conj STK3 (conj MU3 (conj WM3 MI3))))))).
        exists s136, s144, s152, s160, s176, s184, s192, s200, s208, s216, s224, s240, s248, s264, s272, j3. exact FR3. }
    destruct (Z.leb_spec (nbb - (wEnd - 1)) (T - (nbb - w))) as [TWO|ONE].
    - apply bind_Ok_inv in HD as (st & L3 & HD). apply load_Ok in L3 as (L3 & ->).
      assert (LND : Z.land (T - (nbb - w)) 31 = T - (nbb - w)).
      { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      rewrite LND, shl32_1 in HD by lia. cbn [bind] in HD.
      fgo [1036] RS1 RVA RVE w rs0 rv WK.
      all: fgo [1124; 1240] RS1 RVA RVE w rs0 rv WK.
      all: rewrite ?sx32_small in * by lia.
      all: specialize (FXT w dt); cbv zeta in FXT.
      all: first [ rewrite (Z.max_r 1 (nbb - w + (nbb - T))) in FXT, HD by lia
                 | rewrite (Z.max_l 1 (nbb - w + (nbb - T))) in FXT, HD by lia ].
      all: try rewrite (Z.mod_small (nbb - w)) by lia.
      all: try rewrite (Z.mod_small (T - (nbb - w))) by lia.
      all: eapply FXT.
      all: lazymatch goal with
           | |- forall _, _ => idtac
           | |- fill_two_level _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact HD
           | |- rw_cells _ _ _ _ => eassumption
           | |- _ => first [eassumption | lia]
           end.
      all: intros m2 r136 r176 r184 r192 r200 r208 r216 r240 r248 r272 j2
             y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31
             ARR2 LD2 SYB2 FR2 STK2 MU2 WM2 MI2.
      all: eapply TAIL; [exact HF | exact LD2 | exact ARR2 | exact SYB2 | unfold x2_frame; exact FR2 | eassumption .. ].
    - try rewrite (proj2 (Z.leb_gt _ _) ONE) in HD.
      apply bind_Ok_inv in HD as (st & L3 & HD). apply load_Ok in L3 as (L3 & ->).
      apply bind_Ok_inv in HD as ([dtA u] & HFW & HD). cbn in HD. injection HD as <-.
      fgo [1036] RS1 RVA RVE w rs0 rv WK.
      all: fgo [1228; 1240] RS1 RVA RVE w rs0 rv WK.
      all: zstep.
      all: replace (Z_to_bv 64 (Znth (w + 1) rs0 + SY)) with (Z_to_bv 64 (SY + Znth (w + 1) rs0)) by (f_equal; lia).
      all: pose proof x2fill_proof as XF; unfold x2fill_stmt in XF.
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut;
        [ eapply evt_eq; [| eapply (XF _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc DT SY (Znth w rs0)
                                 (Znth (w + 1) rs0) (nbb - w) T 0 1 (Znth w rv) lo sorted js jt ncells dt (dtA, u))];
          [ reflexivity | exact HFW | .. ]
        | ] end.
      all: try exact HSYR.
      all: lazymatch goal with |- evt _ _ _ => idtac | |- forall _, _ => idtac | |- _ =>
             first [ eassumption | (left; reflexivity) | (unfold X2FILL_STACK; lia) | lia | (destruct DJ; [left|right]; lia) ]
           end.
      all: intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & -> & ARR1 & LEN1 & SYB1 &
                  MU1 & WM1 & MI1 & STK1).
      all: cbn [fst] in ARR1, LEN1.
      all: lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
             replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n)
               by (symmetry; apply ret_pc_even; unfold PHUF_RDT_X2; [lia | reflexivity]) end.
      all: lazymatch type of MU1 with munch _ ?mc _ =>
             clear ARR SYB STK; unfold X2FILL_STACK in MU1; transport_after_call usegs mc m2 MU1 WM1; clear MU1 WM1 end.
      all: fgo [968] RS1 RVA RVE w rs0 rv WK.
      all: eapply TAIL; [exact HF | exact LEN1 | eassumption | eassumption | unfold x2_frame; eassumption | eassumption .. ].
  Qed.
  Lemma fx_loop : fx_loop_stmt.
  Proof.
    apply fx_loop_core; [eapply fx_two | eapply fx_latch]; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End FX.
