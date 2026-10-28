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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model
  RF_huf_x1t_model RF_huf_x2t_model RF_huf_x2t_c1 RF_huf_x2t_kit_fill.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
  ?omerge_length, ?ox2_length, ?upd_bytes_length in *.

Lemma lv_shl2 : forall x, x ≪ 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma lv_lx63 : forall o, 0 <= o < 9223372036854775808 -> (Z.lxor o 9223372036854775808 <? 9223372036854775808) = false.
Proof. intros o Ho. change 9223372036854775808 with (2 ^ 63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia. Qed.

Local Ltac pnorm U :=
  repeat match type of U with
         | context [Z.lxor ?o 9223372036854775808 <? 9223372036854775808] => rewrite (lv_lx63 o) in U by lia
         end;
  repeat match type of U with
         | context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b)) in U by (rewrite ?Z.mod_small by lia; lia)
         end;
  cbn in U.

Local Ltac pchk U := exfalso; rewrite ?lv_shl2 in U;
  first [ lia | (Z.div_mod_to_equations; lia)
        | (pnorm U; first [discriminate | lia | (Z.div_mod_to_equations; lia)]) ].

Local Ltac cgo stops := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) stops) in lazymatch b with false => zstep end
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 82516 else _) _ _ _ _) =>
      rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?lv_shl2;
      let U := fresh "U" in if_cases U; zify_cond U; [pchk U |]
  | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 82516) _ _ _ _) =>
      rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?lv_shl2;
      let U := fresh "U" in if_cases U; zify_cond U; [| pchk U]
  end).


Definition x2g_inv (m m1 : fmem) (W : list ivl) (DT SY : Z) (js jt : list byte) (sorted : list (option Z))
    (ncells : nat) (lo S : Z) (dt : list (option deltX2)) : Prop :=
  u8arr usegs m1 (DT + 4) (ox2 jt dt) /\ length dt = ncells /\ bytes_at usegs m1 SY (omerge js sorted)
  /\ stk usegs m1 lo S /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

Lemma lv_sub2 : forall lo S DT n, lo <= S - X2FILL_STACK ->
  sub_fp [(S - X2FILL_STACK, S); (DT + 4, DT + 4 + n)] [(DT + 4, DT + 4 + n); (lo, S)].
Proof.
  unfold X2FILL_STACK. intros lo S DT n HL x HX. cbn [outside] in *. destruct HX as (H1 & H2 & _).
  split; [intro Hx; apply H2; lia | split; [exact H1 | exact I]].
Qed.

Section LV2.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x25 : word).
  Variables (m : fmem) (DT SY WK cons T nbb wEnd start sym1 minW lo : Z) (sorted : list (option Z)) (js jt : list byte)
    (ncells : nat) (rs0 rv : list Z).
  Variable POST : machine_state -> Prop.
  Notation S := (bv_unsigned sp).
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis HDT2 : DT mod 2 = 0.
  Hypothesis HSYE : SY = WK + 736.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= WK \/ WK + 2124 <= DT + 4.
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ WK + 2124 <= lo /\ lo <= S - 48 /\ S <= 2^47.
  Hypothesis HS1 : 0 <= sym1 < 256.
  Hypothesis HT : 1 <= T <= 12.
  Hypothesis HNBB : 2 <= nbb <= 13.
  Hypothesis HWE : 2 <= wEnd <= nbb.
  Hypothesis HCONS : 1 <= cons <= 11.
  Hypothesis HMW : 1 <= minW /\ cons + nbb - T <= minW.
  Hypothesis HST : 0 <= start <= 4096.
  Hypothesis LRS : length rs0 = 15%nat.
  Hypothesis HRSV : forall w, 1 <= w <= wEnd - 1 -> 0 <= Znth w rs0 <= Znth (w + 1) rs0 /\ Znth (w + 1) rs0 <= 256.
  Hypothesis LRV : length rv = 156%nat.
  Variable PRV : Z -> Prop.
  Hypothesis HPRV : forall w, minW <= w <= wEnd - 1 -> PRV (rv_idx cons w).
  Hypothesis HRVR : forall w, minW <= w <= wEnd - 1 -> 0 <= Znth (rv_idx cons w) rv < 2^32.
  Hypothesis RSA0 : u32arr usegs m (WK + 676) (map (Z_to_bv 64) rs0).
  Hypothesis RVA0 : rv_at m WK rv PRV.
  Notation W := [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, S)].
  Notation INV m1 dt := (x2g_inv m m1 W DT SY js jt sorted ncells lo S dt).
  Notation ST pc mm w2 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 T) sp gp tp x5 x6 x7 (Z_to_bv 64 (- (WK + 52 * cons) - 1)) (Z_to_bv 64 T) (Z_to_bv 64 (4 * w2))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 SY) x19 (Z_to_bv 64 sym1) (Z_to_bv 64 (nbb - w2 + cons))
             (Z_to_bv 64 (52 * cons)) (Z_to_bv 64 (- (WK + 676) - 1)) (Z_to_bv 64 (WK + 4 * w2)) x25
             (Z_to_bv 64 (DT + 4 + 4 * start)) (Z_to_bv 64 (wEnd - w2)) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma lv2_loop : forall f w2 dt m1 r (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
    level2_weights f dt start w2 wEnd T cons rv sorted rs0 nbb sym1 = Ok r ->
    wEnd - w2 < Z.of_nat f -> minW <= w2 < wEnd -> INV m1 dt ->
    (forall m2 dt' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word),
       r = dt' -> INV m2 dt' ->
       evt usegs POST (ST 0x14874 m2 wEnd y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x147e0 m1 w2 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros w2 dt m1 r x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 HF Hf Hw INV CONT;
      [lia|].
    destruct INV as (ARR & LDT & SYB & STK & MU & WM & MI).
    cbn [level2_weights] in HF. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hw)) in HF.
    apply bind_Ok_inv in HF as (b & L1 & HF). apply load_Ok in L1 as (L1 & ->).
    apply bind_Ok_inv in HF as (e & L2 & HF). apply load_Ok in L2 as (L2 & ->).
    apply bind_Ok_inv in HF as (off & L3 & HF). apply load_Ok in L3 as (L3 & ->).
    apply bind_Ok_inv in HF as ([dt1 u] & HFW & HF).
    destruct (HRSV w2 ltac:(lia)) as (RB1 & RB2).
    pose proof (HRVR w2 ltac:(lia)) as RO. unfold rv_idx in RO, HFW.
    pose proof (u32arr_transport usegs _ m m1 _ _ RSA0 MU WM
                  ltac:(rewrite length_map, LRS; cbn; lia)) as RS1.
    pose proof (rv_at_transport _ m m1 WK rv PRV RVA0 MU WM ltac:(cbn; lia)) as RV1.
    pose proof (rv_at_read m1 WK rv PRV (cons * 13 + w2) (wa (WK + 4 * (cons * 13 + w2))) RV1
                  (HPRV w2 ltac:(lia)) ltac:(lia) eq_refl) as RD0.
    pose proof (u32arr_read usegs m1 (WK + 676) _ w2 _ (wa (WK + 676 + 4 * w2)) RS1
                  (nth_map_Znth2 rs0 w2 ltac:(lia)) ltac:(lia) eq_refl) as RD1.
    pose proof (u32arr_read usegs m1 (WK + 676) _ (w2 + 1) _ (wa (WK + 676 + 4 * (w2 + 1))) RS1
                  (nth_map_Znth2 rs0 (w2 + 1) ltac:(lia)) ltac:(lia) eq_refl) as RD2.
    cgo [0x14858].
    zstep.
    replace (Z_to_bv 64 (DT + 4 + 4 * start + 4 * Znth (cons * 13 + w2) rv))
      with (Z_to_bv 64 (DT + 4 + 4 * (start + Znth (cons * 13 + w2) rv))) by (f_equal; lia).
    replace (Z_to_bv 64 (Znth (w2 + 1) rs0 + SY)) with (Z_to_bv 64 (SY + Znth (w2 + 1) rs0)) by (f_equal; lia).
    pose proof x2fill_proof as XF. unfold x2fill_stmt in XF.
    eapply evt_cut.
    { eapply evt_eq; [| eapply (XF _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 DT SY (Znth w2 rs0)
                                 (Znth (w2 + 1) rs0) (nbb - w2 + cons) T sym1 2 (start + Znth (cons * 13 + w2) rv) lo
                                 sorted js jt ncells dt (dt1, u))].
      - reflexivity.
      - exact HFW.
      - lia.
      - lia.
      - right; reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact HJT.
      - exact HJS.
      - exact HLS.
      - exact HSYR.
      - lia.
      - exact HDT2.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact ARR.
      - exact LDT.
      - exact SYB.
      - exact STK.
      - unfold X2FILL_STACK; lia.
      - lia.
      - exact MI. }
    intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & -> & ARR1 & LEN1 & SYB1 &
                MU1 & WM1 & MI1 & STK1).
    cbn [fst] in ARR1, LEN1.
    replace (ret_pc (Z_to_bv 64 0x1485c)) with (Z_to_bv 64 0x1485c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    pose proof (munch_trans _ m m1 m2 MU (munch_weaken _ _ m1 m2 (lv_sub2 lo S DT _ ltac:(unfold X2FILL_STACK; lia)) MU1)) as MU2.
    pose proof (wmono_trans usegs m m1 m2 WM WM1) as WM2.
    cgo [0x147e0; 0x14874].
    rewrite swrap32_small by lia.
    replace (nbb - w2 + cons + -1) with (nbb - (w2 + 1) + cons) by lia.
    replace (WK + 4 * w2 + 4) with (WK + 4 * (w2 + 1)) by lia.
    replace (4 * w2 + 4) with (4 * (w2 + 1)) by lia.
    replace (wEnd - w2 + -1) with (wEnd - (w2 + 1)) by lia.
    assert (INV2 : INV m2 dt1) by exact (conj ARR1 (conj LEN1 (conj SYB1 (conj STK1 (conj MU2 (conj WM2 MI1)))))).
    if_cases U9; zify_cond U9.
    - apply (IH (w2 + 1) dt1 m2 r); [exact HF | lia | lia | exact INV2 |].
      exact CONT.
    - assert (EW : w2 + 1 = wEnd) by lia. rewrite EW in *.
      assert (r = dt1) as ->.
      { destruct f; cbn [level2_weights] in HF; [injection HF as <-; reflexivity|].
        rewrite Z.ltb_irrefl in HF. injection HF as <-. reflexivity. }
      apply (CONT m2 dt1); [reflexivity | exact INV2].
  Qed.

End LV2.
