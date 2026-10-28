From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk
  RF_huf_bdt_model RF_huf_x2t_model RF_huf_x2t_c1 RF_huf_x2t_kit_fill RF_huf_x2t_skc RF_huf_x2t_lv2 RF_huf_x2t_gen.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Step MState.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
  ?omerge_length, ?ox2_length, ?upd_bytes_length in *.

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
  | H : stk segs m ?lo2 ?hi2 |- _ =>
      first [ apply (stk_write segs m lo2 hi2 a bs) in H; [ | lia | simpl_sizes; simpl_arr_sizes; lia ]
            | clear H ]
  end.

Definition x2c_frame (DT WK T nbb wEnd w : Z)
    (p80 q136 q144 q152 q160 q176 q184 q192 q200 q208 q216 q224 q240 q248 q264 q272 : word) (j : list byte) : list cell :=
  [C8 (Z_to_bv 64 wEnd); C8 (Z_to_bv 64 (nbb - T)); C8 (Z_to_bv 64 223338299392); C8 (Z_to_bv 64 (- (DT + 4) - 1)); C8 p80;
   C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (nbb - wEnd + 1)); C8 (Z_to_bv 64 nbb); C8 (Z_to_bv 64 WK);
   C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 (WK + 676)); C8 q136; C8 q144; C8 q152; C8 q160;
   C8 (Z_to_bv 64 (2 * nbb - w)); C8 q176; C8 q184; C8 q192; C8 q200; C8 q208; C8 q216; C8 q224;
   C8 (Z_to_bv 64 (DT + 4)); C8 q240; C8 q248; C8 (Z_to_bv 64 (wEnd - 1)); C8 q264; C8 q272; CB 8 j].

Lemma fxc_swrap_dec : forall a M, 0 < M -> M mod 4294967296 = 0 -> -1000 <= a <= 1000 ->
  bv_swrap 32 (a mod M + -1) = a - 1.
Proof.
  intros a M HM HD Ha. apply swrap32_eqm; [lia|].
  replace (a mod M + -1 - (a - 1)) with (a mod M - a) by lia.
  rewrite (Z.mod_eq a M) by lia.
  replace (a - M * (a / M) - a) with (- (a / M) * M) by ring.
  apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide; [lia|]. exact HD.
Qed.

Section FXC.
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
  Notation W := [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, SP); (SP + 136, SP + 288)].

  Definition fx_latch_stmt : Prop :=
    forall w dt1 m2 (q136 q176 q184 q192 q200 q208 q216 q240 q248 q264 q272 : word) (j : list byte)
      (x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    1 <= w < wEnd ->
    u8arr usegs m2 (DT + 4) (ox2 jt dt1) -> length dt1 = ncells -> bytes_at usegs m2 SY (omerge js sorted) ->
    rw_cells usegs m2 (SP + 48)
      (x2c_frame DT WK T nbb wEnd w p80 q136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (nbb - w + (nbb - T))) (Z_to_bv 64 (nbb - w))
         q176 q184 q192 q200 q208 q216 (Z_to_bv 64 w) q240 q248 q264 q272 j) ->
    stk usegs m2 lo SP -> munch W m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
    (w + 1 < wEnd ->
     forall m3 (r136 r144 r152 r160 r176 r184 r192 r200 r208 r216 r224 r240 r248 r264 r272 : word) (j3 : list byte)
            (y5 y6 y7 y8 y10 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 : word),
       u8arr usegs m3 (DT + 4) (ox2 jt dt1) -> bytes_at usegs m3 SY (omerge js sorted) ->
       rw_cells usegs m3 (SP + 48)
         (x2c_frame DT WK T nbb wEnd (w + 1) p80 r136 r144 r152 r160 r176 r184 r192 r200 r208 r216 r224 r240 r248 r264
            r272 j3) ->
       stk usegs m3 lo SP -> munch W m m3 -> wmono usegs m m3 -> mem_inv usegs m3 ->
       evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp y5 y6 y7 y8 (Z_to_bv 64 T) y10
                               (Z_to_bv 64 (nbb - (w + 1) + (nbb - T))) (Z_to_bv 64 (w + 1)) y13 y14 y15 y16 y17
                               (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) y20 y21 y22 (Z_to_bv 64 (- (WK + 676) - 1)) y24 y25
                               y26 y27 y28 y29 y30 (Z_to_bv 64 (nbb - (w + 1))))
                          F (Z_to_bv 64 (PHUF_RDT_X2 + 1012)) fc None m3 (seg_rom usegs))) ->
    (w + 1 = wEnd ->
     forall m3 (r136 r144 r152 r160 r176 r184 r192 r200 r208 r216 r224 r240 r248 r264 r272 : word) (j3 : list byte)
            (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       u8arr usegs m3 (DT + 4) (ox2 jt dt1) -> bytes_at usegs m3 SY (omerge js sorted) ->
       rw_cells usegs m3 (SP + 48)
         (x2c_frame DT WK T nbb wEnd wEnd p80 r136 r144 r152 r160 r176 r184 r192 r200 r208 r216 r224 r240 r248 r264 r272
            j3) ->
       stk usegs m3 lo SP -> munch W m m3 -> wmono usegs m m3 -> mem_inv usegs m3 ->
       evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22
                               y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X2 + 2000)) fc None m3 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp x5 x6 x7 x8 (Z_to_bv 64 T) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) x20 x21 x22 (Z_to_bv 64 (- (WK + 676) - 1)) x24 x25 x26
                            x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 968)) fc None m2 (seg_rom usegs)).

  Ltac fxc_go := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        let b := eval vm_compute in ((pc =? PHUF_RDT_X2 + 1012) || (pc =? PHUF_RDT_X2 + 2000))%bool in
        lazymatch b with false => zstep end
    end).

  Lemma fx_latch : fx_latch_stmt.
  Proof using All.
    unfold fx_latch_stmt.
    intros w dt1 m2 q136 q176 q184 q192 q200 q208 q216 q240 q248 q264 q272 j
      x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      Hw ARR LDT SYB FR STK MU WM MI KB KE.
    unfold x2c_frame in FR.
    pose proof HDT. pose proof HWK. pose proof HLO.
    fxc_go.
    let C := fresh "C" in if_cases C; zify_cond C; rewrite ?unsigned_lit in C by lia.
    all: fxc_go.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (pc =? PHUF_RDT_X2 + 2000) in lazymatch b with
      | true =>
          assert (E : w + 1 = wEnd) by lia;
          try replace (2 * nbb - w + -1) with (2 * nbb - wEnd) in * by lia;
          eapply KE; [exact E | eassumption .. ]
      | false =>
          assert (E : w + 1 < wEnd) by lia;
          try replace (2 * nbb - w + -1) with (2 * nbb - (w + 1)) in * by lia;
          rewrite ?unsigned_lit by lia;
          repeat match goal with |- context [bv_swrap 32 (?a mod ?M + -1)] =>
            rewrite (fxc_swrap_dec a M) by (first [reflexivity | lia]) end;
          try replace (nbb - w + (nbb - T) - 1) with (nbb - (w + 1) + (nbb - T)) by lia;
          try replace (nbb - w + (nbb - T) + -1) with (nbb - (w + 1) + (nbb - T)) by lia;
          try replace (nbb - w + -1) with (nbb - (w + 1)) by lia;
          eapply KB; [exact E | eassumption .. ]
      end end.
  Qed.
End FXC.
