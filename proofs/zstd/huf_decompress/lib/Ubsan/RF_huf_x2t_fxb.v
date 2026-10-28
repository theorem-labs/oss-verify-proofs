From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk
  RF_huf_bdt_model RF_huf_x2t_model RF_huf_x2t_c1 RF_huf_x2t_kit_fill RF_huf_x2t_skc RF_huf_x2t_lv2 RF_huf_x2t_gen.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma zx32_small' : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Ltac dec_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  tryif (match c with context [?v] => is_var v end) then fail else
  let b := eval vm_compute in c in change c with b; cbv iota end.
Ltac xnorm := repeat (first [ rewrite zx32_small' by lia | rewrite sx32_small by lia | rewrite unsigned_lit by lia
                            | rewrite swrap32_small by lia | rewrite zb_lxor_ones by lia | rewrite Z.add_0_r ]).

Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
  ?omerge_length, ?ox2_length, ?upd_bytes_length in *.

Lemma fx_mulhu52 : forall k, 0 <= k < 2^31 -> ((k ≪ 32) mod 18446744073709551616 * 223338299392) ≫ 64 = 52 * k.
Proof.
  intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
  replace (k * 4294967296 * 223338299392) with (52 * k * 18446744073709551616) by lia.
  apply Z.div_mul. lia.
Qed.

Ltac fpn U :=
  repeat match type of U with
         | context [Z.lxor ?o 9223372036854775808 <? 9223372036854775808] => rewrite (gn_lx63 o) in U by lia
         end;
  repeat match type of U with
         | context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b)) in U by (rewrite ?Z.mod_small by lia; lia)
         end;
  cbn in U.

Ltac fck U := exfalso; rewrite ?gn_shl2 in U; rewrite ?signed_small2 in U by lia;
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

Ltac rdw RS RVA RVE w rs0 rv WK :=
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

Ltac fgo stops RS RVA RVE w rs0 rv WK := repeat (lazymatch goal with
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



Lemma fx_bvm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.

Lemma fx_swrap_mod : forall x y, bv_swrap 32 (x + y mod 2^64) = bv_swrap 32 (x + y).
Proof.
  intros x y. unfold bv_swrap, bv_wrap. f_equal.
  change (bv_modulus 32) with 4294967296.
  rewrite (Z.mod_eq y (2^64)) by lia.
  replace (x + (y - 2^64 * (y / 2^64)) + bv_half_modulus 32)
    with (x + y + bv_half_modulus 32 + (- (4294967296 * (y / 2^64))) * 4294967296) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma fx_swrap_modM : forall x y M, M = 2^64 -> bv_swrap 32 (x + y mod M) = bv_swrap 32 (x + y).
Proof. intros x y M ->. apply fx_swrap_mod. Qed.

Definition x2b_frame (DT WK T nbb wEnd w : Z)
    (p80 q136 q144 q152 q160 q176 q184 q192 q200 q208 q216 q224 q240 q248 q264 q272 : word) (j : list byte) : list cell :=
  [C8 (Z_to_bv 64 wEnd); C8 (Z_to_bv 64 (nbb - T)); C8 (Z_to_bv 64 223338299392); C8 (Z_to_bv 64 (- (DT + 4) - 1)); C8 p80;
   C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (nbb - wEnd + 1)); C8 (Z_to_bv 64 nbb); C8 (Z_to_bv 64 WK);
   C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 (WK + 676)); C8 q136; C8 q144; C8 q152; C8 q160;
   C8 (Z_to_bv 64 (2 * nbb - w)); C8 q176; C8 q184; C8 q192; C8 q200; C8 q208; C8 q216; C8 q224;
   C8 (Z_to_bv 64 (DT + 4)); C8 q240; C8 q248; C8 (Z_to_bv 64 (wEnd - 1)); C8 q264; C8 q272; CB 8 j].

Section FXB.
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

  Definition fx_two_stmt : Prop :=
    forall w dt m1 dt1 (q136 q176 q184 q192 q200 q208 q216 q240 q248 q272 : word) (j : list byte)
      (x5 x6 x7 x8 x15 x16 x17 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    let nb := nbb - w in let b := Znth w rs0 in let e := Znth (w + 1) rs0 in
    fill_two_level (S (Z.to_nat (e - b))) dt b e (Znth w rv) (2 ^ (T - nb)) T nb (Z.max 1 (nb + (nbb - T))) wEnd rv sorted
      rs0 nbb = Ok dt1 ->
    1 <= w < wEnd -> nbb - (wEnd - 1) <= T - nb ->
    u8arr usegs m1 (DT + 4) (ox2 jt dt) -> length dt = ncells -> bytes_at usegs m1 SY (omerge js sorted) ->
    rw_cells usegs m1 (SP + 48)
      (x2b_frame DT WK T nbb wEnd w p80 q136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (nb + (nbb - T))) (Z_to_bv 64 nb) q176 q184
         q192 q200 q208 q216 (Z_to_bv 64 w) q240 q248 (Z_to_bv 64 e) q272 j) ->
    stk usegs m1 lo SP -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    (forall m2 (r136 r176 r184 r192 r200 r208 r216 r240 r248 r272 : word) (j2 : list byte)
            (y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       u8arr usegs m2 (DT + 4) (ox2 jt dt1) -> length dt1 = ncells -> bytes_at usegs m2 SY (omerge js sorted) ->
       rw_cells usegs m2 (SP + 48)
         (x2b_frame DT WK T nbb wEnd w p80 r136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (nb + (nbb - T))) (Z_to_bv 64 nb) r176
            r184 r192 r200 r208 r216 (Z_to_bv 64 w) r240 r248 (Z_to_bv 64 e) r272 j2) ->
       stk usegs m2 lo SP -> munch W m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
       evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp y5 y6 y7 y8 (Z_to_bv 64 T) y10 y11 y12 y13 y14 y15 y16 y17
                               (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) y20 y21 y22 (Z_to_bv 64 (- (WK + 676) - 1)) y24 y25
                               y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X2 + 968)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp x5 x6 x7 x8 (Z_to_bv 64 T) (Z_to_bv 64 (Z.max 1 (nb + (nbb - T))))
                            (Z_to_bv 64 (WK + 4 * w)) (Z_to_bv 64 (T - nb)) (Z_to_bv 64 nb) (Z_to_bv 64 (4 * w)) x15 x16 x17
                            (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) x20 x21 x22 (Z_to_bv 64 (- (WK + 676) - 1)) x24
                            (Z_to_bv 64 b) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 1240)) fc None m1 (seg_rom usegs)).
  Definition fx_gen_stmt : Prop :=
    forall w dt m2 dt1 (c136 c176 c184 c192 c200 c208 c216 c240 c248 c272 : word) (j : list byte)
      (x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    let nb := nbb - w in let b := Znth w rs0 in let e := Znth (w + 1) rs0 in
    fill_two_level (S (Z.to_nat (e - b))) dt b e (Znth w rv) (2 ^ (T - nb)) T nb (Z.max 1 (nb + (nbb - T))) wEnd rv sorted
      rs0 nbb = Ok dt1 ->
    1 <= w < wEnd -> nbb - (wEnd - 1) <= T - nb -> b < e ->
    c136 = (Z_to_bv 64 (WK + 52 * (nbb - w) + 4 * (Z.max 1 (nbb - w + (nbb - T))))) ->
    c176 = (Z_to_bv 64 (WK + 4 * (Z.max 1 (nbb - w + (nbb - T))))) ->
    c184 = (Z_to_bv 64 (wEnd - (Z.max 1 (nbb - w + (nbb - T))))) ->
    c192 = (Z_to_bv 64 (nbb - (Z.max 1 (nbb - w + (nbb - T))) + (nbb - w))) ->
    c200 = (Z_to_bv 64 (4 * (Z.max 1 (nbb - w + (nbb - T))))) ->
    c208 = (Z_to_bv 64 ((nbb - w) * 65536 + 16777216)) ->
    c216 = (Z_to_bv 64 (4 * (Z.max 1 (nbb - w + (nbb - T))))) ->
    c240 = (Z_to_bv 64 (nbb - w + (nbb - T))) ->
    c248 = (Z_to_bv 64 (Z.max 1 (nbb - w + (nbb - T)))) ->
    c272 = (Z_to_bv 64 (2 ^ (T - (nbb - w)))) ->
    x8 = Z_to_bv 64 (- (WK + 52 * nb) - 1) -> x16 = Z_to_bv 64 (Znth w rv) -> x22 = Z_to_bv 64 (52 * nb) ->
    u8arr usegs m2 (DT + 4) (ox2 jt dt) -> length dt = ncells -> bytes_at usegs m2 SY (omerge js sorted) ->
    rw_cells usegs m2 (SP + 48)
      (x2b_frame DT WK T nbb wEnd w p80 c136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (nb + (nbb - T))) (Z_to_bv 64 nb) c176 c184
         c192 c200 c208 c216 (Z_to_bv 64 w) c240 c248 (Z_to_bv 64 e) c272 j) ->
    stk usegs m2 lo SP -> munch W m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
    (forall m3 (r136 r176 r184 r192 r200 r208 r216 r240 r248 r272 : word) (j2 : list byte)
            (y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       u8arr usegs m3 (DT + 4) (ox2 jt dt1) -> length dt1 = ncells -> bytes_at usegs m3 SY (omerge js sorted) ->
       rw_cells usegs m3 (SP + 48)
         (x2b_frame DT WK T nbb wEnd w p80 r136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (nb + (nbb - T))) (Z_to_bv 64 nb) r176
            r184 r192 r200 r208 r216 (Z_to_bv 64 w) r240 r248 (Z_to_bv 64 e) r272 j2) ->
       stk usegs m3 lo SP -> munch W m m3 -> wmono usegs m m3 -> mem_inv usegs m3 ->
       evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp y5 y6 y7 y8 (Z_to_bv 64 T) y10 y11 y12 y13 y14 y15 y16 y17
                               (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) y20 y21 y22 (Z_to_bv 64 (- (WK + 676) - 1)) y24 y25
                               y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X2 + 968)) fc None m3 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp x5 x6 x7 x8 (Z_to_bv 64 T) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) x20 x21 x22 (Z_to_bv 64 (- (WK + 676) - 1)) x24
                            (Z_to_bv 64 b) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 1424)) fc None m2 (seg_rom usegs)).

  Lemma fx_gen : fx_gen_stmt.
  Proof using All.
    unfold fx_gen_stmt.
    intros until x31. cbv zeta.
    intros HF HW HNB HBE E136 E176 E184 E192 E200 E208 E216 E240 E248 E272 E8 E16 E22 ARR LDT SYB FR STK MU WM MI CONT.
    subst c136 c176 c184 c192 c200 c208 c216 c240 c248 c272 x8 x16 x22.
    destruct (HRSV w ltac:(lia)) as (RB1 & RB2).
    destruct (HRV0 w ltac:(lia)) as (RV0a & RV0b).
    lazymatch goal with |- context [PHUF_RDT_X2 + ?k] =>
      let v := eval vm_compute in (PHUF_RDT_X2 + k) in change (PHUF_RDT_X2 + k) with v end.
    lazymatch type of CONT with context [PHUF_RDT_X2 + ?k] =>
      let v := eval vm_compute in (PHUF_RDT_X2 + k) in change (PHUF_RDT_X2 + k) with v in CONT end.
    unfold x2b_frame in FR.
    lazymatch type of FR with rw_cells _ _ _ ?L =>
      destruct (proj1 (rw_cells_app' usegs m2 (SP + 48) (firstn 5 L) (skipn 5 L)) FR) as (FRa & FRbc) end.
    cbn [firstn skipn] in FRa, FRbc.
    lazymatch type of FRbc with rw_cells _ _ ?A _ => replace A with (SP + 88) in FRbc by (cbn; lia) end.
    lazymatch type of FRbc with rw_cells _ _ _ ?L =>
      destruct (proj1 (rw_cells_app' usegs m2 (SP + 88) (firstn 24 L) (skipn 24 L)) FRbc) as (FRb & FRc) end.
    cbn [firstn skipn] in FRb, FRc.
    lazymatch type of FRc with rw_cells _ _ ?A _ => replace A with (SP + 280) in FRc by (cbn; lia) end.
    clear FR FRbc.
    eapply gen_loop with (m := m2) (m1 := m2) (dt := dt) (r := dt1) (s := Znth w rs0) (start := Znth w rv)
      (f := S (Z.to_nat (Znth (w + 1) rs0 - Znth w rs0))) (e1 := Znth (w + 1) rs0) (len1 := 2 ^ (T - (nbb - w)))
      (minW := Z.max 1 (nbb - w + (nbb - T))) (mwr := nbb - w + (nbb - T)) (PRV := PRV) (rs0 := rs0) (rv := rv)
      (DT := DT) (SY := SY) (WK := WK) (lo := lo) (ncells := ncells) (js := js) (jt := jt) (sorted := sorted).
    all: try exact HF.
    all: try exact FRb.
    all: try assumption.
    all: try (split; [reflexivity | lia]).
    all: try lia.
    all: first [ (intros w2 Hw2; apply HPRVC; lia)
               | (intros w2 Hw2; apply HRVC; lia)
               | exact (u32arr_transport usegs _ m m2 _ _ RSA0 MU WM ltac:(rewrite length_map, LRS; cbn; lia))
               | exact (rv_at_transport _ m m2 WK rv PRV RVA0 MU WM ltac:(cbn; lia))
               | exact (conj (conj ARR (conj LDT (conj SYB (conj STK (conj (munch_refl _ m2) (conj (wmono_refl usegs m2) MI))))))
                             (ex_intro _ j FRc))
               | exact RV0b
               | idtac ].
    all: try assumption.
    intros m3 dt' y5 y6 y7 y10 y11 y12 y13 y14 y15 y17 y20 y21 y24 y26 y27 y28 y29 y30 y31 HR I3. subst dt'.
    destruct I3 as ((ARR3 & LDT3 & SYB3 & STK3 & MU3 & WM3 & MI3) & j3 & FRc3).
    assert (SUB : sub_fp [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, SP); (SP + 280, SP + 288)]
                         [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, SP); (SP + 136, SP + 288)])
      by (intros x HX; cbn [outside] in *; lia).
    pose proof (munch_trans _ m m2 m3 MU (munch_weaken _ _ m2 m3 SUB MU3)) as MU4.
    pose proof (wmono_trans usegs m m2 m3 WM WM3) as WM4.
    pose proof (rw_cells_transport usegs _ m2 m3 _ _ FRa MU3 WM3 ltac:(cbn; lia)) as FRa3.
    pose proof (rw_cells_transport usegs _ m2 m3 _ _ FRb MU3 WM3 ltac:(cbn; lia)) as FRb3.
    lazymatch type of FRb3 with rw_cells _ _ _ ?L24 =>
      assert (FRbc3 : rw_cells usegs m3 (SP + 88) (L24 ++ [CB 8 j3]))
        by (apply rw_cells_app'; split; [exact FRb3 | replace (SP + 88 + _) with (SP + 280) by (cbn; lia); exact FRc3]) end.
    lazymatch type of FRa3 with rw_cells _ _ _ ?L5 =>
      lazymatch type of FRbc3 with rw_cells _ _ _ ?L25 =>
        assert (FR3 : rw_cells usegs m3 (SP + 48) (L5 ++ L25))
          by (apply rw_cells_app'; split; [exact FRa3 | replace (SP + 48 + _) with (SP + 88) by (cbn; lia); exact FRbc3]) end end.
    cbn [app] in FR3.
    eapply CONT; [exact ARR3 | exact LDT3 | exact SYB3 | unfold x2b_frame; exact FR3 | exact STK3 | exact MU4 | exact WM4
                 | exact MI3].
  Qed.
  Ltac fxbr :=
    repeat match goal with H : context [bv_swrap 32 (?x + ?y mod ?M)] |- _ => rewrite (fx_swrap_modM x y M) in H by reflexivity end;
    repeat match goal with |- context [bv_swrap 32 (?x + ?y mod ?M)] => rewrite (fx_swrap_modM x y M) by reflexivity end;
    repeat match goal with H : context [bv_swrap 32 ?z] |- _ => rewrite (swrap32_small z) in H by lia end;
    repeat match goal with |- context [bv_swrap 32 ?z] => rewrite (swrap32_small z) by lia end;
    repeat match goal with H : context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b); cbn [andb orb] in H end.
  Ltac fxpow := apply fx_bvm; f_equal;
    match goal with |- context [bv_swrap 32 (1 ≪ (?k mod 32))] =>
      rewrite (Z.mod_small k 32) by lia; rewrite (Z.shiftl_1_l k) by lia;
      pose proof (Z.pow_le_mono_r 2 k 11 ltac:(lia) ltac:(lia)); pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia));
      rewrite (swrap32_small (2 ^ k)) by (change (2 ^ 11) with 2048 in *; lia) end; reflexivity.
  Ltac fxeq := first [ (rewrite sx32_small by lia; reflexivity) | fxpow
    | (fxbr; apply fx_bvm;
       rewrite ?fx_swrap_mod; rewrite ?fx_mulhu52 by lia; rewrite ?swrap32_small by lia; rewrite ?gn_shl2;
       rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?zb_lxor_ones by (first [lia | (apply Z.mod_pos_bound; lia)]);
       Z.div_mod_to_equations; lia) ].


  Lemma fx_two : fx_two_stmt.
  Proof.
    unfold fx_two_stmt.
    intros w dt m1 dt1 q136 q176 q184 q192 q200 q208 q216 q240 q248 q272 j
      x5 x6 x7 x8 x15 x16 x17 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31.
    cbv zeta.
    intros HF Hw HTW ARR LDT SYB FR STK MU WM MI CONT.
    destruct (HRSV w ltac:(lia)) as (RB1 & RB2).
    pose proof (u32arr_transport usegs _ m m1 _ _ RSA0 MU WM
                  ltac:(rewrite length_map, LRS; cbn; lia)) as RS1.
    pose proof (rv_at_transport _ m m1 WK rv PRV RVA0 MU WM ltac:(cbn; lia)) as RV1.
    destruct RV1 as (rvw & LRW & RVA & RVE).
    pose proof (HPRV0 w ltac:(lia)) as PW.
    pose proof (HRV0 w ltac:(lia)) as RV0w.
    assert (RVW : 0 <= Znth w rv <= 4096).
    { destruct RV0w as (RA & RB). split; [exact RA|].
      assert (0 <= 2 ^ (T - (nbb - w)) * (Znth (w + 1) rs0 - Znth w rs0)) by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg|]; lia).
      lia. }
    unfold x2b_frame in FR.
    fgo [1424; 968] RS1 RVA RVE w rs0 rv WK.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        let d := eval vm_compute in (pc - PHUF_RDT_X2 =? 1424) in
        lazymatch d with
        | true => eapply fx_gen; [ exact HF | lia | lia | shelve | shelve | shelve | shelve | shelve | shelve | shelve
                                 | shelve | shelve | shelve | shelve | shelve | shelve | shelve
                                 | exact ARR | exact LDT | exact SYB | unfold x2b_frame; exact FR | exact STK
                                 | exact MU | exact WM | exact MI | exact CONT ]
        | false =>
            assert (BE : Znth w rs0 = Znth (w + 1) rs0) by (fxbr; first [lia | (rewrite ?Z.mod_small in * by lia; lia)]);
            assert (dt1 = dt) as -> by (rewrite <- BE in HF; replace (Znth w rs0 - Znth w rs0) with 0 in HF by lia;
                                        cbn [Z.to_nat fill_two_level] in HF; rewrite Z.eqb_refl in HF; inversion HF; reflexivity);
            eapply CONT; [exact ARR | exact LDT | exact SYB | unfold x2b_frame; exact FR | exact STK | exact MU | exact WM
                         | exact MI]
        end
      end.
    Unshelve.
    all: try (solve [lia]).
    all: solve [fxeq].
  Qed.
End FXB.
