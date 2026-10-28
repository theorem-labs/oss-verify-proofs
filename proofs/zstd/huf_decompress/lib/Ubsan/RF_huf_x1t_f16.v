(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX1
  HufPure_HufTableX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model
  RF_huf_x1t_model RF_huf_x1t_cls RF_huf_x1t_wk RF_huf_x1t_fk.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac x1g_to o := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in (z =? PHUF_RDT_X1 + o) in lazymatch d with true => fail | false => zstep end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => x1w_norm; first [ x1w_dec_if | x1k_ck ]
  end).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section F16I.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (WK DT SY tl V len b nb : Z) (syms : list (option Z)) (js jt : list byte) (ncells : nat)
            (cells0 : list (option deltX1)).
  Variables (cu cs cw cc x5 x10 x14 x15 x17 x21 x24 x29 : word).
  Variable POST : machine_state -> Prop.
  Notation SP := (bv_unsigned sp).
  Hypothesis HJT : length jt = (2 * ncells)%nat.
  Hypothesis HJS : length js = length syms.
  Hypothesis HB : 0 <= b < 256.
  Hypothesis HNB : 0 <= nb < 16.
  Hypothesis HV : 0 <= V.
  Hypothesis HLEN : 16 <= len <= 2048 /\ len mod 16 = 0.
  Hypothesis HVL : V + len <= Z.of_nat ncells.
  Hypothesis HNC : Z.of_nat ncells <= 8192.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 2 * Z.of_nat ncells <= 2^47.
  Hypothesis HSY : 0 < SY /\ SY + Z.of_nat (length js) <= 2^47.
  Hypothesis DJ : DT + 4 + 2 * Z.of_nat ncells <= SY \/ SY + Z.of_nat (length js) <= DT + 4.
  Hypothesis HSP : 240 <= SP /\ SP <= 2^47.
  Hypothesis DSD : DT + 4 + 2 * Z.of_nat ncells <= SP + -240 \/ SP <= DT + 4.
  Hypothesis DSS : SY + Z.of_nat (length js) <= SP + -240 \/ SP <= SY.
  Hypothesis LC0 : length cells0 = ncells.
  Notation INV m1 cells := (x1w_inv m m1 SP DT SY js jt syms ncells cells).
  Notation FRC := (x1_fr DT tl WK cu cs cw cc).
  Notation C := (mkX1 nb b).

  Lemma f16_in : forall j k m1 (x6 x7 x8 x11 x12 x22 x23 x25 x26 x27 x28 x30 x31 : word),
    x6 = Z_to_bv 64 (2^64 - 1 - (V * 2 + (DT + 4))) -> x7 = Z_to_bv 64 (32 * k) ->
    x11 = Z_to_bv 64 (DT + 20 + V * 2 + 32 * k) -> x28 = Z_to_bv 64 (16 * k) ->
    x12 = Z_to_bv 64 (rep_val b nb) -> Z.of_nat j = len / 16 - k -> 0 <= k < len / 16 ->
    INV m1 (updc cells0 (seq (Z.to_nat V) (Z.to_nat (16 * k))) C) -> rw_cells usegs m1 (SP + -208) FRC ->
    (forall m2 (y7 y8 y11 y12 y22 y23 y25 y26 y27 y28 y30 y31 : word),
       INV m2 (updc cells0 (seq (Z.to_nat V) (Z.to_nat len)) C) -> rw_cells usegs m2 (SP + -208) FRC ->
       evt usegs POST (MS (mkR (Z_to_bv 64 len) (Z_to_bv 64 (SP + -240)) gp tp x5 x6 y7 y8 (Z_to_bv 64 (-9)) x10 y11 y12
                               (Z_to_bv 64 SY) x14 x15 (Z_to_bv 64 (2^64 - 1 - SY)) x17 (Z_to_bv 64 (-17))
                               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 y22 y23 x24 y25 y26 y27 y28 x29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 2488)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 len) (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 x12
                            (Z_to_bv 64 SY) x14 x15 (Z_to_bv 64 (2^64 - 1 - SY)) x17 (Z_to_bv 64 (-17))
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 2296)) fc None m1 (seg_rom usegs)).
  Proof.
    induction j as [|j IH];
      intros k m1 x6 x7 x8 x11 x12 x22 x23 x25 x26 x27 x28 x30 x31
        X6 X7 X11 X28 X12 HJ HK IV FRm K; [lia|].
    subst x6 x7 x11 x28 x12.
    set (cl := updc cells0 (seq (Z.to_nat V) (Z.to_nat (16 * k))) C) in *.
    destruct IV as (ARR & LC & SYB & MU & WM & MI).
    assert (L16 : 16 * (k + 1) <= len) by (Z.div_mod_to_equations; lia).
    set (U := (Z.to_nat V + Z.to_nat (16 * k))%nat).
    assert (HUz : Z.of_nat U = V + 16 * k) by (unfold U; lia).
    pose proof (omerge_length syms js) as OML.
    x1k_le1 b nb HB HNB.
    unfold x1_fr in FRm. unfold PHUF_RDT_X1.
    x1k_walk. x1w_zbr.
    xc (DT + 4) ARR U 2. xc (DT + 4) ARR U 3. xc (DT + 4) ARR U 0. xc (DT + 4) ARR U 1.
    x1k_walk; x1w_zbr. xc (DT + 4) ARR U 6. xc (DT + 4) ARR U 7. xc (DT + 4) ARR U 4. xc (DT + 4) ARR U 5.
    x1k_walk; x1w_zbr. xc (DT + 4) ARR U 10. xc (DT + 4) ARR U 11. xc (DT + 4) ARR U 8. xc (DT + 4) ARR U 9.
    x1k_walk; x1w_zbr. xc (DT + 4) ARR U 14. xc (DT + 4) ARR U 15. xc (DT + 4) ARR U 12. xc (DT + 4) ARR U 13.
    rewrite upd16_mach in ARR by lia. unfold U, cl in ARR. rewrite <- updc_seq_add in ARR.
    replace (Z.to_nat (16 * k) + 16)%nat with (Z.to_nat (16 * (k + 1))) in ARR by lia.
    x1k_walk. x1w_zbr. x1w_norm. x1w_br BI.
    - eapply (IH (k + 1) _).
      all: try (f_equal; lia).
      all: try reflexivity.
      all: try (Z.div_mod_to_equations; lia).
      all: lazymatch goal with
           | |- x1w_inv _ _ _ _ _ _ _ _ _ _ =>
               unfold x1w_inv; split; [assumption|split; [rewrite updc_length; exact LC0|split; [assumption|split; [assumption|split; assumption]]]]
           | |- rw_cells _ _ _ _ => exact FRm
           | _ => exact K
           end.
    - assert (EK : 16 * (k + 1) = len) by lia. rewrite EK in ARR.
      eapply K.
      + unfold x1w_inv; split; [assumption|split; [rewrite updc_length; exact LC0|split; [assumption|split; [assumption|split; assumption]]]].
      + exact FRm.
  Qed.
End F16I.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section F16O.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (WK DT SY tl w cnt sym0 len nb u0 : Z) (syms : list (option Z)) (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Notation SP := (bv_unsigned sp).
  Hypothesis HJT : length jt = (2 * ncells)%nat.
  Hypothesis HJS : length js = length syms.
  Hypothesis LSY : length syms = 256%nat.
  Hypothesis HNC : Z.of_nat ncells <= 8192.
  Hypothesis HSYR : forall i v, nth i syms None = Some v -> 0 <= v < 256.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HLEN : 16 <= len <= 2048 /\ len mod 16 = 0.
  Hypothesis HCNT : 0 < cnt <= 256.
  Hypothesis HSYM : 0 <= sym0 /\ sym0 + cnt <= 256.
  Hypothesis HU0 : 0 <= u0 /\ u0 + cnt * len <= Z.of_nat ncells.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 2 * Z.of_nat ncells <= 2^47.
  Hypothesis HSY : 0 < SY /\ SY + Z.of_nat (length js) <= 2^47.
  Hypothesis DJ : DT + 4 + 2 * Z.of_nat ncells <= SY \/ SY + Z.of_nat (length js) <= DT + 4.
  Hypothesis HSP : 240 <= SP /\ SP <= 2^47.
  Hypothesis DSD : DT + 4 + 2 * Z.of_nat ncells <= SP + -240 \/ SP <= DT + 4.
  Hypothesis DSS : SY + Z.of_nat (length js) <= SP + -240 \/ SP <= SY.
  Notation INV m1 cells := (x1w_inv m m1 SP DT SY js jt syms ncells cells).
  Notation FRC := (x1_fr DT tl WK (Z_to_bv 64 u0) (Z_to_bv 64 sym0) (Z_to_bv 64 w) (Z_to_bv 64 cnt)).

  Lemma f16_out : forall f s cells m1 r
      (x5 x6 x7 x8 x10 x11 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    x5 = Z_to_bv 64 sym0 -> x10 = Z_to_bv 64 (DT + 20 + (u0 + s * len) * 2) -> x14 = Z_to_bv 64 (len * 2) ->
    x15 = Z_to_bv 64 (u0 + s * len) -> x17 = Z_to_bv 64 s -> x21 = Z_to_bv 64 cnt -> x24 = Z_to_bv 64 nb ->
    x29 = Z_to_bv 64 (256 - sym0) ->
    fill_syms f s cnt sym0 len nb syms cells (u0 + s * len) = Ok r ->
    Z.of_nat f = cnt - s + 1 -> 0 <= s < cnt -> INV m1 cells -> rw_cells usegs m1 (SP + -208) FRC ->
    (forall m2 cells' (y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       r = (cells', u0 + cnt * len) -> INV m2 cells' -> rw_cells usegs m2 (SP + -208) FRC ->
       evt usegs POST (MS (mkR (Z_to_bv 64 len) (Z_to_bv 64 (SP + -240)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (-9))
                               y10 y11 y12 (Z_to_bv 64 SY) y14 y15 (Z_to_bv 64 (2^64 - 1 - SY)) y17 (Z_to_bv 64 (-17))
                               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 2912)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 len) (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 x12
                            (Z_to_bv 64 SY) x14 x15 (Z_to_bv 64 (2^64 - 1 - SY)) x17 (Z_to_bv 64 (-17))
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 2212)) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH];
      intros s cells m1 r x5 x6 x7 x8 x10 x11 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
        X5 X10 X14 X15 X17 X21 X24 X29 FS HF HS IV FRm K; [lia|].
    subst x5 x10 x14 x15 x17 x21 x24 x29.
    pose proof (fill_syms_ok _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as (LR & SR & BR).
    specialize (BR ltac:(lia)).
    assert (SL0 : 0 <= s * len) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SL1 : (s + 1) * len <= cnt * len) by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite fill_syms_step in FS by lia.
    destruct (oload syms (sym0 + s)) as [b| | |] eqn:OL; cbn [bind] in FS; try discriminate.
    destruct (fill_cells (Z.to_nat len) cells (u0 + s * len) (mkX1 nb b)) as [cells1| | |] eqn:FC; cbn [bind] in FS;
      try discriminate.
    apply oload_Ok in OL. destruct OL as [OLR OLN].
    pose proof (HSYR _ _ OLN) as HB.
    pose proof IV as IV0.
    destruct IV as (ARR & LC & SYB & MU & WM & MI).
    pose proof (omerge_nth syms js _ _ HJS OLN) as ON.
    pose proof (bytes_at_read usegs _ _ _ (sym0 + s) 1 SYB ltac:(lia) ltac:(rewrite omerge_length; lia)) as SRD.
    rewrite (x1k_rd1 _ _ _ ON) in SRD.
    pose proof (fill_cells_updc _ _ _ _ _ FC ltac:(lia)) as FC2.
    pose proof (omerge_length syms js) as OML.
    unfold x1_fr in FRm. unfold PHUF_RDT_X1.
    x1g_to 2296.
    rewrite (x1k_rv b nb) by lia.
    eapply f16_in with (j := Z.to_nat (len / 16)) (k := 0) (m := m) (WK := WK) (DT := DT) (SY := SY) (tl := tl)
      (V := u0 + s * len) (len := len) (b := b) (nb := nb) (syms := syms) (js := js) (jt := jt) (ncells := ncells)
      (cells0 := cells) (cu := Z_to_bv 64 u0) (cs := Z_to_bv 64 sym0) (cw := Z_to_bv 64 w) (cc := Z_to_bv 64 cnt).
    all: lazymatch goal with
         | |- @eq (bv 64) _ _ => first [ reflexivity | (x1k_nzg; rewrite ?zb_lxor_ones by lia; x1k_nzg; f_equal; x1k_nzg; lia) ]
         | |- x1w_inv _ _ _ _ _ _ _ _ _ _ => exact IV0
         | |- rw_cells _ _ _ _ => exact FRm
         | |- forall _, _ => idtac
         | |- length _ = _ => assumption
         | |- _ => first [ lia | (Z.div_mod_to_equations; lia) ]
         end.
    intros m2 y7 y8 y11 y12 y22 y23 y25 y26 y27 y28 y30 y31 IV2 FR2.
    rewrite <- FC2 in IV2. clear ARR LC SYB MU WM MI.
    x1k_walk. x1w_zbr. x1w_norm. x1w_br BO.
    - eapply (IH (s + 1) cells1 _ r).
      all: lazymatch goal with
           | |- @eq (bv 64) _ _ => first [ reflexivity | (f_equal; lia) | (x1k_nzg; f_equal; x1k_nzg; lia) ]
           | |- fill_syms _ _ _ _ _ _ _ _ _ = _ => rewrite <- FS; f_equal; lia
           | |- x1w_inv _ _ _ _ _ _ _ _ _ _ => exact IV2
           | |- rw_cells _ _ _ _ => exact FR2
           | |- forall _, _ => exact K
           | |- _ => lia
           end.
    - x1k_walk. x1w_zbr.
      destruct f as [|f]; [lia|]. rewrite fill_syms_stop in FS by lia. injection FS as FS.
      eapply K; [ rewrite <- FS; f_equal; lia | exact IV2 | exact FR2 ].
  Qed.
End F16O.

(* [comment removed for export] *)
Lemma f16_cls : x1cls_stmt (PHUF_RDT_X1 + 2132) (fun len => 16 <= len <= 2048).
Proof.
  intros sp gp tp F fc x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m m1 WK DT SY tl w cnt len nb u sym syms js jt ncells cells r POST
    PL HW HLEN HNB FS HCNT HU HSYM HJT HJS LSY HNC HSYR HDT0 HDT1 HSY0 HSY1 DJ HSP0 HSP1 DSD DSS FRm IV K.
  assert (HW5 : 5 <= w).
  { destruct (Z.le_gt_cases 5 w) as [?|Hlt]; [assumption|].
    assert (2^(w-1) <= 2^3) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (LM : len mod 16 = 0).
  { rewrite HLEN. replace (w - 1) with ((w - 5) + 4) by lia. rewrite Z.pow_add_r by lia.
    change (2^4) with 16. apply Z.mod_mul. lia. }
  pose proof (fill_syms_ok _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as (LR & SR & BR).
  assert (LC : length cells = ncells) by (destruct IV as (_ & LC & _); exact LC).
  unfold x1_fr in FRm. unfold PHUF_RDT_X1.
  destruct (Z.eq_dec cnt 0) as [C0|CP].
  - subst cnt.
    x1k_walk. x1w_zbr.
    rewrite fill_syms_stop in FS by lia. injection FS as <-.
    eapply (K m1 cells); [ f_equal; lia | exact IV | exact FRm ].
  - specialize (BR ltac:(lia)).
    pose proof (fill_syms_sym _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as SYR.
    assert (LCL : len <= cnt * len) by (rewrite <- (Z.mul_1_l len) at 1; apply Z.mul_le_mono_nonneg_r; lia).
    x1k_walk. x1w_zbr. x1w_norm. x1w_br B0; [ exfalso; lia | ].
    x1k_rd4at FRm 48%nat (Z_to_bv 64 (bv_unsigned sp + -160)).
    x1g_to 2212.
    eapply f16_out with (f := S (Z.to_nat cnt)) (s := 0) (cells := cells) (m1 := m1) (r := r) (m := m) (WK := WK)
      (DT := DT) (SY := SY) (tl := tl) (w := w) (cnt := cnt) (sym0 := sym) (len := len) (nb := nb) (u0 := u)
      (syms := syms) (js := js) (jt := jt) (ncells := ncells).
    all: lazymatch goal with
         | |- @eq (bv 64) _ _ =>
             first [ reflexivity | (rewrite ?x1k_lx63 by lia; x1k_nzg; f_equal; x1k_nzg; lia) ]
         | |- fill_syms _ _ _ _ _ _ _ _ _ = _ => rewrite Z.mul_0_l, Z.add_0_r; exact FS
         | |- x1w_inv _ _ _ _ _ _ _ _ _ _ => exact IV
         | |- rw_cells _ _ _ _ => exact FRm
         | |- forall _ : fmem, _ => exact K
         | |- forall _, _ => assumption
         | |- length _ = _ => assumption
         | |- _ => first [ lia | assumption ]
         end.
Qed.
