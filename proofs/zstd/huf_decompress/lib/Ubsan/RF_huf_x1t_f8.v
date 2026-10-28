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

Lemma f8_upd8 : forall l U c, (U + 8 <= length l)%nat ->
  upd (upd (upd (upd (upd (upd (upd (upd l
    (U + Z.to_nat 2) (Some c)) (U + Z.to_nat 3) (Some c)) (U + Z.to_nat 0) (Some c)) (U + Z.to_nat 1) (Some c))
    (U + Z.to_nat 6) (Some c)) (U + Z.to_nat 7) (Some c)) (U + Z.to_nat 4) (Some c)) (U + Z.to_nat 5) (Some c)
  = updc l (seq U 8) c.
Proof.
  intros l U c H.
  change (updc l [(U + Z.to_nat 2)%nat; (U + Z.to_nat 3)%nat; (U + Z.to_nat 0)%nat; (U + Z.to_nat 1)%nat;
                  (U + Z.to_nat 6)%nat; (U + Z.to_nat 7)%nat; (U + Z.to_nat 4)%nat; (U + Z.to_nat 5)%nat] c
          = updc l (seq U 8) c).
  apply updc_perm.
  - intros j [Hj|Hj]; [ cbn in Hj | rewrite in_seq in Hj ]; lia.
  - intros i. rewrite in_seq. cbn. lia.
Qed.

Section F8.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (WK DT SY tl cnt sym0 nb u0 : Z) (syms : list (option Z)) (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Notation SP := (bv_unsigned sp).
  Hypothesis HJT : length jt = (2 * ncells)%nat.
  Hypothesis HJS : length js = length syms.
  Hypothesis LSY : length syms = 256%nat.
  Hypothesis HNC : Z.of_nat ncells <= 8192.
  Hypothesis HSYR : forall i v, nth i syms None = Some v -> 0 <= v < 256.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HCNT : 0 < cnt <= 256.
  Hypothesis HSYM : 0 <= sym0 /\ sym0 + cnt <= 256.
  Hypothesis HU0 : 0 <= u0 /\ u0 + 8 * cnt <= Z.of_nat ncells.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 2 * Z.of_nat ncells <= 2^47.
  Hypothesis HSY : 0 < SY /\ SY + Z.of_nat (length js) <= 2^47.
  Hypothesis DJ : DT + 4 + 2 * Z.of_nat ncells <= SY \/ SY + Z.of_nat (length js) <= DT + 4.
  Hypothesis HSP : 240 <= SP /\ SP <= 2^47.
  Hypothesis DSD : DT + 4 + 2 * Z.of_nat ncells <= SP + -240 \/ SP <= DT + 4.
  Hypothesis DSS : SY + Z.of_nat (length js) <= SP + -240 \/ SP <= SY.
  Notation INV m1 cells := (x1w_inv m m1 SP DT SY js jt syms ncells cells).
  Notation FRC := (x1_fr DT tl WK (Z_to_bv 64 u0) (Z_to_bv 64 sym0) (Z_to_bv 64 4) (Z_to_bv 64 cnt)).

  Lemma f8_inner : forall f s cells m1 r
      (x5 x6 x7 x8 x10 x11 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    x5 = Z_to_bv 64 (cnt * 16) -> x6 = Z_to_bv 64 (DT + 4 + u0 * 2) -> x10 = Z_to_bv 64 (16 * s) ->
    x11 = Z_to_bv 64 (sym0 + s) -> x12 = Z_to_bv 64 (DT + u0 * 2) -> x14 = Z_to_bv 64 ((256 - sym0) * 16) ->
    x15 = Z_to_bv 64 (u0 + 8 * s) -> x17 = Z_to_bv 64 nb ->
    fill_syms f s cnt sym0 8 nb syms cells (u0 + 8 * s) = Ok r ->
    Z.of_nat f = cnt - s + 1 -> 0 <= s < cnt -> INV m1 cells -> rw_cells usegs m1 (SP + -208) FRC ->
    (forall m2 cells' (y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       r = (cells', u0 + cnt * 8) -> INV m2 cells' -> rw_cells usegs m2 (SP + -208) FRC ->
       evt usegs POST (MS (mkR (Z_to_bv 64 8) (Z_to_bv 64 (SP + -240)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (-9))
                               y10 y11 y12 (Z_to_bv 64 SY) y14 y15 (Z_to_bv 64 (2^64 - 1 - SY)) y17 (Z_to_bv 64 (-17))
                               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 2912)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 8) (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 x12
                            (Z_to_bv 64 SY) x14 x15 (Z_to_bv 64 (2^64 - 1 - SY)) x17 (Z_to_bv 64 (-17))
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 1936)) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH];
      intros s cells m1 r x5 x6 x7 x8 x10 x11 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
        X5 X6 X10 X11 X12 X14 X15 X17 FS HF HS IV FRm K; [lia|].
    subst x5 x6 x10 x11 x12 x14 x15 x17.
    pose proof (fill_syms_ok _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as (LR & SR & BR).
    specialize (BR ltac:(lia)).
    rewrite fill_syms_step in FS by lia.
    destruct (oload syms (sym0 + s)) as [b| | |] eqn:OL; cbn [bind] in FS; try discriminate.
    destruct (fill_cells (Z.to_nat 8) cells (u0 + 8 * s) (mkX1 nb b)) as [cells1| | |] eqn:FC; cbn [bind] in FS; try discriminate.
    apply oload_Ok in OL. destruct OL as [OLR OLN].
    pose proof (HSYR _ _ OLN) as HB.
    destruct IV as (ARR & LC & SYB & MU & WM & MI).
    pose proof (omerge_nth syms js _ _ HJS OLN) as ON.
    pose proof (bytes_at_read usegs _ _ _ (sym0 + s) 1 SYB ltac:(lia) ltac:(rewrite omerge_length; lia)) as SRD.
    rewrite (x1k_rd1 _ _ _ ON) in SRD.
    set (U := Z.to_nat (u0 + 8 * s)).
    assert (HUz : Z.of_nat U = u0 + 8 * s) by (unfold U; lia).
    pose proof (fill_cells_updc _ _ _ _ _ FC ltac:(lia)) as FC2. change (Z.to_nat 8) with 8%nat in FC2. fold U in FC2.
    pose proof (omerge_length syms js) as OML.
    unfold x1_fr in FRm. unfold PHUF_RDT_X1.
    x1k_walk. x1w_zbr. x1w_norm.
    rewrite (x1k_rv b nb) by lia.
    assert (NB : 0 <= nb < 16) by lia. assert (HB8 : 0 <= b < 256) by lia.
    x1k_le1 b nb HB8 NB.
    xc (DT + 4) ARR U 2. xc (DT + 4) ARR U 3. xc (DT + 4) ARR U 0. xc (DT + 4) ARR U 1.
    x1k_walk. x1w_zbr.
    xc (DT + 4) ARR U 6. xc (DT + 4) ARR U 7. x1w_zbr. xc (DT + 4) ARR U 4. xc (DT + 4) ARR U 5.
    rewrite f8_upd8 in ARR by (rewrite LC; lia). rewrite <- FC2 in ARR.
    assert (LC1 : length cells1 = ncells) by (rewrite FC2, updc_length; exact LC).
    x1k_walk. x1w_zbr. x1w_norm. x1w_br BE.
    - eapply (IH (s + 1) cells1 _ r).
      all: try (f_equal; lia).
      all: try lia.
      all: lazymatch goal with
           | |- fill_syms _ _ _ _ _ _ _ _ _ = _ => rewrite <- FS; f_equal; lia
           | |- x1w_inv _ _ _ _ _ _ _ _ _ _ =>
               unfold x1w_inv; split; [assumption|split; [assumption|split; [assumption|split; [assumption|split; assumption]]]]
           | |- rw_cells _ _ _ _ => exact FRm
           | _ => exact K
           end.
    - x1k_walk. x1w_zbr.
      destruct f as [|f]; [lia|]. rewrite fill_syms_stop in FS by lia. injection FS as FS.
      eapply K.
      + rewrite <- FS. f_equal. lia.
      + unfold x1w_inv; split; [assumption|split; [assumption|split; [assumption|split; [assumption|split; assumption]]]].
      + exact FRm.
  Qed.
End F8.

(* [comment removed for export] *)
Lemma f8_cls : x1cls_stmt (PHUF_RDT_X1 + 1856) (fun len => len = 8).
Proof.
  intros sp gp tp F fc x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m m1 WK DT SY tl w cnt len nb u sym syms js jt ncells cells r POST
    PL HW HLEN HNB FS HCNT HU HSYM HJT HJS LSY HNC HSYR HDT0 HDT1 HSY0 HSY1 DJ HSP0 HSP1 DSD DSS FRm IV K.
  subst len.
  assert (W4 : w = 4).
  { destruct (Z.lt_total w 4) as [Hl|[He|Hg]]; [ | exact He | ].
    - assert (2^(w-1) <= 2^2) by (apply Z.pow_le_mono_r; lia). lia.
    - assert (2^4 <= 2^(w-1)) by (apply Z.pow_le_mono_r; lia). lia. }
  subst w.
  pose proof (fill_syms_ok _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as (LR & SR & BR).
  assert (LC : length cells = ncells) by (destruct IV as (_ & LC & _); exact LC).
  unfold x1_fr in FRm. unfold PHUF_RDT_X1.
  destruct (Z.eq_dec cnt 0) as [C0|CP].
  - subst cnt.
    x1k_walk. x1w_zbr.
    rewrite fill_syms_stop in FS by lia. injection FS as <-.
    eapply (K m1 cells); [ f_equal; lia | exact IV | exact FRm ].
  - specialize (BR ltac:(lia)).
    x1k_walk. x1w_zbr. x1w_norm. x1w_br B0; [ exfalso; lia | ].
    x1k_rd4at FRm 48%nat (Z_to_bv 64 (bv_unsigned sp + -160)).
    pose proof (fill_syms_sym _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as SYR.
    x1w_zto 1936.
    eapply f8_inner with (f := S (Z.to_nat cnt)) (s := 0) (cells := cells) (m1 := m1) (r := r) (m := m) (WK := WK)
      (DT := DT) (SY := SY) (tl := tl) (cnt := cnt) (sym0 := sym) (nb := nb) (u0 := u) (syms := syms) (js := js) (jt := jt)
      (ncells := ncells).
    all: try (x1k_nzg; f_equal; x1k_nzg; first [ lia | Z.div_mod_to_equations; nia ]).
    all: try lia.
    all: try assumption.
    rewrite Z.mul_0_r, Z.add_0_r. exact FS.
Qed.
