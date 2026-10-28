(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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

Section F1.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (WK DT SY tl cnt sym u nb : Z) (syms : list (option Z)) (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Notation SP := (bv_unsigned sp).
  Hypothesis HJT : length jt = (2 * ncells)%nat.
  Hypothesis HJS : length js = length syms.
  Hypothesis LSY : length syms = 256%nat.
  Hypothesis HSYR : forall i v, nth i syms None = Some v -> 0 <= v < 256.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HCNT : 0 < cnt <= 256.
  Hypothesis HU : 0 <= u.
  Hypothesis HSYM : 0 <= sym <= 256.
  Hypothesis HNC : Z.of_nat ncells <= 8192.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 2 * Z.of_nat ncells <= 2^47.
  Hypothesis HSY : 0 < SY /\ SY + Z.of_nat (length js) <= 2^47.
  Hypothesis DJ : DT + 4 + 2 * Z.of_nat ncells <= SY \/ SY + Z.of_nat (length js) <= DT + 4.
  Hypothesis HSP : 240 <= SP <= 2^47.
  Hypothesis DSD : DT + 4 + 2 * Z.of_nat ncells <= SP + -240 \/ SP <= DT + 4.
  Hypothesis DSS : SY + Z.of_nat (length js) <= SP + -240 \/ SP <= SY.
  Notation FR := (x1_fr DT tl WK (Z_to_bv 64 u) (Z_to_bv 64 sym) (Z_to_bv 64 1) (Z_to_bv 64 cnt)).
  Notation INV m1 cells := (x1w_inv m m1 SP DT SY js jt syms ncells cells).

  Lemma f1_inner : forall k s cells m1 r (x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (a5 a6 a10 a12 a14 a15 a16 a17 : Z),
    a5 = (256 - sym) * 2 -> a6 = cnt * 2 -> a10 = 2 * s -> a12 = sym + s -> a14 = u + s -> a15 = DT + 4 + 2 * u ->
    a16 = 2^64 - 1 - SY -> a17 = 2^32 - 2 - 2 * u ->
    Z.of_nat k = cnt - s -> 0 <= s < cnt ->
    fill_syms (S k) s cnt sym 1 nb syms cells (u + s) = Ok r ->
    INV m1 cells -> rw_cells usegs m1 (SP + -208) FR ->
    (forall m2 cells' (y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       r = (cells', u + cnt * 1) -> INV m2 cells' -> rw_cells usegs m2 (SP + -208) FR ->
       evt usegs POST (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (SP + -240)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (-9))
                               y10 y11 y12 (Z_to_bv 64 SY) y14 y15 (Z_to_bv 64 (2^64 - 1 - SY)) y17 (Z_to_bv 64 (-17))
                               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 2912)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (SP + -240)) gp tp (Z_to_bv 64 a5) (Z_to_bv 64 a6) x7 x8
                            (Z_to_bv 64 (-9)) (Z_to_bv 64 a10) (Z_to_bv 64 nb) (Z_to_bv 64 a12) (Z_to_bv 64 SY)
                            (Z_to_bv 64 a14) (Z_to_bv 64 a15) (Z_to_bv 64 a16) (Z_to_bv 64 a17) (Z_to_bv 64 (-17))
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 2616)) fc None m1 (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros s cells m1 r x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      a5 a6 a10 a12 a14 a15 a16 a17 E5 E6 E10 E12 E14 E15 E16 E17 HK HS FS INV FRM KC; [lia|].
    subst a5 a6 a10 a12 a14 a15 a16 a17.
    pose proof (fill_syms_sym _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as SYB.
    rewrite fill_syms_step in FS by lia.
    destruct (oload syms (sym + s)) as [b|e| |] eqn:OL; cbn [bind] in FS; try discriminate.
    destruct (fill_cells (Z.to_nat 1) cells (u + s) (mkX1 nb b)) as [cells1|e| |] eqn:FC; cbn [bind] in FS;
      try discriminate.
    apply oload_Ok in OL. destruct OL as [OLR OLN].
    pose proof (HSYR _ _ OLN) as HB.
    destruct (fill_cells_ok _ _ _ _ _ FC) as [LC1 RC1]. specialize (RC1 ltac:(cbn; lia)).
    apply fill_cells_updc in FC; [|lia].
    destruct INV as (DTA & LC & SYA & MU & WM & MI).
    pose proof (x1k_syrd m1 SY js syms (sym + s) b SYA HJS ltac:(lia) OLN) as RDS.
    unfold x1_fr in FRM. unfold PHUF_RDT_X1.
    pose proof (omerge_length syms js) as LOM.
    x1k_to 2660. cbv beta. rewrite (x1k_u8 b) by lia.
    xb (DT + 4) DTA (2 * (u + s)).
    xb (DT + 4) DTA (2 * (u + s) + 1).
    x1k_wlk. x1k_zb. x1k_nm.
    replace (Z.to_nat (2 * (u + s))) with (2 * Z.to_nat (u + s))%nat in DTA by lia.
    replace (Z.to_nat (2 * (u + s) + 1)) with (2 * Z.to_nat (u + s) + 1)%nat in DTA by lia.
    rewrite ox1_store' in DTA by lia.
    change (Z.to_nat 1) with 1%nat in FC. unfold updc in FC. cbn [seq fold_left] in FC.
    rewrite <- FC in DTA.

    let U := fresh "U" in if_cases U; zify_cond U.
    -
      eapply IH with (s := s + 1) (cells := cells1) (r := r).
      all: first [ lia
                 | (replace (u + (s + 1)) with (u + s + 1) by lia; exact FS)
                 | exact KC
                 | exact FRM
                 | (unfold x1w_inv; refine (conj DTA (conj _ (conj SYA (conj MU (conj WM MI))))); lia) ].
    -
      x1k_to 2912.
      rewrite fill_syms_stop in FS by lia. injection FS as <-.
      eapply (KC _ cells1).
      all: first [ (f_equal; lia)
                 | exact FRM
                 | (unfold x1w_inv; refine (conj DTA (conj _ (conj SYA (conj MU (conj WM MI))))); lia) ].
  Qed.
End F1.

(* [comment removed for export] *)
Lemma f1_cls : x1cls_stmt (PHUF_RDT_X1 + 2524) (fun len => len = 1).
Proof.
  intros sp gp tp F fc x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m m1 WK DT SY tl w cnt len nb u sym syms js jt ncells cells r POST
    HL HW HLEN HNB FS HCNT HU HSYM HJT HJS LSY HNC HSYR HDT0 HDT1 HSY0 HSY1 DJ HSP0 HSP1 DSD DSS FRM INV KC.
  subst len.
  assert (W1 : w = 1).
  { destruct (Z.eq_dec w 1) as [->|N1]; [reflexivity|]. exfalso.
    assert (2^1 <= 2^(w-1)) by (apply Z.pow_le_mono_r; lia). lia. }
  subst w.
  unfold x1_fr in FRM. unfold PHUF_RDT_X1.
  x1k_to 2616.
  let U := fresh "U" in if_cases U; zify_cond U.
  -
    assert (cnt = 0) by lia. subst cnt.
    rewrite fill_syms_stop in FS by lia. injection FS as <-.
    eapply (KC _ cells).
    all: first [ (f_equal; lia) | exact FRM | exact INV ].
  -
    destruct (fill_syms_ok _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as (FL1 & FL2 & FL3).
    specialize (FL3 ltac:(lia)). pose proof (proj1 (proj2 INV)) as LC.
    x1k_to 2616. x1k_nm. rewrite x1k_lxm31 by lia. x1k_nm.
    eapply f1_inner with (m := m) (WK := WK) (tl := tl) (cnt := cnt) (sym := sym) (u := u) (syms := syms) (js := js) (jt := jt)
      (ncells := ncells) (cells := cells) (k := Z.to_nat cnt) (s := 0) (r := r).
    all: first [ lia | eassumption | (replace (u + 0) with u by lia; exact FS) | exact FRM | exact KC ].
Qed.
