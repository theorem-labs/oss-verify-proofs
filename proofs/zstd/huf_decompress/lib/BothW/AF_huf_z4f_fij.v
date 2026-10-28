(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4f_defs AF_huf_z4f_fi0 AF_huf_z4f_fi1 AF_huf_z4f_fi2 AF_huf_z4f_fi3 AF_huf_z4f_fi4 AF_huf_z4f_fi5 AF_huf_z4f_fi6 AF_huf_z4f_fi7 AF_huf_z4f_fi8 AF_huf_z4f_fi9 AF_huf_z4f_fi10 AF_huf_z4f_fi11 AF_huf_z4f_fi12.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.
Section X42E.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT DTB tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT DTB tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis ACTX : x42e_actx RNG m0 SPV DST dcap SRC n DT DTB lo.
  Variable POST : machine_state -> Prop.
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -528)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 :=
    (rw_cells bsegs mm (SPV + -528) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17]).
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -384) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation LOC mm e0 e1 e2 e3 p0 p1 p2 p3 i0 i1 i2 i3 c0 c1 c2 c3 :=
    (rw_cells bsegs mm (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3; C8 p0; C8 p1; C8 p2; C8 p3; C8 i0; C8 i1; C8 i2; C8 i3;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation WDF := [(DST, DST + dcap); (SPV - 528, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis TL11 : tl = 11.
  Notation WDL := [(DST, DST + dcap); (SPV - 232, SPV - 104)].

  Notation KOR mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y1 y7 y18 y19 y20 y22 y24 y25 y28 y29 y30 y31 : word) (w'0 w'1 w'2 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 w'1 w'2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        (LOC mm' e0 e1 e2 e3 (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) c0' c1' c2' c3') -> bytes_at bsegs mm' SRC src ->
        0 <= i0' <= i0 -> 0 <= i1' <= i1 -> 0 <= i2' <= i2 -> 0 <= i3' <= i3 ->
        o0 + 5 <= o0' <= q -> o1 + 5 <= o1' <= 2 * q -> o2 + 5 <= o2' <= 3 * q -> o3 + 5 <= o3' <= dcap -> OL <= o3' ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' ->
        evtF bsegs RNG POST (ST 0x85278 mm' y1 (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) y7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0' (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) y18 y19 y20 (Z_to_bv 64 (SPV + -168)) y22 SB y24 y25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) y28 y29 y30 y31)).

  Lemma x42e_body : x42e_fi0_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.
  Proof using CTX X2OK NBOK ACTX TL11.
    all: eapply x42e_fi0; try eassumption.
    all: eapply x42e_fi1; try eassumption.
    all: eapply x42e_fi2; try eassumption.
    all: eapply x42e_fi3; try eassumption.
    all: eapply x42e_fi4; try eassumption.
    all: eapply x42e_fi5; try eassumption.
    all: eapply x42e_fi6; try eassumption.
    all: eapply x42e_fi7; try eassumption.
    all: eapply x42e_fi8; try eassumption.
    all: eapply x42e_fi9; try eassumption.
    all: eapply x42e_fi10; try eassumption.
    all: eapply x42e_fi11; try eassumption.
    all: eapply x42e_fi12; try eassumption.
  Qed.

  Lemma x42e_fi : forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x5 x6 x16 x17 x18 x19 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    KOR mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x853d4 mm x1 x5 x6 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) x16 x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) c1 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).
  Proof using CTX X2OK NBOK ACTX TL11.
    induction r as [|r IH]; intros mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 x1 x5 x6 x16 x17 x18 x19 x25
      w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBH FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN HLB0 HLB1 HLB2 HLB3 KOR; [exfalso; clear - HR; lia|].
    eapply (x42e_body (S r) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3); try eassumption; try lia.
    -
      intros mm' i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
        intros MU' WM' MU0' WM0' MI' OUT' DTBH' FR' AR' LC' SRCB' HI0' HI1' HI2' HI3' HO0' HO1' HO2' HO3' HL0' HL1' HL2' HL3' HOL' HR2.
      eapply (IH mb mm' q OL nd l1 l2 l3 i0' i1' i2' i3' o0' o1' o2' o3'); try eassumption; try lia.
      intros mm'' i0'' i1'' i2'' i3'' o0'' o1'' o2'' o3'' c0'' c1'' c2'' c3''; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
        intros MU'' WM'' MU0'' WM0'' MI'' OUT'' DTBH'' FR'' AR'' LC'' SRCB'' GI0 GI1 GI2 GI3 GO0 GO1 GO2 GO3 GOL GL0 GL1 GL2 GL3.
      eapply (KOR mm'' i0'' i1'' i2'' i3'' o0'' o1'' o2'' o3''); try eassumption; lia.
    -
      intros mm' i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
        intros MU' WM' MU0' WM0' MI' OUT' DTBH' FR' AR' LC' SRCB' HI0' HI1' HI2' HI3' HO0' HO1' HO2' HO3' HL0' HL1' HL2' HL3' HOL'.
      eapply (KOR mm' i0' i1' i2' i3' o0' o1' o2' o3'); try eassumption; lia.
  Qed.

End X42E.
End CANSEC1.
