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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4f_defs AF_huf_z4kx.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  Notation KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y1 y5 y6 y16 y17 y18 y19 y25 : word) (w'0 w'1 w'2 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 w'1 w'2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        (LOC mm' e0 e1 e2 e3 (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) c0' c1' c2' c3') -> bytes_at bsegs mm' SRC src ->
        i0 - 7 <= i0' <= i0 -> i1 - 7 <= i1' <= i1 -> i2 - 7 <= i2' <= i2 -> i3 - 7 <= i3' <= i3 ->
        o0 + 5 <= o0' <= o0 + 10 -> o1 + 5 <= o1' <= o1 + 10 -> o2 + 5 <= o2' <= o2 + 10 -> o3 + 5 <= o3' <= o3 + 10 ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' -> o3' < OL -> (2 <= r)%nat ->
        evtF bsegs RNG POST (ST 0x853d4 mm' y1 y5 y6 (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0' (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) y16 y17 y18 y19 c3' (Z_to_bv 64 (SPV + -168)) c1' SB c2' y25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i0')))).
  Notation KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y1 y7 y18 y19 y20 y22 y24 y25 y28 y29 y30 y31 : word) (w'0 w'1 w'2 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 w'1 w'2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        (LOC mm' e0 e1 e2 e3 (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) c0' c1' c2' c3') -> bytes_at bsegs mm' SRC src ->
        i0 - 7 <= i0' <= i0 -> i1 - 7 <= i1' <= i1 -> i2 - 7 <= i2' <= i2 -> i3 - 7 <= i3' <= i3 ->
        o0 + 5 <= o0' <= o0 + 10 -> o1 + 5 <= o1' <= o1 + 10 -> o2 + 5 <= o2' <= o2 + 10 -> o3 + 5 <= o3' <= o3 + 10 ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' -> OL <= o3' ->
        evtF bsegs RNG POST (ST 0x85278 mm' y1 (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) y7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0' (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) y18 y19 y20 (Z_to_bv 64 (SPV + -168)) y22 SB y24 y25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) y28 y29 y30 y31)).

  Notation STMT11 := (x42e_fi11_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST).
  Notation STMT12 := (x42e_fi12_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST).
  Hypothesis FI12 : STMT12.
  Notation z4fI := (AF_huf_z4f_defs.z4fI m0 SPV DST dcap SRC DT src dtb).

  Lemma z4f11_bvm : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
  Proof.
    intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. exact H.
  Qed.

  Lemma x42e_fi11 : STMT11.
  Proof using CTX X2OK NBOK ACTX TL11 FI12.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi11_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 j1 j2 ix c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x7 x18 x19 x25 x31 w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBY FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HU3 HJ0 HJ1 HJ2 HIX HLBc0 HLBc1 HLBc2 HLBc3 KH KO.
    subst nd.
    rewrite TL11 in DTBF. change (2 ^ 11) with 2048 in DTBF.
    assert (DPOS : 0 < dcap) by lia.
    specialize (DHI DPOS).
    assert (TB : ztab_fact bsegs mm (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)])
      by exact (x42f_tab SPV DST dcap SRC n DT DTB tl lo src dtb CTX X2OK NBOK TL11 mm DTBY).
    assert (UDTm : unpoisoned mm DT (DT + DTB)).
    { eapply unpoisoned_munch; [exact UDT | exact MU0 |]. cbn [disjoint_from]. rewrite !shad_div.
      unfold ASHOFF, ABase.AIMG_HI in *. lia. }
    assert (UDSTm : unpoisoned mm DST (DST + dcap)).
    { eapply unpoisoned_munch; [exact (UDST DPOS) | exact MU0 |]. cbn [disjoint_from]. rewrite !shad_div.
      unfold ASHOFF, ABase.AIMG_HI in *. lia. }
    pose proof (RDST DPOS) as RDSTc. pose proof (RDSTS DPOS) as RDSTSc.
    unfold shspan in RDTS, RDSTSc, RSRCS.
    assert (RW3 : rng RNG (DST + u3) 2) by (eapply rng_sub; [exact RDSTc | lia | lia]).
    assert (RLC : rng RNG (SPV + -232) 128) by (eapply rng_sub; [exact RSTK | lia | lia]).
    assert (RTB : rng RNG (DT + 4) 8192) by (eapply rng_sub; [exact RDT | lia | lia]).
    assert (WAD : wr_at bsegs mm DST dcap).
    { destruct OUT as (OUT1 & OUT2 & OUT3). split; [lia | split; [lia |]]. intros i Hi.
      exact (proj1 (OUT3 (DST + i) ltac:(lia))). }
    replace (Z_to_bv 64 (-1 * DT + -5)) with (Z_to_bv 64 (18446744073709551611 - DT))
      by (apply z4f11_bvm; change (2^64) with 18446744073709551616;
          rewrite <- (Z_mod_plus_full (-1 * DT + -5) 1); f_equal; lia).
    remember (18446744073709551611 - DT) as ND eqn:HNDe.
    assert (NDR : 18446603336221204480 <= ND <= 18446744073709547515) by lia.
    kx_runFm [550236] 120%nat
      [KZRange SPV 7232 (2^47 - 16); KZRange DT 4096 (2^47 - 8197); KZAlign DT 4; KZRange DST 4096 (2^47 - 1);
       KZRange SRC 4096 (2^47 - 1); KZRange ND 18446603336221204480 18446744073709547515; KZRange ix 0 2047;
       KZRange u3 0 (2^32); KZRange (DST + u3) 4096 (2^47 - 2);
       KZTab (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)];
       KZWr (DST + u3) 2; KZWr (SPV + -232) 128;
       KZDisj (DST + u3) 2 (DT + 4) 8192; KZDisj (SPV + -232) 128 (DT + 4) 8192; KZDisj (DST + u3) 2 (SPV + -232) 128]
      [(DT + 4, 8192)]
      [(DST + u3, 2); (SPV + -232, 128)]
      [(DT + 4, 8192); (DST + u3, 2)].
    all: try (lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; apply (proj2 (proj2 RTB)); lia end).
    kx_post_regs_keep.
    (repeat match goal with |- context [bv_unsigned (ev ?E ?j)] =>
      lazymatch goal with _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail | _ =>
        let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H end end).
    (replace (Z_to_bv 64 ND) with (Z_to_bv 64 (-1 * DT + -5))
      by (subst ND; apply z4f11_bvm; change (2^64) with 18446744073709551616;
          rewrite <- (Z_mod_plus_full (-1 * DT + -5) 1); f_equal; lia)).
    (lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; z4fan E end).
    (lazymatch goal with FRh : rw_cells _ mm (SPV + -528) ?fr, ARh : rw_cells _ mm (SPV + -384) ?ar, LCh : rw_cells _ mm (SPV + -232) ?cs |- _ =>
      assert (I0 : z4fI mb mm fr ar cs) by (unfold z4fI; z4fsplit 12%nat; first [eassumption | reflexivity]) end).
    (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => z4fmem M end).
    lazymatch goal with I0 : z4fI _ ?M ?fr ?ar ?cs |- _ =>
      destruct I0 as (MU' & WM' & MU0' & WM0' & MI' & STK' & DTB' & SRC' & FR' & AR' & LC' & LFR' & LAR') end.
    rewrite ?Z_to_bv_bv_unsigned in *.
    eapply (FI12 r mb _ q OL (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 _ j0 j1 j2 c0 c1 c2 _ e0 e1 e2 e3
              av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 _ _ _ _ _ _ _ w0 w1 w2).
    all: try eassumption.
    all: try reflexivity.
    all: try (lazymatch goal with |- LBW _ (edenot (kE ?zv ?xs) _) => e42_lb_chain (kE_atoms zv xs) end).
    all: lazymatch goal with |- _ <= _ + bv_unsigned (ev ?E ?j) <= _ =>
      match goal with H : _ <= bv_unsigned (ev E j) <= _ |- _ => clear - H HU3; lia end end.
  Qed.
End X42E.
End CANSEC1.
