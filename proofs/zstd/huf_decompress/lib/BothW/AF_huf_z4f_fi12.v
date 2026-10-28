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

Lemma z4f12_br_nz : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAlu ALU_SRL B (ELit 3))) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64, u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (3 mod 64) with 3. change (2 ^ 3) with 8.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
    { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
      intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
  reflexivity.
Qed.

Ltac z4f12_br :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (EAlu ALU_SRL ?B (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = true =>
      apply (z4f12_br_nz E P B);
      [ let H := fresh "BR" in kx_erange H B; lia
      | z4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia ]
  end.

Ltac z4f12_acc_img R :=
  lazymatch goal with |- accP _ ?E ({| a_base := ?b; a_off := ?o |}, _) =>
    let H := fresh "AR" in kx_erange H b;
    unfold accP, adenot; cbn [a_base a_off fst snd]; unfold PropExec.v_addi;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
    rewrite (Z.mod_small (bv_unsigned (edenot E b) + o) (2 ^ 64)) by lia;
    apply (proj2 (proj2 R)); lia
  end.

Ltac z4f12_rd_img CT :=
  lazymatch goal with |- exists bs, rdn _ _ (adenot ?E {| a_base := ?b; a_off := ?o |}) _ = Some bs =>
    let H := fresh "AR" in kx_erange H b;
    unfold adenot; cbn [a_base a_off]; unfold PropExec.v_addi;
    let bb := fresh "bb" in let HB := fresh "HB" in
    destruct (CT (bv_unsigned (edenot E b) + o) ltac:(lia) 0 63 ltac:(rewrite Z.mod_1_r; reflexivity)) as (bb & HB & _);
    exists [bb]; exact HB
  end.

Tactic Notation "z4f12_runL" uconstr(STOPS) uconstr(FUEL) uconstr(DIRS) uconstr(KZS) uconstr(RRS) uconstr(WWS) uconstr(UWS) :=
  let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in let D := constr:(DIRS : list bool) in
  let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
  let U := constr:(UWS : list (Z * Z)) in
  kx_prepFm S Fu K R W U; kx_goFL D.

Ltac z4f12_rng :=
  repeat match goal with |- context [EVar ?j] =>
    lazymatch goal with _ : _ <= bv_unsigned (ev _ j) <= _ |- _ => fail | _ =>
      let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H end end.

Ltac z4f12_nb :=
  repeat match goal with |- context [(bv_unsigned (ev ?E ?j) mod 2 ^ 64) / 2 ^ (3 mod 64)] =>
    rewrite (Z.mod_small (bv_unsigned (ev E j)) (2 ^ 64)) by lia;
    change (2 ^ (3 mod 64)) with 8;
    let H := fresh "NB" in assert (H : 0 <= bv_unsigned (ev E j) / 8 <= 7) by (Z.div_mod_to_equations; lia);
    let v := fresh "nb" in set (v := bv_unsigned (ev E j) / 8) in *; clearbody v end.

Ltac z4f12_m64 :=
  rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
  repeat match goal with |- context [?a mod 2 ^ 64] =>
    lazymatch a with context [_ mod 2 ^ 64] => fail | _ => rewrite (Z.mod_small a (2 ^ 64)) by lia end end.

Ltac z4f12_accS R :=
  lazymatch goal with |- accP _ _ _ =>
    z4f12_rng; unfold accP, adenot; cbn [a_base a_off fst snd]; unfold PropExec.v_addi; z4fez;
    z4f12_nb; z4f12_m64; apply (proj2 (proj2 R)); lia
  end.

Ltac z4f12shd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit ?L)) /\ _ =>
      z4f12_rng; apply (z4f_shd_ap E X B O k L);
      [ z4fez; z4f12_nb; z4fnum; first [lia | Z.div_mod_to_equations; lia] | lia | lia | lia
      | z4fez; z4f12_nb; z4fnum; lia | z4fez; z4f12_nb; z4fnum; lia | z4fez; z4f12_nb; z4fnum; lia ]
  end.

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
  Notation z4fI := (AF_huf_z4f_defs.z4fI m0 SPV DST dcap SRC DT src dtb).
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

  Notation STMT12 := (x42e_fi12_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST).

  Lemma x42e_fi12 : STMT12.
  Proof using CTX X2OK NBOK ACTX TL11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi12_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 j1 j2 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x7 x18 x19 x25 x30 x31 w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBY FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HU3 HJ0 HJ1 HJ2 HLBc0 HLBc1 HLBc2 HLBc3 KH KO.
    subst nd.
    rewrite TL11 in DTBF. change (2 ^ 11) with 2048 in DTBF.
    assert (DPOS : 0 < dcap) by lia.
    specialize (DHI DPOS).
    assert (USRCm : unpoisoned mm SRC (SRC + n)).
    { eapply unpoisoned_munch; [exact USRC | exact MU0 |]. cbn [disjoint_from]. rewrite !shad_div.
      unfold ASHOFF, ABase.AIMG_HI in *. lia. }
    unfold shspan in RDTS, RSRCS.
    assert (RLC : rng RNG (SPV + -232) 128) by (eapply rng_sub; [exact RSTK | lia | lia]).
    pose proof (lbw_pos _ _ HLBc3) as HP3.
    assert (CTZ : ztab_fact bsegs mm 134483 64 1 [(0, 0, 63)]) by (apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity]).
    destruct (Z_lt_le_dec u3 OL) as [HC | HC].
    - z4f12_runL [545748; 545400] 200%nat [true]
        [KZRange SPV 7232 (2^47 - 16); KZRange DT 4096 (2^47 - 8197); KZRange DST 4096 (2^47 - 1);
         KZRange SRC 4096 (2^47 - 1); KZRange n 38 (2^32); KZRange i3 7 (2^32); KZRange (n - i3) 8 (2^32);
         KZRange (bv_unsigned c3) 1 (2^64 - 1); KZRange u3 0 (2^32); KZRange OL 0 (2^32); KZRange (OL - u3) 1 (2^32);
         KZTab 134483 64 1 [(0, 0, 63)];
         KZWr (SPV + -232) 128; KZDisj (SPV + -232) 128 SRC n]
        [(SRC, n)] [(SPV + -232, 128)] [(SRC, n)].
      all: try z4f12_br.
      all: try z4f12_rd_img CTZ.
      all: try z4f12_acc_img RI.
      all: try z4f12shd.
      all: try z4f12_accS RSRC.
      kx_post_regs_keep.
      repeat match goal with |- context [bv_unsigned (ev ?E ?j)] =>
        lazymatch goal with _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail | _ =>
          let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H end end.
      lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; z4fan E end.
      lazymatch goal with FRh : rw_cells _ mm (SPV + -528) ?fr, ARh : rw_cells _ mm (SPV + -384) ?ar, LCh : rw_cells _ mm (SPV + -232) ?cs |- _ =>
        assert (I0 : z4fI mb mm fr ar cs) by (unfold z4fI; z4fsplit 12%nat; first [eassumption | reflexivity]) end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => z4fmem M end.
      lazymatch goal with I0 : z4fI _ ?M ?fr ?ar ?cs |- _ =>
        destruct I0 as (MU' & WM' & MU0' & WM0' & MI' & STK' & DTB' & SRC' & FR' & AR' & LC' & LFR' & LAR') end.
      rewrite ?Z_to_bv_bv_unsigned in *.
      eapply (KH _ j0 j1 j2 _ u0 u1 u2 u3 c0 c1 c2 _ _ _ _ _ _ _ _ _ w0 w1 w2).
      all: try eassumption.
      all: try reflexivity.
      all: try (lazymatch goal with |- LBW _ (edenot _ _) => e42_lb_reload end).
      all: try (lazymatch goal with |- LBW _ _ => eapply lbw_mono; [eassumption | lia] end).
      all: try (lazymatch goal with |- (2 <= _)%nat => clear - HOL HU3 HC; lia end).
      all: lazymatch goal with |- context [bv_unsigned (ev ?E ?j)] =>
        match goal with H : _ <= bv_unsigned (ev E j) <= _ |- _ =>
          clear - H; change (2 ^ (3 mod 64)) with 8;
          rewrite ?(Z.mod_small (bv_unsigned (ev E j)) (2 ^ 64)) by lia; Z.div_mod_to_equations; lia end end.
    - z4f12_runL [545748; 545400] 200%nat [true]
        [KZRange SPV 7232 (2^47 - 16); KZRange DT 4096 (2^47 - 8197); KZRange DST 4096 (2^47 - 1);
         KZRange SRC 4096 (2^47 - 1); KZRange n 38 (2^32); KZRange i3 7 (2^32); KZRange (n - i3) 8 (2^32);
         KZRange (bv_unsigned c3) 1 (2^64 - 1); KZRange u3 0 (2^32); KZRange OL 0 (2^32); KZRange (u3 - OL) 0 (2^32);
         KZTab 134483 64 1 [(0, 0, 63)];
         KZWr (SPV + -232) 128; KZDisj (SPV + -232) 128 SRC n]
        [(SRC, n)] [(SPV + -232, 128)] [(SRC, n)].
      all: try z4f12_br.
      all: try z4f12_rd_img CTZ.
      all: try z4f12_acc_img RI.
      all: try z4f12shd.
      all: try z4f12_accS RSRC.
      kx_post_regs_keep.
      repeat match goal with |- context [bv_unsigned (ev ?E ?j)] =>
        lazymatch goal with _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail | _ =>
          let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H end end.
      lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; z4fan E end.
      lazymatch goal with FRh : rw_cells _ mm (SPV + -528) ?fr, ARh : rw_cells _ mm (SPV + -384) ?ar, LCh : rw_cells _ mm (SPV + -232) ?cs |- _ =>
        assert (I0 : z4fI mb mm fr ar cs) by (unfold z4fI; z4fsplit 12%nat; first [eassumption | reflexivity]) end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => z4fmem M end.
      lazymatch goal with I0 : z4fI _ ?M ?fr ?ar ?cs |- _ =>
        destruct I0 as (MU' & WM' & MU0' & WM0' & MI' & STK' & DTB' & SRC' & FR' & AR' & LC' & LFR' & LAR') end.
      rewrite ?Z_to_bv_bv_unsigned in *.
      eapply (KO _ j0 j1 j2 _ u0 u1 u2 u3 c0 c1 c2 _ _ _ _ _ _ _ _ _ _ _ _ _ w0 w1 w2).
      all: try eassumption.
      all: try reflexivity.
      all: try (lazymatch goal with |- LBW _ (edenot _ _) => e42_lb_reload end).
      all: try (lazymatch goal with |- LBW _ _ => eapply lbw_mono; [eassumption | lia] end).
      all: try (lazymatch goal with |- (2 <= _)%nat => clear - HOL HU3 HC; lia end).
      all: lazymatch goal with |- context [bv_unsigned (ev ?E ?j)] =>
        match goal with H : _ <= bv_unsigned (ev E j) <= _ |- _ =>
          clear - H; change (2 ^ (3 mod 64)) with 8;
          rewrite ?(Z.mod_small (bv_unsigned (ev E j)) (2 ^ 64)) by lia; Z.div_mod_to_equations; lia end end.
  Qed.
End X42E.
End CANSEC1.
