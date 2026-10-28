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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs AF_huf_z4f_defs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition zf8_hide (P : Prop) : Prop := P.
Ltac zf8_hide1 H :=
  lazymatch goal with
  | PK : zf8_hide ?Q |- _ =>
      let T := type of H in let PK' := fresh "PK" in
      assert (PK' : zf8_hide (T /\ Q)) by exact (conj H PK); clear H PK
  | _ => let T := type of H in let PK := fresh "PK" in assert (PK : zf8_hide T) by exact H; clear H
  end.
Ltac zf8_unpk H :=
  lazymatch type of H with
  | _ /\ _ => let A := fresh "HA" in let B := fresh "HB" in destruct H as [A B]; zf8_unpk B
  | _ => idtac
  end.
Ltac zf8_unhide := lazymatch goal with PK : zf8_hide _ |- _ => unfold zf8_hide in PK; zf8_unpk PK end.

Lemma zf8_br_nz : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P B) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))).
    { apply Z.lxor_nonneg; split; intros; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B)) <> 0).
    { intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))) 1); [lia|].
  reflexivity.
Qed.

Lemma zf8_srl58 : forall x : word, 0 <= bv_unsigned (alu64 ALU_SRL x (Z_to_bv 64 58)) < 64.
Proof.
  intros x. rewrite KXS.u_srl64, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (58 mod 2 ^ 64 mod 64) with 58. pose proof (bv_unsigned_in_range _ x) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R. split; [apply Z.div_pos; lia |].
  apply Z.div_lt_upper_bound; lia.
Qed.

Ltac zf8_rdtab T :=
  lazymatch goal with |- exists bs, rdn _ _ (adenot ?E ?a) 1 = Some bs =>
    rewrite adenot_wa; unfold wa;
    lazymatch goal with |- context [estart E ?a'] =>
      edestruct (T (estart E a')) as (b & Hb & _);
      [ unfold estart; cbn [a_base a_off edenot];
        lazymatch goal with |- context [bv_unsigned (alu64 ALU_SRL ?x (Z_to_bv 64 58))] => pose proof (zf8_srl58 x) end; lia
      | rewrite Z.mod_1_r; reflexivity
      | exists [b]; exact Hb ]
    end
  end.

Ltac zf8_brx :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?P (EAlu ALU_SRL (EVar ?j) (ELit 3))) (ELit 1)))) _ = true =>
      let HRJ := fresh "HRJ" in
      kx_range (EVar j) HRJ; apply zf8_br_nz; z4fez;
      [ rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); change (2 ^ (3 mod 64)) with 8;
        rewrite (Z.mod_small (bv_unsigned (ev E j))) by lia; rewrite Z.mod_small; Z.div_mod_to_equations; lia
      | rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); rewrite Z.mod_small by lia; lia ]
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
  Hypothesis TL11 : tl = 11.
  Notation z4fI := (AF_huf_z4f_defs.z4fI m0 SPV DST dcap SRC DT src dtb).
  Hypothesis FI9 : x42e_fi9_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.

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

  Definition x42e_fi8n_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 ct (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x5 x17 x18 x19 x25 x31 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 5 <= u2 <= o2 + 10 ->
    o3 + 2 <= u3 <= o3 + 4 ->
    i0 - 7 <= j0 <= i0 ->
    0 <= ct <= 63 ->
    LBW 63 c1 ->
    LBW 63 c2 ->
    LBW 30 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x860d4 mm x1 x5 c1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) (Z_to_bv 64 ct) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (SRC + j0)) x17 x18 x19 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (SPV + -168)) c3 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) x31).

  Lemma x42e_fi8n : x42e_fi8n_stmt.
  Proof using CTX X2OK NBOK ACTX TL11 FI9.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi8n_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 ct c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x5 x17 x18 x19 x25 x31 w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBH FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HU3 HJ0 HCT HLBc1 HLBc2 HLBc3 KH KO. subst nd.
    destruct (x42f_unp _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ACTX mm MU0) as (USRCm & _ & _).
    assert (RFRM : rng RNG (SPV + -528) 424) by (eapply rng_sub; [exact RSTK | lia | lia]).
    pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 128 LC ltac:(cbn; lia)) as WLOC.
    assert (KJ0 : 0 <= j0 /\ j0 + 8 <= n) by lia.
    assert (SRL : SRC + n <= SPV + -528 \/ SPV <= SRC) by lia.
    unfold shspan in RSRCS.
    clear UDST RDST RDSTS UDT USRC RSTK ART RDT RDTS RI.
    zf8_hide1 HOL. zf8_hide1 HO0. zf8_hide1 HO1. zf8_hide1 HO2. zf8_hide1 HE0. zf8_hide1 HE1. zf8_hide1 HE2. zf8_hide1 HQ3.
    zf8_hide1 HQ0. zf8_hide1 HOLR. zf8_hide1 HI0. zf8_hide1 HI1. zf8_hide1 HI2. zf8_hide1 HI3. zf8_hide1 HN0. zf8_hide1 HN1.
    zf8_hide1 HN2. zf8_hide1 HN3. zf8_hide1 HL1. zf8_hide1 HL2. zf8_hide1 HL3. zf8_hide1 HLN. zf8_hide1 HU0. zf8_hide1 HU1.
    zf8_hide1 HU2. zf8_hide1 HR. zf8_hide1 HE3. zf8_hide1 HO3. zf8_hide1 HU3. zf8_hide1 HJ0. zf8_hide1 TL. zf8_hide1 OS2.
    zf8_hide1 DJ1. zf8_hide1 SPA. zf8_hide1 DT2. zf8_hide1 DJ2. zf8_hide1 OS1. zf8_hide1 OS3. zf8_hide1 DSTA. zf8_hide1 DTA.
    zf8_hide1 DHI. zf8_hide1 DTBF. zf8_hide1 R1. zf8_hide1 R3. zf8_hide1 KLO. zf8_hide1 DL.
    kx_runFm [0x86168] 120%nat
      [KZRange SRC 4096 (2^47 - 1); KZRange n 8 (2^32 - 1); KZRange j0 0 (2^32 - 1); KZRange (n - j0) 8 (2^32);
       KZRange ct 0 63; KZRange SPV 4096 (2^47 - 1);
       KZWr (SPV + -232) 128;
       KZDisj (SPV + -528) 424 SRC n]
      [(SRC, n)]
      [(SRC, n); (SPV + -528, 424)]
      [(SRC, n)].
    kx_post_regs_keep.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ ?X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      set (C0N := X) in * end.
    assert (LC0 : LBW 7 C0N) by (subst C0N; e42_lb_reload).
    set (IX := bv_unsigned c3 mod 2 ^ 64 / 2 ^ (53 mod 64)) in *.
    assert (HIXN : 0 <= IX <= 2047).
    { subst IX. pose proof (bv_unsigned_in_range _ c3) as RC. unfold bv_modulus in RC. change (2 ^ Z.of_N 64) with (2 ^ 64) in RC.
      rewrite Z.mod_small by lia. change (2 ^ (53 mod 64)) with (2 ^ 53). split; [apply Z.div_pos; lia |].
      assert (bv_unsigned c3 / 2 ^ 53 < 2 ^ 11) by (apply Z.div_lt_upper_bound; lia). lia. }
    zf8_unhide.
    kx_cells_split LC. kx_cells_post.
    kx_munch MU. kx_munch MU0.
    kx_post_mem_free.
    kx_frame DTBH. kx_frame SRCB. kx_frame FR. kx_frame AR.
    all: try (cbn [cells_size csize]; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => set (M1 := m1) in * end.
    replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)) by (f_equal; lia).
    eapply (FI9 r mb M1 q OL (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 IX C0N c1 c2 c3 e0 e1 e2 e3
              av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 _ _ _ _ _ _ w0 w1 w2).
    all: try eassumption.
    all: try reflexivity.
    all: try kx_cells_merge.
    all: try lia.
  Qed.

  Definition x42e_fi8m_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x5 x11 x16 x17 x18 x19 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 5 <= u2 <= o2 + 10 ->
    o3 + 2 <= u3 <= o3 + 4 ->
    LBW 63 c1 ->
    LBW 63 c2 ->
    LBW 30 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x86094 mm x1 x5 c1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) x11 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) x16 x17 x18 x19 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (SPV + -168)) c3 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Lemma x42e_fi8m : x42e_fi8m_stmt.
  Proof using CTX X2OK NBOK ACTX TL11 FI9.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi8m_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x5 x11 x16 x17 x18 x19 x25 w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBH FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HU3 HLBc1 HLBc2 HLBc3 KH KO. subst nd.
    pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 128 LC ltac:(cbn; lia)) as WLOC.
    assert (RFRM : rng RNG (SPV + -528) 424) by (eapply rng_sub; [exact RSTK | lia | lia]).
    assert (TCZ : ztab_fact bsegs mm 134483 64 1 [(0, 0, 63)]) by (apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity]).
    assert (KI0 : 7 <= i0 /\ i0 + 8 <= n) by lia.
    assert (SIM : 134483 + 64 <= SPV + -528) by lia.
    clear UDST RDST RDSTS UDT USRC RSTK ART RDT RDTS RSRC RSRCS.
    zf8_hide1 HOL. zf8_hide1 HO0. zf8_hide1 HO1. zf8_hide1 HO2. zf8_hide1 HE0. zf8_hide1 HE1. zf8_hide1 HE2. zf8_hide1 HQ3.
    zf8_hide1 HQ0. zf8_hide1 HOLR. zf8_hide1 HI0. zf8_hide1 HI1. zf8_hide1 HI2. zf8_hide1 HI3. zf8_hide1 HN0. zf8_hide1 HN1.
    zf8_hide1 HN2. zf8_hide1 HN3. zf8_hide1 HL1. zf8_hide1 HL2. zf8_hide1 HL3. zf8_hide1 HLN. zf8_hide1 HU0. zf8_hide1 HU1.
    zf8_hide1 HU2. zf8_hide1 HR. zf8_hide1 HE3. zf8_hide1 HO3. zf8_hide1 HU3. zf8_hide1 TL. zf8_hide1 OS2.
    zf8_hide1 DJ1. zf8_hide1 SPA. zf8_hide1 DT2. zf8_hide1 DJ2. zf8_hide1 OS1. zf8_hide1 OS3. zf8_hide1 DSTA. zf8_hide1 DTA.
    zf8_hide1 DHI. zf8_hide1 DTBF. zf8_hide1 R1. zf8_hide1 R3. zf8_hide1 DL. zf8_hide1 SL.
    kx_runFmd [549076] 40%nat [true]
      [KZTab 134483 64 1 [(0, 0, 63)];
       KZRange SRC 4096 (2^47 - 1); KZRange n 8 (2^32 - 1); KZRange i0 7 (2^32 - 1); KZRange (n - i0) 8 (2^32);
       KZRange SPV 4096 (2^47 - 1);
       KZImg 134483 (134483 + 64);
       KZWr (SPV + -232) 128]
      []
      [(SPV + -528, 424); (134483, 64)]
      [].
    all: try (zf8_rdtab TCZ).
    all: try zf8_brx.
    kx_post_regs_keep.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (ev KXE ?j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      kx_range (EVar j) HCT; cbn [edenot] in HCT; set (CT := bv_unsigned (ev KXE j)) in *;
      replace (ev KXE j) with (Z_to_bv 64 CT) by (subst CT; apply Z_to_bv_bv_unsigned) end.
    zf8_unhide.
    kx_cells_split LC. kx_cells_post.
    kx_munch MU. kx_munch MU0.
    kx_post_mem_free.
    kx_frame DTBH. kx_frame SRCB. kx_frame FR. kx_frame AR.
    all: try (cbn [cells_size csize]; lia).
    rewrite ?kx_mul_m1 in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => set (M1 := m1) in * end.
    replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)) by (f_equal; lia).
    eapply (x42e_fi8n r mb M1 q OL (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 (i0 + - (CT mod 2 ^ 64 / 2 ^ (3 mod 64))) CT
              c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 _ _ _ _ _ _ _ w0 w1 w2).
    all: try eassumption.
    all: try reflexivity.
    all: try kx_cells_merge.
    all: try lia.
    all: (change (2 ^ (3 mod 64)) with 8; rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia).
  Qed.

  Lemma x42e_fi8 : x42e_fi8_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.
  Proof using CTX X2OK NBOK ACTX TL11 FI9.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi8_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 ix c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x17 x18 x19 x20 x22 x25 w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBH FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HU3 HIX HLBc0 HLBc1 HLBc2 HLBc3 KH KO. subst nd.
    rewrite TL11 in DTBF. change (4 + 4 * 2 ^ 11) with 8196 in DTBF.
    assert (DPOS : 0 < dcap) by lia.
    destruct (x42f_unp _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ACTX mm MU0) as (_ & UDTm & UDSTm).
    specialize (UDSTm DPOS). pose proof (RDST DPOS) as RDSTc. pose proof (RDSTS DPOS) as RDSTSc.
    assert (RFRM : rng RNG (SPV + -528) 424) by (eapply rng_sub; [exact RSTK | lia | lia]).
    assert (WAD : wr_at bsegs mm DST dcap).
    { pose proof OUT as (S0 & S1 & S2). split; [lia | split; [lia |]]. intros i Hi. apply (S2 (DST + i)). lia. }
    pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 128 LC ltac:(cbn; lia)) as WLOC.
    pose proof (x42f_tab _ _ _ _ _ _ _ _ _ _ _ CTX X2OK NBOK TL11 mm DTBH) as TAB.
    pose proof (lbw_pos _ _ HLBc0) as HPc0.
    assert (KU3 : 1 <= u3 /\ u3 + 8 <= dcap) by lia.
    assert (KDC : 10 <= dcap) by nia.
    assert (DIM : 66420 + 68 <= DST) by (pose proof (DHI DPOS); unfold AIMG_HI in *; lia).
    assert (SIM : 66420 + 68 <= SPV + -528) by lia.
    unfold shspan in RDTS, RDSTSc.
    clear UDST RDST RDSTS UDT USRC RSTK ART RSRC RSRCS.
    zf8_hide1 HOL. zf8_hide1 HO0. zf8_hide1 HO1. zf8_hide1 HO2. zf8_hide1 HE0. zf8_hide1 HE1. zf8_hide1 HE2. zf8_hide1 HQ3.
    zf8_hide1 HQ0. zf8_hide1 HOLR. zf8_hide1 HI0. zf8_hide1 HI1. zf8_hide1 HI2. zf8_hide1 HI3. zf8_hide1 HN0. zf8_hide1 HN1.
    zf8_hide1 HN2. zf8_hide1 HN3. zf8_hide1 HL1. zf8_hide1 HL2. zf8_hide1 HL3. zf8_hide1 HLN. zf8_hide1 HU0. zf8_hide1 HU1.
    zf8_hide1 HU2. zf8_hide1 HR. zf8_hide1 HE3. zf8_hide1 HO3. zf8_hide1 HU3. zf8_hide1 SL. zf8_hide1 TL. zf8_hide1 OS2.
    zf8_hide1 DJ1. zf8_hide1 SPA. zf8_hide1 DT2.
    kx_runFm [549012] 80%nat
      [KZTab (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)];
       KZRange (bv_unsigned c0) 1 (2^64 - 1);
       KZRange DST 4096 (2^47 - 1); KZRange dcap 10 (2^32 - 1); KZRange u3 1 (2^32 - 1); KZRange (dcap - u3) 8 (2^32);
       KZRange ix 0 2047;
       KZRange DT 4096 (2^47 - 8196); KZRange DTB 8196 (2^47 - 1); KZRange SPV 8192 (2^47 - 1);
       KZWord (SPV + -392) 8 66420; KZImg (66420 + 60) (66420 + 68);
       KZWr (DST + u3) 2; KZWr (SPV + -232) 128;
       KZDisj (DST + u3) 2 DT DTB; KZDisj (SPV + -232) 128 DT DTB;
       KZDisj (DST + u3) 2 (SPV + -528) 424;
       KZDisj (DST + u3) 2 (66420 + 60) 8; KZDisj (SPV + -528) 424 (66420 + 60) 8]
      [(DT, DTB)]
      [(DT, DTB); (DST, dcap); (SPV + -528, 424); (66420 + 60, 8)]
      [(DT + 4, 8192); (DST + u3, 2)].
    kx_post_regs_keep.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?X _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      set (W3 := X) in *; assert (LW3 : LBW 30 W3) by (subst W3; e42_lb_chain KXA) end.
    lazymatch goal with |- context [Z_to_bv 64 (DST + (u3 + bv_unsigned (ev KXE ?j)))] => kx_range (EVar j) HLEN;
      cbn [edenot] in HLEN; set (LEN := bv_unsigned (ev KXE j)) in * end.
    zf8_unhide.
    kx_cells_split LC. kx_cells_post.
    kx_munch MU. kx_munch MU0.
    kx_post_mem_free.
    kx_frame DTBH. kx_frame SRCB. kx_frame FR. kx_frame AR.
    all: try (cbn [cells_size csize]; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => set (M1 := m1) in * end.
    replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)) by (f_equal; lia).
    eapply (x42e_fi8m r mb M1 q OL (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 (u3 + LEN) c0 c1 c2 W3 e0 e1 e2 e3
              av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 _ _ _ _ _ _ _ _ w0 w1 w2).
    all: try eassumption.
    all: try reflexivity.
    all: try kx_cells_merge.
    all: try lia.
  Qed.
End X42E.
End CANSEC1.
