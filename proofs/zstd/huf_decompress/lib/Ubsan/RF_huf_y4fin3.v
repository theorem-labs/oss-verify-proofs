(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_y4s_iface RF_huf_y4fin.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Y4F3.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis DTA : DT mod 4 = 0.
  Hypothesis CBL : DT + 4 + 8192 <= lo.
  Hypothesis DJ1 : DT + 4 + 8192 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).

  Notation YF l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
                      TOK ECB LCB D8 DC SG DL S0 SL NSM BYS DT0 DTA CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  Notation NDT := (Z.lxor (DT + 4) 18446744073709551615).
  Notation KH pc mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 prev) x9 (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 64)
             (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Section STREAM3.
  Variables (k SE OPk : Z) (sps ws ops ips bts : list word).
  Hypothesis K4 : 0 <= k < 4.
  Hypothesis HSE : DST <= OPk <= SE.
  Hypothesis HSE2 : SE <= DST + dcap.
  Hypothesis SPD : nth_error sps 15 = Some (Z_to_bv 64 (DT + 4)).
  Hypothesis WOP : nth_error ws (Z.to_nat (4 + k)) = Some (Z_to_bv 64 OPk).

  Notation STL pc mm p x22 c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22
             x23 (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Hypothesis CONT : forall mm (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
    Y4M mm sps (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 SE)) ops ips bts ->
    evt usegs POST (KH 0x16d28 mm k SE x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31).

  Notation ST pc mm p ptr bits c x1 x7 x17 x21 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation YS l := (YF l k SE OPk sps ws ops ips bts K4 HSE HSE2 SPD WOP CONT) (only parsing).

  Ltac y4mpack :=
    unfold RF_huf_y4s_iface.Y4M;
    lazymatch goal with ARR : u8arr usegs ?m DST (map (Z_to_bv 8) ?bf), LB : zlen ?bf = dcap |- _ =>
      split; [exists bf; split; [exact ARR | exact LB] |] end;
    repeat (split; [first [eassumption | rewrite ?upd_length; eassumption | eexists; eassumption] |]);
    eassumption.

  Ltac y4open Y := destruct Y as ((buf & ARR & LB) & SRC & CBR & STK & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM);
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof y4_seg_le as SGL.
  Ltac y4spd := lazymatch goal with SPA : u64arr usegs ?m (SP + -512) sps |- _ =>
    pose proof (u64arr_read usegs m (SP + -512) sps 15 (Z_to_bv 64 (DT + 4)) (wa (SP + -512 + 8 * 15)) SPA SPD ltac:(lia) eq_refl) as RSPW end.
  Ltac y4sw := repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (y4_swrap_small x) by lia end.
  Ltac y4nrm := rewrite ?byte_lit by lia; rewrite ?y4_land7; y4sw.
  Ltac y4bnd2 := rewrite ?Z.shiftl_mul_pow2 by lia; try (change (2 ^ 3) with 8); y4sw; lia.

  Notation EL pc mm ptr bits c x1 x7 x21 x24 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) (Z_to_bv 64 8) (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) x24 c (Z_to_bv 64 (SE - OPk)) x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma y4f_else : forall mm ptr bits (c x1 x7 x21 x24 x27 : word),
    Y4M mm sps ws ops ips bts -> SE - OPk < 8 -> SS <= ptr -> ptr + 8 <= SS + n -> 0 <= bits < 64 ->
    evt usegs POST (EL 0x16a44 mm ptr bits c x1 x7 x21 x24 x27).
  Proof using All.
    intros until x27. intros Y HSK HP1 HP2 HB.
    pose proof (bv_unsigned_in_range 64 c) as RC. unfold bv_modulus in RC. cbn in RC.
    y4open Y. y4spd.
    zstep. y4go2 0x16b70 0x16cd0.
    all: y4nrm.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16b70) _ _ _ _) => eapply (YS y4f_j)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16cd0) _ _ _ _) => eapply (YS y4f_last)
      end.
    all: first [ y4mpack | lia | (intros; split; lia) | idtac ].
    all: rewrite ?Z.shiftr_div_pow2 in * by lia; rewrite ?Z.shiftl_mul_pow2 in * by lia;
      try change (2 ^ 3) with 8 in *.
    all: rewrite ?swrap32_small by (Z.div_mod_to_equations; lia).
    all: rewrite ?Z.mod_small by (Z.div_mod_to_equations; lia).
    all: Z.div_mod_to_equations; lia.
  Qed.

  End STREAM3.
End Y4F3.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
