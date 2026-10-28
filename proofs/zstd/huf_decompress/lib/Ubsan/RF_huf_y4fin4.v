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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_y4s_iface RF_huf_y4fin RF_huf_y4fin2 RF_huf_y4fin3 RF_huf_y4fin5 RF_huf_y4fin6.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4F4.
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
  Hypothesis CBL : DT + 4 + 8192 <= lo.
  Hypothesis DJ1 : DT + 4 + 8192 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DTA : DT mod 4 = 0.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).
  Notation W4 a b c d := [Z_to_bv 64 a; Z_to_bv 64 b; Z_to_bv 64 c; Z_to_bv 64 d].

  Notation YF l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
                      TOK ECB LCB D8 DC SG DL S0 SL NSM BYS DT0 DTA CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  Notation NDT := (Z.lxor (DT + 4) 18446744073709551615).
  (* [comment removed for export] *)
  Notation KH pc mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 prev) x9 (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 64)
             (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation STB pc mm k SE OPk p ptr bits c x1 x7 x17 x21 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation ELB pc mm k SE OPk ptr bits c x1 x7 x21 x24 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) (Z_to_bv 64 8) (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) x24 c (Z_to_bv 64 (SE - OPk)) x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation STLB pc mm k SE OPk p bits c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 (Z_to_bv 64 bits)
             x23 (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition WSOK (ws : list word) (k : Z) : Prop :=
    nth_error ws 13 = Some (Z_to_bv 64 SS) /\
    forall i, k <= i < 4 -> exists ipi opi iei bi,
      nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 ipi) /\ nth_error ws (Z.to_nat (4 + i)) = Some (Z_to_bv 64 opi)
      /\ nth_error ws (Z.to_nat (8 + i)) = Some bi /\ nth_error ws (Z.to_nat (15 + i)) = Some (Z_to_bv 64 iei)
      /\ DST <= opi <= DST + dcap /\ SS <= ipi /\ ipi + 8 <= SS + n /\ SS <= iei <= SS + n /\ bv_unsigned bi <> 0.

  Lemma wsok_upd : forall ws k v, 0 <= k < 4 -> WSOK ws k -> WSOK (upd ws (Z.to_nat (4 + k)) v) (k + 1).
  Proof using All.
    intros ws k v K (W13 & W). split; [rewrite nth_error_upd_other by lia; exact W13|].
    intros i Hi. destruct (W i ltac:(lia)) as (ipi & opi & iei & bi & A & B & C & D & H).
    exists ipi, opi, iei, bi. rewrite !nth_error_upd_other by lia.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. exact H.
  Qed.

  Lemma y4_seg_bound : 0 <= seg <= dcap.
  Proof using All. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.

  (* [comment removed for export] *)
  Lemma y4_se_bnd : forall prev, DST <= prev <= DST + dcap ->
    DST <= y4_se DST dcap prev <= DST + dcap /\ prev <= y4_se DST dcap prev.
  Proof using All.
    intros prev HP. pose proof y4_seg_bound. unfold y4_se.
    destruct (Z.ltb_spec (DST + dcap - prev) ((dcap + 3) / 4)); cbv beta iota; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma y4f_kstep : forall k prev mm (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) ws ops ips bts
                          (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
    0 <= k < 4 -> Y4M mm (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws ops ips bts -> WSOK ws k ->
    DST <= prev <= DST + dcap ->
    (k + 1 < 4 -> forall prev' mm' ws' (y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 : word),
       Y4M mm' (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws' ops ips bts -> WSOK ws' (k + 1) -> DST <= prev' <= DST + dcap ->
       evt usegs POST (KH 0x16720 mm' (k + 1) prev' y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31)) ->
    evt usegs POST (KH 0x16720 mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31).
  Proof using All.
    intros k prev mm w0 w8 w64 w72 w80 w88 w96 w104 w112 ws ops ips bts x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 K4 Y WK PV NX.
    pose proof WK as WK0. unfold WSOK in WK0. destruct WK0 as (W13 & W).
    destruct (W k ltac:(lia)) as (ipk & opk & iek & bk & WI & WO & WB & WE & O1 & I1 & I2 & E1 & BK).
    destruct (y4_se_bnd prev PV) as (SB & SP0).
    assert (HSE2 : (y4_se DST dcap prev) <= DST + dcap) by lia.
    assert (SPD : nth_error (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) 15 = Some (Z_to_bv 64 (DT + 4))) by reflexivity.
    assert (CONT : forall mm' (y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 : word),
        Y4M mm' (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 (y4_se DST dcap prev))) ops ips bts ->
        evt usegs POST (KH 0x16d28 mm' k (y4_se DST dcap prev) y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31)).
    { intros mm' y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 Y'.
      eapply (YF y4f_be); [lia | lia | exact Y' | reflexivity |].
      intros K1 mm'' z1 z7 z9 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z31 Y''.
      eapply NX; [exact K1 | exact Y'' | apply wsok_upd; [lia | exact WK] | lia]. }
    refine (YF y4f_body k prev ipk opk iek bk w0 w8 w64 w72 w80 w88 w96 w104 w112 ws ops ips bts
              K4 PV W13 WI WO WB WE O1 (conj I1 I2) E1 BK _ _ mm x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 Y).
    - intros mmL bits c y1 y7 y17 y21 y27 YL HL HB.
      assert (HSE : DST <= opk <= (y4_se DST dcap prev)) by lia.
      assert (K56 : forall mm' p ptr bits' (c' z1 z7 z17 z21 z26 z27 : word),
          Y4M mm' (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws ops ips bts -> opk <= p <= (y4_se DST dcap prev) ->
          (64 < bits' \/ SS <= ptr /\ ptr + 8 <= SS + n) -> 0 <= bits' < 2^64 ->
          evt usegs POST (STB 0x16b70 mm' k (y4_se DST dcap prev) opk p ptr bits' c' z1 z7 z17 z21 z26 z27)).
      { intros mm' p ptr bits' c' z1 z7 z17 z21 z26 z27 Y' HP HPT HB'.
        eapply (YF y4f_j k (y4_se DST dcap prev) opk _ ws ops ips bts K4 HSE HSE2 SPD WO CONT); [exact Y' | exact HP | | exact HB'].
        intros HB64. destruct HPT as [HPT | HPT]; [lia | exact HPT]. }
      assert (K08 : forall mm' p bits' (c' z1 z7 z17 z18 z19 z20 z21 z23 z26 z27 : word),
          Y4M mm' (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws ops ips bts -> opk <= p <= (y4_se DST dcap prev) ->
          evt usegs POST (STLB 0x16cd0 mm' k (y4_se DST dcap prev) opk p bits' c' z1 z7 z17 z18 z19 z20 z21 z23 z26 z27)).
      { intros mm' p bits' c' z1 z7 z17 z18 z19 z20 z21 z23 z26 z27 Y' HP.
        eapply (YF y4f_last k (y4_se DST dcap prev) opk _ ws ops ips bts K4 HSE HSE2 SPD WO CONT); [exact Y' | exact HP]. }
      eapply (YF y4f_loop5 k (y4_se DST dcap prev) opk _ ws ops ips bts K4 HSE HSE2 SPD K56 K08 (Z.to_nat (dcap + 1)));
        [exact YL | lia | lia | rewrite Z2Nat.id by lia; lia | exact I1 | exact I2 | lia].
    - intros mmE bits c y1 y7 y21 y24 y27 YE HL1 HL2 HB.
      assert (HSE : DST <= opk <= (y4_se DST dcap prev)) by lia.
      eapply (YF y4f_else k (y4_se DST dcap prev) opk _ ws ops ips bts K4 HSE HSE2 SPD WO CONT);
        [exact YE | exact HL2 | exact I1 | exact I2 | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma y4f_kloop : forall (j : nat) k prev mm (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) ws ops ips bts
                          (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
    k + Z.of_nat j = 3 -> 0 <= k ->
    Y4M mm (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws ops ips bts -> WSOK ws k -> DST <= prev <= DST + dcap ->
    evt usegs POST (KH 0x16720 mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31).
  Proof using All.
    induction j as [|j IH]; intros k prev mm w0 w8 w64 w72 w80 w88 w96 w104 w112 ws ops ips bts x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 HJ HK Y WK PV;
      (apply (y4f_kstep k prev mm w0 w8 w64 w72 w80 w88 w96 w104 w112 ws ops ips bts); [lia | exact Y | exact WK | exact PV |]).
    - intros K1. exfalso. lia.
    - intros K1 prev' mm' ws' y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 Y' WK' PV'.
      eapply IH; [lia | lia | exact Y' | exact WK' | exact PV'].
  Qed.

  (* [comment removed for export] *)
  Lemma y4_wb : forall mm ws (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) (b0 b1 b2 b3 : word)
                         IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 IE0 IE1 IE2 IE3
                         (x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    Y4M mm (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws (W4 OP0 OP1 OP2 OP3) (W4 IP0 IP1 IP2 IP3) [b0; b1; b2; b3] ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) ->
    nth_error ws 15 = Some (Z_to_bv 64 IE0) -> nth_error ws 16 = Some (Z_to_bv 64 IE1) ->
    nth_error ws 17 = Some (Z_to_bv 64 IE2) -> nth_error ws 18 = Some (Z_to_bv 64 IE3) ->
    SS <= IE0 <= SS + n -> SS <= IE1 <= SS + n -> SS <= IE2 <= SS + n -> SS <= IE3 <= SS + n ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= DST + seg -> DST <= OP1 <= DST + 2 * seg -> DST <= OP2 <= DST + 3 * seg -> DST <= OP3 <= DST + dcap ->
    bv_unsigned b0 <> 0 -> bv_unsigned b1 <> 0 -> bv_unsigned b2 <> 0 -> bv_unsigned b3 <> 0 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 0xfdb8) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 0x104a0)
                           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1667c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm ws w0 w8 w64 w72 w80 w88 w96 w104 w112 b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 IE0 IE1 IE2 IE3
      x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      Y W13 WI0 WI1 WI2 WI3 HE0 HE1 HE2 HE3 HI0 HI0' HI1 HI1' HI2 HI2' HI3 HI3' HO0 HO1 HO2 HO3 NB0 NB1 NB2 NB3.
    pose proof y4_seg_bound as SGB.
    assert (WSL : length ws = 19%nat) by (destruct Y as (_ & _ & _ & _ & _ & _ & _ & WSL & _); exact WSL).
    apply (YF y4f_pre mm ws w0 w8 w64 w72 w80 w88 w96 w104 w112 b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 IE0 IE1 IE2 IE3
      x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31); try assumption.
    intros mm' y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 Y'.
    eapply (y4f_kloop 3%nat 0 DST mm' w0 w8 w64 w72 w80 w88 w96 w104 w112); [lia | lia | exact Y' | | lia].
    destruct ws as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|c6 [|c7 [|c8 [|c9 [|c10 [|c11 [|c12 [|c13 [|c14
      [|c15 [|c16 [|c17 [|c18 [|]]]]]]]]]]]]]]]]]]]]; cbn in WSL; try lia.
    cbn in W13, WI0, WI1, WI2, WI3.
    injection W13 as W13. injection WI0 as WI0. injection WI1 as WI1. injection WI2 as WI2. injection WI3 as WI3.
    subst c13 c15 c16 c17 c18.
    unfold WSOK. split; [reflexivity |].
    intros i Hi. assert (HI : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct HI as [-> | [-> | [-> | ->]]]; do 4 eexists; repeat split; try reflexivity; try assumption; lia.
  Qed.

End Y4F4.
End CANSEC1.
