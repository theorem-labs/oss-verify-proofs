(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx
     AZ_hft_x1_seg AZ_hft_x1_defs AZ_hft_x1_h1 AZ_hft_x1_h2 AZ_hft_x1_h3 AZ_hft_x1_rs AZ_hft_x1_s AZ_hft_x1_fk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + 16388).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : art m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000)
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Variables (n SRC : Z) (flags : word).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation FRA0 jA jC jD jB jE := ([CB 80 jA; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); CB 16 jC;
                                    C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 WK); CB 64 jD; CB 80 jB; CB 24 jE; C8 (Z_to_bv 64 FF)]).
  (* [comment removed for export] *)
  Notation STR pc mm xra dtd tl' nbs x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 dtd) (Z_to_bv 64 tl') (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  (* [comment removed for export] *)
  Notation STF mm xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST 0x96800 mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        x28 x29 x30 x31).

  (* [comment removed for export] *)
  Hypothesis KENDX : forall (hw rank : list Z) (tl : Z) m2 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
      (xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    XF m5 SPV SPA lo DT WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m2 -> x1pref tl (2^tl) dt -> 11 <= tl <= 12 -> zlen hw = 256 -> zlen rank = 13 ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000)
                                  xs5 (Z_to_bv 64 r) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x970d8) fc None m2 (seg_rom bsegs)).
  (* [comment removed for export] *)
  Hypothesis FILLX : forall (hw rank : list Z) (nbs tl : Z) m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte)
      (xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 11 <= tl <= 12 -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw -> zlen rank = 13 ->
    XB m5 SPV SPA lo DT WK wksz FF r hw rank tl (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE dt rst syb m1 -> x1pref tl 0 dt ->
    evtF bsegs RNG POST (STF m1 xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  (* [comment removed for export] *)
  Hypothesis HULW : ahull RNG m5 WK wksz.

  Section TAIL.
  Variables (hw rank : list Z) (nbs tl dtd : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 11 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis DTD : 0 <= dtd < 4294967296.
  Hypothesis DTD12 : dtd mod 256 = 12.
  (* [comment removed for export] *)
  Local Ltac sect := first [exact HY| exact UDT| exact UW| exact ART0| exact Hr| exact STATS| exact TLR| exact NBSR| exact LHW| exact BHW| exact LRK| exact DTD| exact DTD12| idtac].

  (* [comment removed for export] *)
  Lemma x1_tailA : forall m1 (dt rst : list Z) (syb jA jC jD jB jE j3 j5 j6 : list byte) (tl0 fl : Z)
      xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt ->
    Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt = dtd ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) -> zlen rst = 13 -> Forall (fun v : Z => 0 <= v) rst ->
    stk bsegs m1 (WK + 104) (WK + 980) -> u8arr bsegs m1 (WK + 980) syb -> zlen syb = 256 -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA -> mem_inv bsegs m1 -> munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (FRA0 jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
    rw_cells bsegs m1 (SPA + 56) [C8 (Z_to_bv 64 r)] ->
    evtF bsegs RNG POST (STR 0x96440 m1 xra dtd tl nbs x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros DTC DTLEN DTBY DTDE HWC RK RST RSTLEN RSTNN STS SYC SYLEN WKR STK MI MU WM FR FFC FR56.
    (eapply (x1_h3aA RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF r) with (hw := hw) (rank := rank) (tl := tl) (nbs := nbs) (dtd := dtd) (dt := dt) (rst := rst) (syb := syb); sect);
      [exact DTC| exact DTLEN| exact DTBY| exact DTDE| exact HWC| exact RK| exact RST| exact RSTLEN| exact RSTNN| exact STS| exact SYC| exact SYLEN| exact WKR
      | exact STK| exact MI| exact MU| exact WM| exact FR| exact FFC| exact FR56|].
    intros m2 dt2 k176 jA' jA2 jC' jD' jB' ya0 ya1 ya2 ya3 I2 PF2 FFC2.
    (eapply (x1_rs0A RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF r) with (hw := hw) (rank := rank) (tl := tl) (nbs := nbs); sect); [exact I2| exact PF2| exact FFC2|].
    intros m3 rs3 y2 y5 y6 y7 I3 RSI3 FFC3.
    (eapply (x1_rsA RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF r) with (hw := hw) (rank := rank) (tl := tl) (nbs := nbs); sect); [exact I3| exact RSI3| exact FFC3|].
    intros m4 rs4 za0 za2 za3 za4 za5 z6 z28 z29 I4 RSI4 FFC4.
    (eapply (x1_sortA RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF r) with (hw := hw) (rank := rank) (tl := tl) (nbs := nbs); sect); [exact I4| exact RSI4|].
    intros m6 rs6 syb6 w5 w6 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 w28 w29 w30 w31 I6.
    eapply (FILLX hw rank nbs tl); [exact STATS| exact TLR| exact NBSR| exact LHW| exact BHW| exact LRK| exact I6| exact PF2].
  Qed.
  End TAIL.

  Local Ltac sect := first [exact HY| exact UDT| exact UW| exact ART0| exact Hr| exact HULW| idtac].

  (* [comment removed for export] *)
  Lemma x1_bodyA : forall (hw rank : list Z) (nbs tl : Z) (dtb : list byte) (fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte)
      (x5 x6 x7 xa2 xa3 xa4 xa5 xa6 xa7 x19 x28 x29 x30 x31 : word),
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw ->
    mem_inv bsegs m5 -> stk bsegs m5 lo SPA ->
    rw_cells bsegs m5 SPA (FRA0 jA jC jD jB jE) -> rw_cells bsegs m5 (SPA + 56) [C8 (Z_to_bv 64 r)] ->
    rw_cells bsegs m5 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    u8arr bsegs m5 DT dtb -> huf_hdr_ok dtb ->
    u8arr bsegs m5 (WK + 1236) (map (Z_to_bv 8) hw) -> u32arr bsegs m5 WK (map (Z_to_bv 64) rank) ->
    stk bsegs m5 (WK + 52) (WK + 1236) -> stk bsegs m5 (WK + 1492) (WK + wksz) ->
    evtF bsegs RNG POST (ST 0x962cc m5 (Z_to_bv 64 0x962bc) x5 x6 x7 (Z_to_bv 64 r) (Z_to_bv 64 18446744073709551496) xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 FF) x19 (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 n)
                           (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31).
  Proof.
    intros until x31; intros STATS NBSR LHW BHW MI STK FR FR56 FFC DTC0 HDR HWC RK0 WS1 WKR.
    pose proof STATS as (TL0 & _ & _ & LRK0 & _). unfold FseNCount.Zlength in LRK0.
    pose proof HDR as [DTBL DT0].
    rewrite <- (bytes_of_unsigned dtb) in DTC0. set (dt := map bv_unsigned dtb) in *.
    assert (DTLEN : zlen dt = 16388) by (subst dt; rewrite length_map; exact DTBL).
    assert (DTBY : Forall isbyte dt) by (subst dt; apply bytes_unsigned_range).
    assert (DTZ0 : Znth 0 dt = 12).
    { subst dt. unfold Znth. change (Z.to_nat 0) with 0%nat. destruct dtb as [|b0 t]; [discriminate DT0|]. cbn in DT0 |- *. injection DT0 as ->. reflexivity. }
    clearbody dt.
    pose proof (u32arr_u32b bsegs m5 WK rank RK0) as RK.
    pose proof (Forall_Znth _ dt 1 DTBY ltac:(lia)) as B1. pose proof (Forall_Znth _ dt 2 DTBY ltac:(lia)) as B2. pose proof (Forall_Znth _ dt 3 DTBY ltac:(lia)) as B3. cbv beta in B1, B2, B3.
    set (dtd := 12 + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt).
    assert (DTDR : 0 <= dtd < 4294967296) by (subst dtd; lia). assert (DTD12 : dtd mod 256 = 12) by (subst dtd; Z.div_mod_to_equations; lia).
    assert (DTDE : Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt = dtd) by (subst dtd; lia).
    (* [comment removed for export] *)
    assert (TAIL : forall m1 (hw1 rank1 : list Z) (tl1 : Z) yra y5 y6 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31,
      huf_stats_ok (firstn (Z.to_nat nbs) hw1) rank1 tl1 -> 11 <= tl1 <= 12 -> zlen hw1 = 256 -> Forall isbyte hw1 -> zlen rank1 = 13 ->
      mem_inv bsegs m1 -> munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 -> stk bsegs m1 lo SPA ->
      rw_cells bsegs m1 SPA (FRA0 jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
      rw_cells bsegs m1 (SPA + 56) [C8 (Z_to_bv 64 r)] -> u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
      u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw1) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank1)) ->
      stk bsegs m1 (WK + 52) (WK + 1236) -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
      evtF bsegs RNG POST (STR 0x96440 m1 yra dtd tl1 nbs y5 y6 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31)).
    { intros m1 hw1 rank1 tl1 yra y5 y6 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31
             ST1 TL1 LH1 BH1 LR1 MI1 MU1 WM1 STK1 FR1 FFC1 FR561 DTC1 HWC1 RK1 WS WKR1.
      destruct (stk_split bsegs _ (WK + 52) (WK + 104) (WK + 1236) WS ltac:(lia)) as [WRS WS2].
      destruct (stk_split bsegs _ (WK + 104) (WK + 980) (WK + 1236) WS2 ltac:(lia)) as [STS WSY].
      open_hx HY.
      destruct (u32b_of_stk bsegs m1 (WK + 52) 13%nat ltac:(replace (WK + 52 + 4 * Z.of_nat 13) with (WK + 104) by lia; exact WRS) ltac:(lia) ltac:(lia)) as (rst & RST & RL & RNN).
      destruct (stk_open bsegs m1 (WK + 980) (WK + 1236) (WK + 980) 256%nat WSY ltac:(lia) ltac:(lia)) as (syb & SYC & _ & _).
      assert (SYLEN : zlen syb = 256) by (destruct SYC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; rewrite LJ; reflexivity).
      apply u8arr_of_rw_cells in SYC.
      (eapply (x1_tailA hw1 rank1 nbs tl1 dtd) with (dt := dt) (rst := rst) (syb := syb));
        [exact ST1| exact TL1| exact NBSR| exact LH1| exact BH1| exact LR1| exact DTDR| exact DTD12
        | exact DTC1| exact DTLEN| exact DTBY| exact DTDE| exact HWC1| exact RK1| exact RST| rewrite RL; reflexivity
        | eapply Forall_impl; [| exact RNN]; cbv beta; intros; lia
        | exact STS| exact SYC| exact SYLEN| exact WKR1| exact STK1| exact MI1| exact MU1| exact WM1| exact FR1| exact FFC1| exact FR561]. }
    (eapply (x1_h1A RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF r) with (hw := hw) (rank := rank) (dt := dt) (tl := tl) (nbs := nbs); sect);
      [exact MI| exact FR| exact FFC| exact DTC0| exact DTLEN| exact DTBY| exact DTZ0| lia| exact NBSR| |].
    - (* [comment removed for export] *)
      intros TL11 ya0 ya1.
      eapply (TAIL m5 hw rank tl); first [exact STATS| lia| exact LHW| exact BHW| exact LRK0| exact MI| apply munch_refl| apply wmono_refl| exact STK| exact FR| exact FFC| exact FR56| exact DTC0| exact HWC| exact RK| exact WS1| exact WKR].
    - (* [comment removed for export] *)
      intros TL10 ya1.
      (eapply (x1_h2A RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF r) with (hw := hw) (rank := rank) (tl := tl) (nbs := nbs) (dt := dt) (m1 := m5); sect);
        first [exact STATS| lia| exact NBSR| exact LHW| exact BHW| exact LRK0| exact MI| apply munch_refl| apply wmono_refl| exact STK| exact FR| exact FFC| exact FR56| exact DTC0| exact DTLEN| exact HWC| exact RK| exact WS1| exact WKR| idtac].
      intros m2 hw' rank' y5 y6 ya0' ya1' ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ST' LH' BH' LR' MI2 MU2 WM2 STK2 FR2 FFC2 FR562 DTC2 HWC2 RK2 WS2 WKR2.
      eapply (TAIL m2 hw' rank' 11); first [exact ST'| lia| exact LH'| exact BH'| exact LR'| exact MI2| exact MU2| exact WM2| exact STK2| exact FR2| exact FFC2| exact FR562| exact DTC2| exact HWC2| exact RK2| exact WS2| exact WKR2].
  Qed.
End X1B.
End CANSEC1.
