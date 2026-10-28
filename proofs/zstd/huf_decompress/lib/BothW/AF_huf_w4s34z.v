(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b AF_huf_w4s34k AF_huf_w4s34k2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Stdio_pure.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).

Lemma w4s34_sub2 : forall lo hi lo' hi' A B, lo' <= lo -> hi <= hi' -> sub_fp [(lo, hi); (A, B)] [(lo', hi'); (A, B)].
Proof. intros lo hi lo' hi' A B H1 H2 x Hx. cbn [outside] in *. lia. Qed.

Lemma w4s34_c4n : forall segs m A c bw pad p a e,
  rw_cells segs m A [C8 c; C4 bw; CB 4 pad; C8 p; C8 a; C8 e] ->
  rw_cells segs m A [C8 c; C4 (Z_to_bv 64 (bv_unsigned bw mod 2^32)); CB 4 pad; C8 p; C8 a; C8 e].
Proof.
  intros segs m A c bw pad p a e H.
  apply (Stdio_pure.rw_cells_C4_eq segs m A [C8 c] bw (Z_to_bv 64 (bv_unsigned bw mod 2^32)) [CB 4 pad; C8 p; C8 a; C8 e]); [|exact H].
  pose proof (bv_unsigned_in_range _ bw) as R. pose proof (Z.mod_pos_bound (bv_unsigned bw) (2^32) ltac:(lia)) as B.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite (Z.mod_small (bv_unsigned bw mod 2^32) (2^64)) by lia. rewrite Zmod_mod. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.

Theorem w4s34_g4 : w4s34_g4_case.
Proof.
  unfold w4s34_g4_case.
  intros until j. intros FR MI RS HD HC HS HQ HJ HJ2 HSP HDT HT HR HDL KT KE.
  destruct (Z_lt_le_dec (3 * seg + q + j) dcap) as [HL|HL].
  - Time kx_runFLd [0x8c514; 0x8c5c4] 40%nat (repeat false 8)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange j 0 (2^32);
        KZRange SP (0x10007fff8000 + 2720) (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZRange (64 - tl) 52 63;
        KZRange (dcap - 3 * seg - q - j) 1 (2^32); KZWord (SP + -384) 8 (DST + dcap)]
      [] [(SP + -480, 480)] [].
    all: try w4br5.
    all: try w4br.
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; try (change (mem_denot _ mm []) with mm);
        try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
        try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
        try w4_fix_x5 dl tl rsv;
        try replace (Z_to_bv 64 (DST + (3 * seg + (q + j)))) with (Z_to_bv 64 (DST + 3 * seg + q + j)) by (f_equal; lia) end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => exact (KT HL) end).
  - Time kx_runFLd [0x8c514; 0x8c5c4] 40%nat (repeat false 8)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange j 0 (2^32);
        KZRange SP (0x10007fff8000 + 2720) (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZRange (64 - tl) 52 63;
        KZRange (dcap - 3 * seg - q - j) 0 0; KZWord (SP + -384) 8 (DST + dcap)]
      [] [(SP + -480, 480)] [].
    all: try w4br5.
    all: try w4br.
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; try (change (mem_denot _ mm []) with mm);
        try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
        try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
        try w4_fix_x5 dl tl rsv;
        try replace (Z_to_bv 64 (DST + (3 * seg + (q + j)))) with (Z_to_bv 64 (DST + 3 * seg + q + j)) by (f_equal; lia) end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => eapply KE; lia end).
Time Qed.

Theorem w4s34_t4b : w4s34_t4b_case.
Proof.
  unfold w4s34_t4b_case.
  intros until j. intros FR DS. do 47 intro. intros KT KD.
  destruct (Z_lt_le_dec (3 * seg + q + j + 1) dcap) as [HL|HL].
  - kx_runFLd [0x8c514; 0x8c5c4] 200%nat (false :: false :: repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange b 0 (2^32 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange j 0 (2^32); KZRange c 0 (2^64 - 1);
       KZRange (dcap - 3 * seg - q - j) 2 (2^32);
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b;
       KZWr (SP + -224) 40; KZWr DST dcap; KZWord (SP + -384) 8 (DST + dcap);
       KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (DT + 4, 2 * 2^tl)] [(DT + 4, 2 * 2^tl); (DST, dcap)].
    all: try w4br5.
    all: try w4br.
    all: try w4word4.
    all: try w4shd.
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
        apply (w4_shd8 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
        apply (w4_shd4 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
        apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4s34_xbs | w4s34_xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc;
        try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
        try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + 3 * seg + q + j + 1)) with (Z_to_bv 64 (DST + 3 * seg + q + (j + 1))) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + 3 * seg + q)) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia) end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -224 => fail | _ => kx_frame H end end end).
    all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
        repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
          let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
    all: try (lazymatch goal with HD : rw_cells _ _ (_ + -224) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
    all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
        pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        pose proof (munch_refl [(DST + 3 * seg + q + j, DST + 3 * seg + q + j + 1); (SP + -224, SP + -184)] mm) as MUW;
        kx_munch_wins MUW [(DST + 3 * seg + q + j, 1); (SP + -224, 40)];
        apply (munch_weaken _ [(DST, DST + dcap); (SP + -224, SP + -184)]) in MUW; [ | apply w4s34_sub2; lia ] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => eapply KT end).
    all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
    all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
    all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ < _ => lia | _ => eassumption end).
    all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
    all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
        apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
          cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
        apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  - kx_runFLd [0x8c514; 0x8c5c4] 200%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange b 0 (2^32 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange j 0 (2^32); KZRange c 0 (2^64 - 1);
       KZRange (dcap - 3 * seg - q - j) 1 1;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b;
       KZWr (SP + -224) 40; KZWr DST dcap; KZWord (SP + -384) 8 (DST + dcap);
       KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (DT + 4, 2 * 2^tl)] [(DT + 4, 2 * 2^tl); (DST, dcap)].
    all: try w4br5.
    all: try w4br.
    all: try w4word4.
    all: try w4shd.
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
        apply (w4_shd8 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
        apply (w4_shd4 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
        apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4s34_xbs | w4s34_xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc;
        try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
        try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + 3 * seg + q + j + 1)) with (Z_to_bv 64 (DST + 3 * seg + q + (j + 1))) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + 3 * seg + q)) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia) end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -224 => fail | _ => kx_frame H end end end).
    all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
        repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
          let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
    all: try (lazymatch goal with HD : rw_cells _ _ (_ + -224) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
    all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
        pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        pose proof (munch_refl [(DST + 3 * seg + q + j, DST + 3 * seg + q + j + 1); (SP + -224, SP + -184)] mm) as MUW;
        kx_munch_wins MUW [(DST + 3 * seg + q + j, 1); (SP + -224, 40)];
        apply (munch_weaken _ [(DST, DST + dcap); (SP + -224, SP + -184)]) in MUW; [ | apply w4s34_sub2; lia ] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => eapply KD end).
    all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
    all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
    all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ < _ => lia | _ => eassumption end).
    all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
    all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
        apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
          cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
        apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Time Qed.

Theorem w4s34_t4 : w4s34_t4_case.
Proof.
  pose proof w4s34_t4b as T4B. unfold w4s34_t4b_case in T4B. unfold w4s34_t4_case.
  induction n as [|n IH]; intros until j; intros HN MU WM; intros.
  - lia.
  - eapply T4B with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption.
    + intros mm' ob' bw' y5 y6 y7 y8 y9 y11 y12 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 MU' WM' MI' U' UL' FR' DS' BT' UZ1 UZ2 ZT' HLT.
      apply w4s34_c4n in DS'.
      pose proof (munch_trans _ _ _ _ MU MU') as MU2. pose proof (wmono_trans _ _ _ _ WM WM') as WM2.
      eapply IH with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
    + intros mm' ob' cw' bw' pw' aw' ew'. intros.
      match goal with KD : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => eapply KD end; try eassumption; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption].
Time Qed.

End CANSEC1.










