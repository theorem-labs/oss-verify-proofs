(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw Stdio_pure.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).



Lemma w4s32_sub2 : forall lo hi lo' hi' A B, lo' <= lo -> hi <= hi' -> sub_fp [(lo, hi); (A, B)] [(lo', hi'); (A, B)].
Proof. intros lo hi lo' hi' A B H1 H2 x Hx. cbn [outside] in *. lia. Qed.

Lemma w4s32_c4n : forall segs m A c bw pad p a e,
  rw_cells segs m A [C8 c; C4 bw; CB 4 pad; C8 p; C8 a; C8 e] ->
  rw_cells segs m A [C8 c; C4 (Z_to_bv 64 (bv_unsigned bw mod 2^32)); CB 4 pad; C8 p; C8 a; C8 e].
Proof.
  intros segs m A c bw pad p a e H.
  apply (rw_cells_C4_eq segs m A [C8 c] bw (Z_to_bv 64 (bv_unsigned bw mod 2^32)) [CB 4 pad; C8 p; C8 a; C8 e]); [|exact H].
  pose proof (bv_unsigned_in_range _ bw) as R. pose proof (Z.mod_pos_bound (bv_unsigned bw) (2^32) ltac:(lia)) as B.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite (Z.mod_small (bv_unsigned bw mod 2^32) (2^64)) by lia. rewrite Zmod_mod. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.


Lemma w4s32_ts2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 : word)
    (SP DST seg q j DT dl tl rsv : Z),
  mem_inv bsegs mm ->
  4096 <= DST <= 2^47 -> 0 <= seg <= 2^32 -> 0 <= q <= 2^32 -> 0 <= j <= 2^32 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= DT <= 2^47 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q + j)) x9
               (Z_to_bv 64 (DST + seg + q + j)) x11 x12 (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 2)
               x16 x17 (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b8dc) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q + j)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b8c8) fc None mm (seg_rom bsegs)).
Proof.
  intros until rsv. intros MI HD HS HQ HJ HSP HDT HT HR HDL K.
  kx_runFLd [0x8b8dc; 0x8b994] 100%nat (repeat false 64)
      [KZRange (64 - tl) 52 63; KZRange DST 4096 (2^47); KZRange seg 0 (2^32);
       KZRange q 0 (2^32); KZRange j 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47); KZRange DT 4096 (2^47);
       KZRange tl 1 12; KZRange rsv 0 255]
      [] [] [].
  all: try w4br.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc;
      replace (- DT + -5) with (- DT - 5) by lia;
      match goal with |- context [edenot ?E (EAlu ALU_AND (EAluw ALU_SUB (ELit 0) ?v) (ELit 63))] =>
        rewrite (w4s32_negsh E v tl rsv HT HR) by w4uz end;
      exact K end).
Qed.


Lemma w4s32_t2b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x11 x12 x16 x17 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pw aw ew : word) (pad1 : list byte) (cbs ob : list byte)
    (SP DST dcap seg q DT dl b c tl rsv j : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A2 L2 A3 L3 : Z), A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A2 -> 0 <= A3 ->
  A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -480) 480 ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + j < seg -> 0 <= j -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^32 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (bw' : word) (y5 y6 y7 y9 y11 y12 y16 y17 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 bw'; CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
     bytes_at bsegs mm' (DT + 4) cbs -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
     q + j + 1 < seg ->
     evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6
               y7 (Z_to_bv 64 (DST + seg + q + (j + 1))) y9 (Z_to_bv 64 (DST + seg + q + (j + 1))) y11 y12 (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 2) y16 y17 (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4))
               y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b8dc) fc None mm' (seg_rom bsegs))) ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6
               x7 (Z_to_bv 64 (DST + seg + q + j)) x9 (Z_to_bv 64 (DST + seg + q + j)) x11 x12 (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 2) x16 x17 (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b8dc) fc None mm (seg_rom bsegs)).
Proof.
  intros until j. intros FR DS. do 47 intro. intros KT KD.
  destruct (Z_lt_le_dec (q + j + 1) seg) as [HL|HL].
  - kx_runFLd [0x8b8dc; 0x8b994] 200%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange b 0 (2^32 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange j 0 (2^32); KZRange c 0 (2^64 - 1);
       KZRange (seg - q - j) 2 (2^32); KZRange (dcap - seg - q - j) 1 (2^32);
       KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
       KZWr (SP + -144) 40; KZWr DST dcap;
       KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (DT + 4, 2 * 2^tl)] [(DT + 4, 2 * 2^tl); (DST, dcap)].
    all: try w4br.
    all: try w4word4.
    all: try w4shd.
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc;
        try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
        try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + seg + q + j + 1)) with (Z_to_bv 64 (DST + seg + q + (j + 1))) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + 3 * seg + q)) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia) end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -144 => fail | _ => kx_frame H end end end).
    all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
        repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
          let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
    all: try (lazymatch goal with HD : rw_cells _ _ (_ + -144) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
    all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
        pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        pose proof (munch_refl [(DST + seg + q + j, DST + seg + q + j + 1); (SP + -144, SP + -104)] mm) as MUW;
        kx_munch_wins MUW [(DST + seg + q + j, 1); (SP + -144, 40)];
        apply (munch_weaken _ [(DST, DST + dcap); (SP + -144, SP + -104)]) in MUW; [ | apply w4s32_sub2; lia ] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => eapply KT end).
    all: try (lazymatch goal with |- rw_cells _ _ (_ + -144) _ => kx_cells_merge end).
    all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
    all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ < _ => lia | _ => eassumption end).
    all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
    all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
        apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
          cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
        apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
        apply (w4_shd_ap E X B O k); [ try w4xb | try lia | try lia | try w4uz | try w4uz | try w4apz ] end).
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
        apply (w4_shd4 E X B O k); [ try w4xb | try lia | try lia | try w4uz | try w4uz | try w4apz ] end).
  - kx_runFLd [0x8b8dc; 0x8b994] 200%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange b 0 (2^32 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange j 0 (2^32); KZRange c 0 (2^64 - 1);
       KZRange (seg - q - j) 1 1; KZRange (dcap - seg - q - j) 1 (2^32);
       KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
       KZWr (SP + -144) 40; KZWr DST dcap;
       KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (DT + 4, 2 * 2^tl)] [(DT + 4, 2 * 2^tl); (DST, dcap)].
    all: try w4br.
    all: try w4word4.
    all: try w4shd.
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc;
        try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
        try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + seg + q + j + 1)) with (Z_to_bv 64 (DST + seg + q + (j + 1))) by (f_equal; lia);
        try replace (Z_to_bv 64 (DST + 3 * seg + q)) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia) end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -144 => fail | _ => kx_frame H end end end).
    all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
        repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
          let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
    all: try (lazymatch goal with HD : rw_cells _ _ (_ + -144) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
    all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
        pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
    all: try (lazymatch goal with |- evtF _ _ _ _ =>
        pose proof (munch_refl [(DST + seg + q + j, DST + seg + q + j + 1); (SP + -144, SP + -104)] mm) as MUW;
        kx_munch_wins MUW [(DST + seg + q + j, 1); (SP + -144, 40)];
        apply (munch_weaken _ [(DST, DST + dcap); (SP + -144, SP + -104)]) in MUW; [ | apply w4s32_sub2; lia ] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => eapply KD end).
    all: try (lazymatch goal with |- rw_cells _ _ (_ + -144) _ => kx_cells_merge end).
    all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
    all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ < _ => lia | _ => eassumption end).
    all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
    all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
        apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
          cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
    all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
        apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
    all: try w4shd.
    all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
        apply (w4_shd4 E X B O k); [ w4xb | lia | lia | w4uz | w4uz | w4apz ] end).
Qed.


Lemma w4s32_t2 : forall (n : nat) (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x11 x12 x16 x17 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pw aw ew : word) (pad1 : list byte) (cbs ob : list byte)
    (SP DST dcap seg q DT dl b c tl rsv j : Z),
    seg - q - j = Z.of_nat n ->
  munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm -> wmono bsegs mm0 mm ->
rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A2 L2 A3 L3 : Z), A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A2 -> 0 <= A3 ->
  A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -480) 480 ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + j < seg -> 0 <= j -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^32 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6
               x7 (Z_to_bv 64 (DST + seg + q + j)) x9 (Z_to_bv 64 (DST + seg + q + j)) x11 x12 (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 2) x16 x17 (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b8dc) fc None mm (seg_rom bsegs)).
Proof.
  induction n as [|n IH]; intros until j; intros HN MU WM; intros.
  - lia.
  - eapply w4s32_t2b with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption.
    + intros mm' ob' bw' y5 y6 y7 y9 y11 y12 y16 y17 y23 y25 y27 y28 y29 y30 y31 MU' WM' MI' U' UL' FR' DS' BT' UZ1 UZ2 ZT' HLT.
      apply w4s32_c4n in DS'.
      pose proof (munch_trans _ _ _ _ MU MU') as MU2. pose proof (wmono_trans _ _ _ _ WM WM') as WM2.
      eapply IH with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
    + intros mm' ob' cw' bw' pw' aw' ew'. intros.
      match goal with KD : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => eapply KD end; try eassumption; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption].
Qed.

Lemma w4s32_tsd : forall (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pw aw ew : word) (pad1 : list byte) (cbs ob : list byte)
    (SP DST dcap seg q DT dl b c tl rsv j : Z),
  munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm -> wmono bsegs mm0 mm ->
rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A2 L2 A3 L3 : Z), A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A2 -> 0 <= A3 ->
  A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -480) 480 ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + j < seg -> 0 <= j -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^32 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q + j)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b8c8) fc None mm (seg_rom bsegs)).
Proof.
  intros. eapply w4s32_ts2; try eassumption; try lia.
  eapply (w4s32_t2 (Z.to_nat (seg - q - j))) with (mm0 := mm0) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3);
    try eassumption; try lia.
Qed.

Lemma w4s32_j2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 : word)
    (SP DST seg q i DT dl tl rsv : Z),
  mem_inv bsegs mm ->
  4096 <= DST <= 2^47 -> 0 <= seg <= 2^32 -> 0 <= q <= 2^32 -> 0 <= i -> q + i <= seg ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= DT <= 2^47 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  (q + i = seg ->
    evtF bsegs RNG Q
        (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q + i)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg))
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) x23
                 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 571796) fc None mm (seg_rom bsegs))) ->
  (q + i < seg ->
    evtF bsegs RNG Q
        (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q + i)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg))
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) x23
                 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 571592) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q + i)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 571588) fc None mm (seg_rom bsegs)).
Proof.
  intros until rsv. intros MI HD HS HQ HI HQI HSP HDT HT HR HDL KD KT.
  destruct (Z.eq_dec (q + i) seg) as [HE|HE];
  [ kx_runFLd [571592; 571796] 16%nat (repeat true 4) [KZRange (seg - q - i) 0 0; KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange i 0 (2^32); KZRange SP 4096 (2^47)] [] [] []
  | kx_runFLd [571592; 571796] 16%nat (repeat true 4) [KZRange (seg - q - i) 1 (2^32); KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange i 0 (2^32); KZRange SP 4096 (2^47)] [] [] [] ].
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc;
      first [ exact (KD HE) | exact (KT ltac:(lia)) ] end).
Qed.

Lemma w4s32_jsd : forall (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pw aw ew : word) (pad1 : list byte) (cbs ob : list byte)
    (SP DST dcap seg q DT dl b c tl rsv j : Z),
  munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm -> wmono bsegs mm0 mm ->
rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A2 L2 A3 L3 : Z), A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A2 -> 0 <= A3 ->
  A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -480) 480 ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + j <= seg -> 0 <= j -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^32 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q + j)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 571588) fc None mm (seg_rom bsegs)).
Proof.
  intros. eapply (w4s32_j2 _ _ _ _ _ gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 SP DST seg q j DT dl tl rsv);
    try eassumption; try lia.
  - intros HE. match goal with KD : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => eapply KD end;
      try eassumption.
  - intros HE. eapply w4s32_tsd with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
Qed.

End CANSEC1.
