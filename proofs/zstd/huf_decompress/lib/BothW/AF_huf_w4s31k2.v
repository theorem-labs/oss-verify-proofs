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

Section CANSEC1. Context {rc : runConstT}.


Lemma w4s31_d1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  2^20 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  (seg - q < 4 -> evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q)) x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs))) ->
  (4 <= seg - q -> 64 < b -> evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q)) x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (b)) x12 x13 (Z_to_bv 64 (64)) x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 570144) fc None mm (seg_rom bsegs))) ->
  (4 <= seg - q -> b <= 64 -> forall y10 : word, evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (2)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (18446744073709551615)) (Z_to_bv 64 (DST + seg + q)) x9 y10 (Z_to_bv 64 (b)) x12 x13 (Z_to_bv 64 (64)) (Z_to_bv 64 (0)) (Z_to_bv 64 (DST + seg - 3)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 568540) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) x21 (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 568472) fc None mm (seg_rom bsegs)).
Proof.
  intros until pt. intros FR DS MI RS HD HC HS HQ HQ2 HSP HB HT HR HDL KA KB1 KB2.
    destruct (Z_lt_le_dec (seg - q) 4) as [HA|HA].
  - kx_runFLd [568540; 569580; 570144] 64%nat (repeat true 8) [KZRange (seg - q) 0 3; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -368) 4 b] (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
    all: try w4br.
    all: try w4word4.
    all: try (kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc; exact (KA HA)).
  - destruct (Z_lt_le_dec 64 b) as [HB2|HB2].
    + kx_runFLd [568540; 569580; 570144] 64%nat (repeat true 8) [KZRange (seg - q) 4 (2^32); KZRange b 65 (2^31 - 1); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -368) 4 b] (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
      all: try w4br.
      all: try w4word4.
    all: try w4word4.
      all: try (kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc; exact (KB1 HA HB2)).
    + kx_runFLd [568540; 569580; 570144] 64%nat (repeat true 8) [KZRange (seg - q) 4 (2^32); KZRange b 0 64; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -368) 4 b] (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
      all: try w4br.
      all: try w4word4.
    all: try w4word4.
      all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc; replace (DST + seg + -3) with (DST + seg - 3) by lia; replace (- DT + -5) with (- DT - 5) by lia; match goal with |- context [edenot ?E (EAlu ALU_AND (EAluw ALU_SUB (ELit 0) ?v) (ELit 63))] => rewrite (w4s32_negsh E v tl rsv HT HR) by w4uz end; apply (KB2 HA HB2) end).
Time Qed.


Lemma w4s31_o1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  2^20 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
   4 <= seg - q -> 64 < b ->
   (forall (mm' : amem) (pw' y10 : word),
      munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
               C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
               C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 pw'; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 (Z_to_bv 64 (b)) x12 x13 (Z_to_bv 64 (64)) x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->
   evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (b)) x12 x13 (Z_to_bv 64 (64)) x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31) F (Z_to_bv 64 570144) fc None mm (seg_rom bsegs)).
Proof.
  intros. kx_runFLd [569912; 570176; 569944; 568540; 569580] 64%nat (repeat true 8) [KZRange (seg - q) 4 (2^32); KZRange b 65 (2^31 - 1); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg); KZWord (SP + -448) 8 seg; KZWord (SP + -368) 4 b; KZWr (SP + -376) 40] [] [(SP + -480, 480)] [].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia); try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity); idtac end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -376 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -376) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW; kx_munch_wins MUW [(SP + -376, 40)] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try eassumption.
Time Qed.


End CANSEC1.
