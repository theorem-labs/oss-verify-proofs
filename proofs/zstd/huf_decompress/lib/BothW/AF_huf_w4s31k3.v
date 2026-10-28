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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s32k3.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.


Lemma w4s31_e1a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  2^20 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  seg - q < 4 -> 64 < b ->
  (q = seg -> forall (mm' : amem) (pw' y10 : word),
      munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
               C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
               C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 pw'; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 (Z_to_bv 64 (b)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
  (q < seg -> forall (mm' : amem) (pw' y10 : word),
      munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
               C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
               C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 pw'; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 (Z_to_bv 64 (b)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec q seg) as [HQE|HQE]; [ kx_runFLd [569912; 570176; 569944; 568540; 569876; 569896] 96%nat (repeat true 16) [KZRange (seg - q) 0 0; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg); KZWord (SP + -368) 4 b; KZRange b 65 (2^31 - 1); KZWr (SP + -376) 40] [] [(SP + -480, 480)] [] | kx_runFLd [569912; 570176; 569944; 568540; 569876; 569896] 96%nat (repeat false 16) [KZRange (seg - q) 1 3; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg); KZWord (SP + -368) 4 b; KZRange b 65 (2^31 - 1); KZWr (SP + -376) 40] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia); try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity); idtac end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -376 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -376) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW; kx_munch_wins MUW [(SP + -376, 40)] end).
  all: try (match goal with KK : _ -> forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK; [lia|..] end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try eassumption.
Time Qed.


Lemma w4s31_e1z : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  2^20 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  seg - q < 4 -> b <= 64 -> pt = 0 -> 4096 <= S <= 2^47 ->
  (q = seg -> forall (y10 y11 y12 y14 : word), evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 x13 y14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 570176) fc None mm (seg_rom bsegs))) ->
  (q < seg -> forall (y10 y11 y12 y14 : word), evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 x13 y14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569912) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec q seg) as [HQE|HQE]; [ kx_runFLd [569912; 570176; 569944; 568540; 569876; 569896] 96%nat (repeat true 16) [KZRange (seg - q) 0 0; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg); KZWord (SP + -368) 4 b; KZRange b 0 64; KZWr (SP + -376) 40; KZWord (SP + -360) 8 (S + pt); KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8); KZRange S 4096 (2^47); KZRange pt 0 0] [] [(SP + -480, 480)] [] | kx_runFLd [569912; 570176; 569944; 568540; 569876; 569896] 96%nat (repeat false 16) [KZRange (seg - q) 1 3; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg); KZWord (SP + -368) 4 b; KZRange b 0 64; KZWr (SP + -376) 40; KZWord (SP + -360) 8 (S + pt); KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8); KZRange S 4096 (2^47); KZRange pt 0 0] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc;
      match goal with KK : _ -> forall y10 y11 y12 y14 : word, _ |- _ => eapply KK; lia end end).
Time Qed.

Lemma w4s31_e1ra : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  2^20 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
   seg - q < 4 -> b <= 64 -> 4096 <= S <= 2^47 -> 8 <= pt <= 2^32 ->
   (forall (y11 y12 : word),
 evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 569900) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -376)) y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
   evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs)).
Proof.
  intros. kx_runFLd [569912; 570176; 569944; 568540; 569876; 0x8e354] 96%nat (repeat true 16) [KZRange (seg - q) 0 3; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg); KZWord (SP + -368) 4 b; KZRange b 0 64; KZWr (SP + -376) 40; KZWord (SP + -360) 8 (S + pt); KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8); KZRange S 4096 (2^47); KZRange pt 8 (2^32)] [] [(SP + -480, 480)] [].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc;
      match goal with KK : forall y11 y12 : word, _ |- _ => eapply KK end end).
Time Qed.

Lemma w4s31_e1rb : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word)
    (SP DST dcap seg q DT dl tl rsv : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  2^20 <= SP <= 2^47 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> seg - q < 4 ->
  (q = seg -> evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -376)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 570176) fc None mm (seg_rom bsegs))) ->
  (q < seg -> evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -376)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569912) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 569900) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -376)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569900) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec q seg) as [HQE|HQE]; [ kx_runFLd [569912; 570176; 569944; 568540; 569876; 569896] 96%nat (repeat true 16) [KZRange (seg - q) 0 0; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg)] [] [(SP + -480, 480)] [] | kx_runFLd [569912; 570176; 569944; 568540; 569876; 569896] 96%nat (repeat false 16) [KZRange (seg - q) 1 3; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (2^20) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg)] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot]; rewrite ?Z.add_assoc;
      match goal with KK : _ -> evtF _ _ _ _ |- _ => eapply KK; lia end end).
Time Qed.

Lemma w4s31_e1r : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt lo : Z) (bs : list Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  2^20 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
   seg - q < 4 -> b <= 64 -> 4096 <= S <= 2^47 -> 8 <= pt <= 2^32 ->
   SP mod 8 = 0 -> pt + 8 <= zlen bs ->
   bytes_at bsegs mm S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> ablk S (S + zlen bs) ->
   stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 ->
   artcells mm -> unpoisoned mm (SP + -376) (SP + -336) -> unpoisoned mm S (S + zlen bs) ->
   rng RNG (shad (SP + -376)) 5 -> rng RNG S (zlen bs) -> rng RNG (shad S) (nshad (zlen bs + S mod 8)) ->
   rng RNG (SP + -496) 16 -> rng_aimg RNG -> rng_aimg_sh RNG ->
  (q = seg -> forall (mm' : amem) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 : word),
      munch [(SP + -376, SP + -336); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
      stk bsegs mm' lo (SP + -480) ->
      rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 (le64v bs (pt - b / 8))); C4 (Z_to_bv 64 (b mod 8)); CB 4 pad; C8 (Z_to_bv 64 (S + (pt - b / 8)));
                C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 x8 (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -376)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
  (q < seg -> forall (mm' : amem) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 : word),
      munch [(SP + -376, SP + -336); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
      stk bsegs mm' lo (SP + -480) ->
      rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 (le64v bs (pt - b / 8))); C4 (Z_to_bv 64 (b mod 8)); CB 4 pad; C8 (Z_to_bv 64 (S + (pt - b / 8)));
                C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 x8 (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -376)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->
   evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  eapply w4s31_e1ra; try eassumption.
  intros y11 y12.
  eapply w4_rl_call with (lo := lo) (S := S) (bc := b) (q := pt) (cont := c) (jp := pad) (bs := bs).
  - unfold reload_cellsA. eassumption.
  - eassumption.
  - eassumption.
  - Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - eassumption.
  - lia.
  - lia.
  - lia.
  - eassumption.
  - eassumption.
  - unfold RELOADI_STACK. lia.
  - eassumption.
  - eassumption.
  - replace (SP + -376 + 40) with (SP + -336) by lia. eassumption.
  - eassumption.
  - eapply (rng_sub RNG (SP + -480) 480); [eassumption | lia | lia].
  - eassumption.
  - eassumption.
  - eassumption.
  - unfold RELOADI_STACK. replace (SP + -480 - 16) with (SP + -496) by lia. eassumption.
  - eassumption.
  - eassumption.
  - intros m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 MU WM MI' STK' RW'.
    unfold RELOADI_STACK in MU. replace (SP + -376 + 40) with (SP + -336) in MU by lia.
    replace (SP + -480 - 16) with (SP + -496) in MU by lia.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    assert (FR' : rw_cells bsegs m' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))]).
    { eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize]; lia]. }
    unfold reload_cellsA in RW'.
    eapply w4s31_e1rb; try eassumption; try lia.
    + intros HQ. match goal with KK : q = seg -> forall mm' : amem, _ |- _ => eapply KK; eassumption end.
    + intros HQ. match goal with KK : q < seg -> forall mm' : amem, _ |- _ => eapply KK; eassumption end.
Time Qed.

Lemma w4s31_e1st : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad bs : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt len A1 L1 : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len -> unpoisoned mm S (S + len) -> rng RNG S len ->
  A1 mod 8 = 0 -> 0 <= A1 -> A1 <= S -> S + len <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  seg - q < 4 -> b <= 64 -> 4096 <= S -> S + len <= 2^47 -> 1 <= pt <= 7 -> pt + 8 <= len -> len <= 2^32 ->
  q < seg ->
  (forall (mm' : amem) (c' b' : Z) (pw' y10 y11 y12 y13 y14 y15 : word),
      munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
              C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
              C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad; C8 pw'; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      0 <= c' < 2^64 -> 0 <= b' <= 64 ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->
   evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs)).
Proof.
  intros. assert (HO : pt = 1 \/ pt = 2 \/ pt = 3 \/ pt = 4 \/ pt = 5 \/ pt = 6 \/ pt = 7) by lia.
  let w k blo bhi lmin :=
    kx_runFLd [569912; 570176; 569944; 568540; 569896] 160%nat (repeat true 32)
      [KZRange (seg - q) 1 3; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32);
       KZRange SP (0x10007fff8000 + 2720) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg);
       KZWord (SP + -368) 4 b; KZRange b blo bhi; KZWr (SP + -376) 40; KZWord (SP + -360) 8 (S + k);
       KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47);
       KZRange len lmin (2^32); KZRange (len - k) 8 (2^32); KZDisj S len (SP + -480) 480]
      [(S, len)] [(SP + -480, 480); (S, len)] [(S, len)] in
  destruct HO as [HO | [HO | [HO | [HO | [HO | [HO | HO]]]]]]; subst pt;
    [ destruct (Z_le_gt_dec b 15); [w 1 0 15 9 | w 1 16 64 9]
    | destruct (Z_le_gt_dec b 23); [w 2 0 23 10 | w 2 24 64 10]
    | destruct (Z_le_gt_dec b 31); [w 3 0 31 11 | w 3 32 64 11]
    | destruct (Z_le_gt_dec b 39); [w 4 0 39 12 | w 4 40 64 12]
    | destruct (Z_le_gt_dec b 47); [w 5 0 47 13 | w 5 48 64 13]
    | destruct (Z_le_gt_dec b 55); [w 6 0 55 14 | w 6 56 64 14]
    | destruct (Z_le_gt_dec b 63); [w 7 0 63 15 | w 7 64 64 15] ].
  all: try w4bry.
  all: try w4br_bsum.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia); try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity); idtac end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -376 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -376) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW; kx_munch_wins MUW [(SP + -376, 40)] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => w4_c4_bsum end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => kx_cells_merge end).
  all: try w4_bsum_rng.
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ <= 64 => w4b8 end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; lia end).
  all: try eassumption.
Time Qed.

Lemma w4s31_e1sd : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad bs : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt len A1 L1 : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len -> unpoisoned mm S (S + len) -> rng RNG S len ->
  A1 mod 8 = 0 -> 0 <= A1 -> A1 <= S -> S + len <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  seg - q < 4 -> b <= 64 -> 4096 <= S -> S + len <= 2^47 -> 1 <= pt <= 7 -> pt + 8 <= len -> len <= 2^32 ->
  q = seg ->
  (forall (mm' : amem) (c' b' : Z) (pw' y10 y11 y12 y13 y14 y15 : word),
      munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
              C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
              C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad; C8 pw'; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      0 <= c' < 2^64 -> 0 <= b' <= 64 ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
   evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs)).
Proof.
  intros. assert (HO : pt = 1 \/ pt = 2 \/ pt = 3 \/ pt = 4 \/ pt = 5 \/ pt = 6 \/ pt = 7) by lia.
  let w k blo bhi lmin :=
    kx_runFLd [569912; 570176; 569944; 568540; 569896] 160%nat (repeat true 32)
      [KZRange (seg - q) 0 0; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32);
       KZRange SP (0x10007fff8000 + 2720) (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZWord (SP + -416) 8 (DST + seg);
       KZWord (SP + -368) 4 b; KZRange b blo bhi; KZWr (SP + -376) 40; KZWord (SP + -360) 8 (S + k);
       KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47);
       KZRange len lmin (2^32); KZRange (len - k) 8 (2^32); KZDisj S len (SP + -480) 480]
      [(S, len)] [(SP + -480, 480); (S, len)] [(S, len)] in
  destruct HO as [HO | [HO | [HO | [HO | [HO | [HO | HO]]]]]]; subst pt;
    [ destruct (Z_le_gt_dec b 15); [w 1 0 15 9 | w 1 16 64 9]
    | destruct (Z_le_gt_dec b 23); [w 2 0 23 10 | w 2 24 64 10]
    | destruct (Z_le_gt_dec b 31); [w 3 0 31 11 | w 3 32 64 11]
    | destruct (Z_le_gt_dec b 39); [w 4 0 39 12 | w 4 40 64 12]
    | destruct (Z_le_gt_dec b 47); [w 5 0 47 13 | w 5 48 64 13]
    | destruct (Z_le_gt_dec b 55); [w 6 0 55 14 | w 6 56 64 14]
    | destruct (Z_le_gt_dec b 63); [w 7 0 63 15 | w 7 64 64 15] ].
  all: try w4bry.
  all: try w4br_bsum.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + q)) with (Z_to_bv 64 (DST + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia); try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia); try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity); idtac end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -376 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -376) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW; kx_munch_wins MUW [(SP + -376, 40)] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => w4_c4_bsum end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => kx_cells_merge end).
  all: try w4_bsum_rng.
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ <= 64 => w4b8 end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; lia end).
  all: try eassumption.
Time Qed.

Lemma w4s31_e1s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x8 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad bs : list byte)
    (SP DST dcap seg q DT dl tl rsv b S pt len A1 L1 : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len -> unpoisoned mm S (S + len) -> rng RNG S len ->
  A1 mod 8 = 0 -> 0 <= A1 -> A1 <= S -> S + len <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^31 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  seg - q < 4 -> b <= 64 -> 4096 <= S -> S + len <= 2^47 -> 1 <= pt <= 7 -> pt + 8 <= len -> len <= 2^32 ->
  (q = seg -> forall (mm' : amem) (c' b' : Z) (pw' y10 y11 y12 y13 y14 y15 : word),
      munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
              C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
              C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad; C8 pw'; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      0 <= c' < 2^64 -> 0 <= b' <= 64 ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
  (q < seg -> forall (mm' : amem) (c' b' : Z) (pw' y10 y11 y12 y13 y14 y15 : word),
      munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
              C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
              C8 (Z_to_bv 64 (DST + dcap))] ->
      rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad; C8 pw'; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
      0 <= c' < 2^64 -> 0 <= b' <= 64 ->
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->
   evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) x28 x29 x30 x31) F (Z_to_bv 64 569580) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec q seg) as [HQE|HQE];
    [ eapply w4s31_e1sd with (A1 := A1) (L1 := L1) | eapply w4s31_e1st with (A1 := A1) (L1 := L1) ];
    try eassumption; try lia;
    match goal with KK : _ -> forall mm' : amem, _ |- _ => apply KK; lia end.
Time Qed.

End CANSEC1.
