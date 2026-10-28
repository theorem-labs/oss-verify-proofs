(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b AF_huf_w4s33z AF_huf_w4s33k.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw Stdio_pure.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Set Ltac Backtrace. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).


Section CANSEC1. Context {rc : runConstT}.
Lemma w4s33_x81a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 8 <= off -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 8 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 16 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 8 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 16 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x81b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> 1 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 1 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 1 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Ltac w4x3_b8 :=
  lazymatch goal with |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?X (ELit 3)))] =>
    let Q := fresh "Q" in
    assert (Q : bv_unsigned (edenot E (EAluw ALU_SRL X (ELit 3))) = bv_unsigned (edenot E X) / 8);
    [ change (edenot E (EAluw ALU_SRL X (ELit 3))) with (sext 64 (alu32 ALU_SRL (low32 (edenot E X)) (low32 (edenot E (ELit 3)))));
      rewrite (u_srlw_small (edenot E X) (edenot E (ELit 3)) 3);
      [ reflexivity | vm_compute; reflexivity
      | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
      | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        replace (2 ^ (3 mod 32)) with 8 by reflexivity; lia ]
    | rewrite Q; clear Q;
      let b0 := eval unfold E in E in
      lazymatch b0 with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        rewrite (ez_ok zv E (kE_atoms zv xs) X); cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end;
      rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
      Z.div_mod_to_equations; lia ]
  end.

Lemma w4x3_br_nzl : forall E P k, 0 <= k <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (ELit k)) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P k HK HP.
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HKu : bv_unsigned (Z_to_bv 64 k) = k)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; apply Z.mod_small; lia).
  rewrite HKu.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) k).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) k) by (apply Z.lxor_nonneg; split; intros; lia).
    assert (Z.lxor (bv_unsigned (edenot E P)) k <> 0) by (intros H0; pose proof (Z.lxor_eq _ _ H0); lia).
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) k) 1); [lia|].
  reflexivity.
Qed.

Lemma w4s33_x3s1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 1 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 0 15; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 0 15; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3s2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 2 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 0 23; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 0 23; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3s3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 3 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 0 31; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 0 31; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3s4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 4 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 0 39; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 0 39; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3s5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 5 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 0 47; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 0 47; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3s6 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 6 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 0 55; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 0 55; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3s7 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 7 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 0 63; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 0 63; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 3; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> seg < q + i + 4 -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len.
  destruct (Z.eq_dec off 1) as [HO1|HO1]; [exact (w4s33_x3s1 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO1) |].
  destruct (Z.eq_dec off 2) as [HO2|HO2]; [exact (w4s33_x3s2 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO2) |].
  destruct (Z.eq_dec off 3) as [HO3|HO3]; [exact (w4s33_x3s3 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO3) |].
  destruct (Z.eq_dec off 4) as [HO4|HO4]; [exact (w4s33_x3s4 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO4) |].
  destruct (Z.eq_dec off 5) as [HO5|HO5]; [exact (w4s33_x3s5 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO5) |].
  destruct (Z.eq_dec off 6) as [HO6|HO6]; [exact (w4s33_x3s6 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO6) |].
  destruct (Z.eq_dec off 7) as [HO7|HO7]; [exact (w4s33_x3s7 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO7) |].
  intros. exfalso. lia.
Qed.

Lemma w4s33_x3e1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 1 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 16 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 16 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3e2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 2 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 24 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 24 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3e3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 3 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 32 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 32 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3e4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 4 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 40 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 40 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3e5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 5 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 48 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 48 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3e6 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 6 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 56 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 56 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3e7 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 7 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q - i) 0) as [HE|HE]; [
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 64 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 0 0; KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8b9d0; 0x8bee4; 0x8bff0; 0x8bfb0] 400%nat (true :: true :: true :: repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
      KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 64 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
      KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (len - off) 8 (2^32);
      KZRange (seg - q - i) 1 (2^32); KZRange (dcap - 2 * seg - q - i) 0 (2^32);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
      KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
      KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
      KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true => apply (w4x3_br_nzl E P k); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      replace (Z_to_bv 64 (DST + 2 * seg + i + q)) with (Z_to_bv 64 (DST + 2 * seg + q + i)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - i))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4x3_b8 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_x3e : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 8 <= b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len.
  destruct (Z.eq_dec off 1) as [HO1|HO1]; [exact (w4s33_x3e1 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO1) |].
  destruct (Z.eq_dec off 2) as [HO2|HO2]; [exact (w4s33_x3e2 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO2) |].
  destruct (Z.eq_dec off 3) as [HO3|HO3]; [exact (w4s33_x3e3 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO3) |].
  destruct (Z.eq_dec off 4) as [HO4|HO4]; [exact (w4s33_x3e4 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO4) |].
  destruct (Z.eq_dec off 5) as [HO5|HO5]; [exact (w4s33_x3e5 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO5) |].
  destruct (Z.eq_dec off 6) as [HO6|HO6]; [exact (w4s33_x3e6 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO6) |].
  destruct (Z.eq_dec off 7) as [HO7|HO7]; [exact (w4s33_x3e7 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO7) |].
  intros. exfalso. lia.
Qed.

Lemma w4s33_l3s5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 5 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i + 4 <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y8 y10 y12 y13 y28 y29 y30 y31 : word),
     munch [(DST + 2 * seg + q + i, DST + 2 * seg + q + i + 4); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) y8 x9 y10 (Z_to_bv 64 b') y12 y13
               (Z_to_bv 64 64) (Z_to_bv 64 (i + 4)) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x8b9d0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO. intros.
  kx_runFLd [0x8b9d0; 0x8bec8; 0x8bfb0; 0x8bee4; 0x8bff0] 400%nat (true :: true :: true :: false :: false :: false :: repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 0 47; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (seg - q - i) 4 (2^32); KZRange (dcap - 2 * seg - q - i) 4 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br_bsum.
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + 3 * seg + -3)) with (Z_to_bv 64 (DST + 3 * seg - 3)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST + 2 * seg + q + i, DST + 2 * seg + q + i + 4); (SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(DST + 2 * seg + q + i, 4); (SP + -184, 40)] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => w4_c4_bsum end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try w4_bsum_rng.
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Qed.

Lemma w4s33_l3s6 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 6 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i + 4 <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y8 y10 y12 y13 y28 y29 y30 y31 : word),
     munch [(DST + 2 * seg + q + i, DST + 2 * seg + q + i + 4); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) y8 x9 y10 (Z_to_bv 64 b') y12 y13
               (Z_to_bv 64 64) (Z_to_bv 64 (i + 4)) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x8b9d0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO. intros.
  kx_runFLd [0x8b9d0; 0x8bec8; 0x8bfb0; 0x8bee4; 0x8bff0] 400%nat (true :: true :: true :: false :: false :: false :: repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 0 55; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (seg - q - i) 4 (2^32); KZRange (dcap - 2 * seg - q - i) 4 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br_bsum.
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + 3 * seg + -3)) with (Z_to_bv 64 (DST + 3 * seg - 3)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST + 2 * seg + q + i, DST + 2 * seg + q + i + 4); (SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(DST + 2 * seg + q + i, 4); (SP + -184, 40)] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => w4_c4_bsum end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try w4_bsum_rng.
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Qed.

Lemma w4s33_l3s7 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  off = 7 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i + 4 <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y8 y10 y12 y13 y28 y29 y30 y31 : word),
     munch [(DST + 2 * seg + q + i, DST + 2 * seg + q + i + 4); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) y8 x9 y10 (Z_to_bv 64 b') y12 y13
               (Z_to_bv 64 64) (Z_to_bv 64 (i + 4)) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x8b9d0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros HO. intros.
  kx_runFLd [0x8b9d0; 0x8bec8; 0x8bfb0; 0x8bee4; 0x8bff0] 400%nat (true :: true :: true :: false :: false :: false :: repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 0 63; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (seg - q - i) 4 (2^32); KZRange (dcap - 2 * seg - q - i) 4 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br_bsum.
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + 3 * seg + -3)) with (Z_to_bv 64 (DST + 3 * seg - 3)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST + 2 * seg + q + i, DST + 2 * seg + q + i + 4); (SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(DST + 2 * seg + q + i, 4); (SP + -184, 40)] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => w4_c4_bsum end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try w4_bsum_rng.
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Qed.

End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
