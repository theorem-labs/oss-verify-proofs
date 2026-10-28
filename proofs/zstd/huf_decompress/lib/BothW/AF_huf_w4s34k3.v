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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s34k3h AF_huf_w4s34k3a AF_huf_w4s34k3b AF_huf_w4s34k3c AF_huf_w4s34k3d.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).



Section CANSEC1. Context {rc : runConstT}.
Lemma w4s34_hca : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q + i + 4 <= dcap -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y1 y7 y8 y9 y10 y12 y13 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST + 3 * seg + q + i, DST + 3 * seg + q + i + 4); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
              C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
              C8 (Z_to_bv 64 (DST + dcap))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) y7 y8 y9 y10 (Z_to_bv 64 b') y12 y13
                 (Z_to_bv 64 64) (Z_to_bv 64 (i + 4)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
            F (Z_to_bv 64 0x8c024) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  assert (HB : b <= 7 \/ 8 <= b <= 15 \/ 16 <= b <= 23 \/ 24 <= b <= 31 \/ 32 <= b <= 39 \/ 40 <= b <= 47 \/
               48 <= b <= 55 \/ 56 <= b <= 63) by lia.
  let ap L := (eapply L with (S := S) (off := off) (len := len) (c := c) (pad1 := pad1) (bs := bs) (cbs := cbs)
      (ob := ob) (dcap := dcap) (rsv := rsv) (w0 := w0) (w8 := w8) (w16 := w16) (w40 := w40) (w48 := w48) (w56 := w56)
      (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3)) in
  destruct HB as [HB | [HB | [HB | [HB | [HB | [HB | [HB | HB]]]]]]];
    [ ap w4s34_hb0 | ap w4s34_hb1 | ap w4s34_hb2 | ap w4s34_hb3
    | ap w4s34_hb4 | ap w4s34_hb5 | ap w4s34_hb6 | ap w4s34_hb7 ].
  all: first [assumption | lia].
Qed.

Theorem w4s34_hcb : w4s34_hcb_case.
Proof.
  unfold w4s34_hcb_case.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [573504] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 7; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 (2^32);
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4s34_fix_srlw3 b; w4_phase_clear end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 7; KZRange (b / 8) 0 8; KZRange (b / 8 - off) 1 8; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 (2^32);
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] end).
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx0 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 0 <= b <= 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 7; KZRange b 0 7; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 <= b <= 15 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 7; KZRange b 8 15; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 2 <= off <= 7 -> 16 <= b <= 23 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 7; KZRange b 16 23; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 3 <= off <= 7 -> 24 <= b <= 31 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 7; KZRange b 24 31; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 4 <= off <= 7 -> 32 <= b <= 39 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 7; KZRange b 32 39; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 5 <= off <= 7 -> 40 <= b <= 47 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 7; KZRange b 40 47; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx6 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 6 <= off <= 7 -> 48 <= b <= 55 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 7; KZRange b 48 55; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx7 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 7 <= off <= 7 -> 56 <= b <= 63 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 56 63; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br6 b.
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
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hcx : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  assert (HB : b <= 7 \/ 8 <= b <= 15 \/ 16 <= b <= 23 \/ 24 <= b <= 31 \/ 32 <= b <= 39 \/ 40 <= b <= 47 \/
               48 <= b <= 55 \/ 56 <= b <= 63) by lia.
  let ap L := (eapply L with (S := S) (off := off) (len := len) (c := c) (pad1 := pad1) (bs := bs) (cbs := cbs)
      (ob := ob) (dcap := dcap) (rsv := rsv) (w0 := w0) (w8 := w8) (w16 := w16) (w40 := w40) (w48 := w48) (w56 := w56)
      (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3)) in
  destruct HB as [HB | [HB | [HB | [HB | [HB | [HB | [HB | HB]]]]]]];
    [ ap w4s34_hcx0 | ap w4s34_hcx1 | ap w4s34_hcx2 | ap w4s34_hcx3
    | ap w4s34_hcx4 | ap w4s34_hcx5 | ap w4s34_hcx6 | ap w4s34_hcx7 ].
  all: first [assumption | lia].
Qed.

End CANSEC1.





