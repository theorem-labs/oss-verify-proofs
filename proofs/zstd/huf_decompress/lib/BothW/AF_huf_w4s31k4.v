(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation amem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma w4s31_x0 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
    (q + i = seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
           F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
  (q + i < seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + q + i)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) y28 y29 y30 y31)
           F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->

  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (DST + seg + q)) x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + seg - 3)) (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (DST + q)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 seg) x28 x29 x30 x31)
          F (Z_to_bv 64 0x8acdc) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  let w lo hi :=
  kx_runFLd [570176; 569912] 400%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 0 (2^32);
       KZRange (seg - q - i) lo hi; KZRange (dcap - q - i) 0 (2^32);
       KZWord (SP + -376) 8 c; KZWord (SP + -368) 4 b; KZWord (SP + -360) 8 (S + off); KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8);
       KZWr (SP + -376) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] in
  destruct (Z_lt_ge_dec (q + i) seg) as [HE | HE];
    [ match goal with K : q + i = seg -> _ |- _ => clear K end;
      match goal with K : q + i < seg -> _ |- _ => specialize (K HE) end;
      w 1 (2^32)
    | assert (HE' : q + i = seg) by lia;
      match goal with K : q + i < seg -> _ |- _ => clear K end;
      match goal with K : q + i = seg -> _ |- _ => specialize (K HE') end;
      w 0 0 ].
  all: try w4word4.
  all: try w4br.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (seg + q))) with (Z_to_bv 64 (DST + seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia);
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (q + i))) with (Z_to_bv 64 (DST + q + i)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply wmono_refl end).
Time Qed.

(* [comment removed for export] *)
Lemma w4s31_xf : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> seg < q + i + 4 -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 8 <= off -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
    (q + i = seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
           F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
  (q + i < seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + q + i)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) y28 y29 y30 y31)
           F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->

  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (DST + seg + q)) x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + seg - 3)) (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (DST + q)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 seg) x28 x29 x30 x31)
          F (Z_to_bv 64 0x8acdc) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  let w lo hi :=
  kx_runFLd [570176; 569912] 400%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 8 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 16 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (seg - q - i) lo hi; KZRange (dcap - q - i) 0 (2^32);
       KZWord (SP + -376) 8 c; KZWord (SP + -368) 4 b; KZWord (SP + -360) 8 (S + off); KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8);
       KZWr (SP + -376) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] in
  destruct (Z_lt_ge_dec (q + i) seg) as [HE | HE];
    [ match goal with K : q + i = seg -> _ |- _ => clear K end;
      match goal with K : q + i < seg -> _ |- _ => specialize (K HE) end;
      w 1 3
    | assert (HE' : q + i = seg) by lia;
      match goal with K : q + i < seg -> _ |- _ => clear K end;
      match goal with K : q + i = seg -> _ |- _ => specialize (K HE') end;
      w 0 0 ].
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (seg + q))) with (Z_to_bv 64 (DST + seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia);
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (q + i))) with (Z_to_bv 64 (DST + q + i)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -376 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -376) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW;
      kx_munch_wins MUW [(SP + -376, 40)] end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E (EAlu ALU_AND ?Y (ELit 7)))] |- evtF _ _ _ _ =>
      replace (edenot E (EAlu ALU_AND Y (ELit 7))) with (Z_to_bv 64 (bv_unsigned (edenot E (EAlu ALU_AND Y (ELit 7)))))
        in H by (rewrite Z_to_bv_bv_unsigned; reflexivity);
      rewrite (u_and_mask E Y 7 3) in H by first [reflexivity | lia] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- 0 <= ?x mod 2 ^ 3 <= 64 =>
      change (2 ^ 3) with 8; pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB; clear - MB; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ <= 64 =>
    lazymatch goal with |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?X (ELit 3)))] =>
      let Q := fresh "Q" in
      assert (Q : bv_unsigned (edenot E (EAluw ALU_SRL X (ELit 3))) = bv_unsigned (edenot E X) / 8);
      [ change (edenot E (EAluw ALU_SRL X (ELit 3))) with (sext 64 (alu32 ALU_SRL (low32 (edenot E X)) (low32 (edenot E (ELit 3)))));
        rewrite (u_srlw_small (edenot E X) (edenot E (ELit 3)) 3);
        [ reflexivity | vm_compute; reflexivity
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
          replace (2 ^ (3 mod 32)) with 8 by reflexivity; lia ]
      | rewrite Q; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia ]
    end end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Time Qed.

(* [comment removed for export] *)
Lemma w4s31_xs : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> seg < q + i + 4 -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
    (q + i = seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
           F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
  (q + i < seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + q + i)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) y28 y29 y30 y31)
           F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->

  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (DST + seg + q)) x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + seg - 3)) (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (DST + q)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 seg) x28 x29 x30 x31)
          F (Z_to_bv 64 0x8acdc) fc None mm (seg_rom bsegs)).
Proof.
  intros. assert (HO : off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
  let w k bmax lmin lo hi :=
  kx_runFLd [570176; 569912] 400%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off k k; KZRange b 0 bmax; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len lmin (2^32); KZRange (len - off) 8 (2^32);
       KZRange (seg - q - i) lo hi; KZRange (dcap - q - i) 0 (2^32);
       KZWord (SP + -376) 8 c; KZWord (SP + -368) 4 b; KZWord (SP + -360) 8 (S + off); KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8);
       KZWr (SP + -376) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] in
  destruct (Z_lt_ge_dec (q + i) seg) as [HE | HE];
    [ match goal with K : q + i = seg -> _ |- _ => clear K end;
      match goal with K : q + i < seg -> _ |- _ => specialize (K HE) end;
      destruct HO as [HO | [HO | [HO | [HO | [HO | [HO | HO]]]]]];
      [ w 1 15 9 1 3
        | w 2 23 10 1 3
        | w 3 31 11 1 3
        | w 4 39 12 1 3
        | w 5 47 13 1 3
        | w 6 55 14 1 3
        | w 7 63 15 1 3 ]
    | assert (HE' : q + i = seg) by lia;
      match goal with K : q + i < seg -> _ |- _ => clear K end;
      match goal with K : q + i = seg -> _ |- _ => specialize (K HE') end;
      destruct HO as [HO | [HO | [HO | [HO | [HO | [HO | HO]]]]]];
      [ w 1 15 9 0 0
        | w 2 23 10 0 0
        | w 3 31 11 0 0
        | w 4 39 12 0 0
        | w 5 47 13 0 0
        | w 6 55 14 0 0
        | w 7 63 15 0 0 ] ].
  all: try w4br_bsum.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (seg + q))) with (Z_to_bv 64 (DST + seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia);
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (q + i))) with (Z_to_bv 64 (DST + q + i)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -376 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -376) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW;
      kx_munch_wins MUW [(SP + -376, 40)] end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E (EAlu ALU_AND ?Y (ELit 7)))] |- evtF _ _ _ _ =>
      replace (edenot E (EAlu ALU_AND Y (ELit 7))) with (Z_to_bv 64 (bv_unsigned (edenot E (EAlu ALU_AND Y (ELit 7)))))
        in H by (rewrite Z_to_bv_bv_unsigned; reflexivity);
      rewrite (u_and_mask E Y 7 3) in H by first [reflexivity | lia] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => w4_c4_bsum end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => kx_cells_merge end).
  all: try w4_bsum_rng.
  all: try (lazymatch goal with |- 0 <= ?x mod 2 ^ 3 <= 64 =>
      change (2 ^ 3) with 8; pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB; clear - MB; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ <= 64 =>
    lazymatch goal with |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?X (ELit 3)))] =>
      let Q := fresh "Q" in
      assert (Q : bv_unsigned (edenot E (EAluw ALU_SRL X (ELit 3))) = bv_unsigned (edenot E X) / 8);
      [ change (edenot E (EAluw ALU_SRL X (ELit 3))) with (sext 64 (alu32 ALU_SRL (low32 (edenot E X)) (low32 (edenot E (ELit 3)))));
        rewrite (u_srlw_small (edenot E X) (edenot E (ELit 3)) 3);
        [ reflexivity | vm_compute; reflexivity
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
          replace (2 ^ (3 mod 32)) with 8 by reflexivity; lia ]
      | rewrite Q; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia ]
    end end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Time Qed.

(* [comment removed for export] *)
Lemma w4s31_xe : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> 8 * off + 7 < b -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
    (q + i = seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
           F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->
  (q + i < seg -> forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word),
     munch [(SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + q + i)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 seg) y28 y29 y30 y31)
           F (Z_to_bv 64 569912) fc None mm' (seg_rom bsegs))) ->

  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (DST + seg + q)) x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + seg - 3)) (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (DST + q)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 seg) x28 x29 x30 x31)
          F (Z_to_bv 64 0x8acdc) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  assert (BRK : forall E0 P0 k0, 1 <= k0 <= 8 -> 64 < bv_unsigned (edenot E0 P0) ->
    branch_taken BC_NE (edenot E0 (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P0 (ELit k0)) (ELit 1))))
      (edenot E0 (ELit 0)) = true).
  { intros E0 P0 k0 HK HP.
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  replace (bv_unsigned (Z_to_bv 64 k0)) with k0
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E0 P0)) k0).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E0 P0)) k0).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E0 P0)) k0 <> 0).
    { intros HZ0. pose proof (Z.lxor_eq _ _ HZ0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E0 P0)) k0) 1); [lia|].
  reflexivity. }
  assert (HO : off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
  let w k bmax lmin lo hi :=
  kx_runFLd [570176; 569912] 400%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off k k; KZRange b bmax 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len lmin (2^32); KZRange (len - off) 8 (2^32);
       KZRange (seg - q - i) lo hi; KZRange (dcap - q - i) 0 (2^32);
       KZWord (SP + -376) 8 c; KZWord (SP + -368) 4 b; KZWord (SP + -360) 8 (S + off); KZWord (SP + -352) 8 S; KZWord (SP + -344) 8 (S + 8);
       KZWr (SP + -376) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] in
  destruct (Z_lt_ge_dec (q + i) seg) as [HE | HE];
    [ match goal with K : q + i = seg -> _ |- _ => clear K end;
      match goal with K : q + i < seg -> _ |- _ => specialize (K HE) end;
      destruct HO as [HO | [HO | [HO | [HO | [HO | [HO | HO]]]]]];
      [ w 1 16 9 1 (2^32)
        | w 2 24 10 1 (2^32)
        | w 3 32 11 1 (2^32)
        | w 4 40 12 1 (2^32)
        | w 5 48 13 1 (2^32)
        | w 6 56 14 1 (2^32)
        | w 7 64 15 1 (2^32) ]
    | assert (HE' : q + i = seg) by lia;
      match goal with K : q + i < seg -> _ |- _ => clear K end;
      match goal with K : q + i = seg -> _ |- _ => specialize (K HE') end;
      destruct HO as [HO | [HO | [HO | [HO | [HO | [HO | HO]]]]]];
      [ w 1 16 9 0 0
        | w 2 24 10 0 0
        | w 3 32 11 0 0
        | w 4 40 12 0 0
        | w 5 48 13 0 0
        | w 6 56 14 0 0
        | w 7 64 15 0 0 ] ].
  all: try w4br_bsum.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
      (EAlu ALU_XOR ?P (ELit ?K)) (ELit 1)))) (edenot ?E (ELit 0)) = true =>
      apply (BRK E P K); [lia | w4uz] end).
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      try replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (seg + q))) with (Z_to_bv 64 (DST + seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + seg + -3)) with (Z_to_bv 64 (DST + seg - 3)) by (f_equal; lia);
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (2 * seg + q))) with (Z_to_bv 64 (DST + 2 * seg + q)) by (f_equal; lia);
      try replace (Z_to_bv 64 (DST + (q + i))) with (Z_to_bv 64 (DST + q + i)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -376 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -376) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (match goal with H : rw_cells _ _ (_ + -360) [C8 (Z_to_bv 64 ?e)],
      HS : rw_cells _ _ (_ + -352) [C8 (Z_to_bv 64 ?s)], HO : _ = _ |- evtF _ _ _ _ =>
      replace e with s in H by (clear - HO; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -376, SP + -336)] mm) as MUW;
      kx_munch_wins MUW [(SP + -376, 40)] end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E (EAlu ALU_AND ?Y (ELit 7)))] |- evtF _ _ _ _ =>
      replace (edenot E (EAlu ALU_AND Y (ELit 7))) with (Z_to_bv 64 (bv_unsigned (edenot E (EAlu ALU_AND Y (ELit 7)))))
        in H by (rewrite Z_to_bv_bv_unsigned; reflexivity);
      rewrite (u_and_mask E Y 7 3) in H by first [reflexivity | lia] end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ _ => eapply KK end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => w4_c4_bsum end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -376) _ => kx_cells_merge end).
  all: try w4_bsum_rng.
  all: try (lazymatch goal with |- 0 <= ?x mod 2 ^ 3 <= 64 =>
      change (2 ^ 3) with 8; pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB; clear - MB; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ <= 64 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ <= 64 =>
    lazymatch goal with |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?X (ELit 3)))] =>
      let Q := fresh "Q" in
      assert (Q : bv_unsigned (edenot E (EAluw ALU_SRL X (ELit 3))) = bv_unsigned (edenot E X) / 8);
      [ change (edenot E (EAluw ALU_SRL X (ELit 3))) with (sext 64 (alu32 ALU_SRL (low32 (edenot E X)) (low32 (edenot E (ELit 3)))));
        rewrite (u_srlw_small (edenot E X) (edenot E (ELit 3)) 3);
        [ reflexivity | vm_compute; reflexivity
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
          replace (2 ^ (3 mod 32)) with 8 by reflexivity; lia ]
      | rewrite Q; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia ]
    end end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Time Qed.

(* [comment removed for export] *)
End CANSEC1.
