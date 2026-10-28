(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi AF_huf_z4s3b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Lemma z4s31_R5A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x8fdfc) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x15 (Z_to_bv 64 qb) x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fcec) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x8fdfc] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + (p2 + qb)); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_R5B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x8fdfc) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x15 (Z_to_bv 64 qb) x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fcec) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x8fdfc] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_H5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z13 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x8fdf0) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x12 x9 (Z_to_bv 64 (SP + -144))
               (Z_to_bv 64 b) x12 z13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z13 z14 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) x12 z13 z14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x8fdfc) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x8fdfc) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fcd4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x8fcec] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x8fcec] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x8fcec] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s31_R5A with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
        all: exact (KA ltac:(lia) Q1).
       - eapply z4s31_R5B with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
        all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma z4s31_P1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 10 <= Qe -> Qe <= dcap ->
  1 <= tl <= 11 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 7 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 2048 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (nb : Z), 0 <= nb <= 11 -> 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) (Z_to_bv 64 (DST + q))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x8fec8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fdfc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x8fec8; 0x90a04; 0x90a08] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 10 (2^32); KZRange (Qe - q) 10 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 7; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 10 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R40 := fresh "R40" in kx_range (EVar 40) R40.
  all: let R42 := fresh "R42" in kx_range (EVar 42) R42.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_P2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 4 <= Qe -> Qe <= dcap ->
  1 <= tl <= 11 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 55 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 2048 -> 1 <= L1 <= 2 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z11 z12 z14 z15 : word) (nb : Z), 0 <= nb <= 11 -> 1 <= bv_unsigned z12 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x8ff84) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 L1) (Z_to_bv 64 bc) (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x8fec8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x8ff84] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 38) R.
  all: let R := fresh "R" in kx_range (EVar 40) R.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  replace (L1 + (DST + q)) with (DST + (q + L1)) in * by lia.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_P3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 4 <= Qe -> Qe <= dcap ->
  1 <= tl <= 11 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 55 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 2048 -> 1 <= L1 <= 2 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z11 z12 z14 z15 : word) (nb : Z), 0 <= nb <= 11 -> 1 <= bv_unsigned z12 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90040) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x8ff84) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90040] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 38) R.
  all: let R := fresh "R" in kx_range (EVar 40) R.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_P4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 4 <= Qe -> Qe <= dcap ->
  1 <= tl <= 11 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 55 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 2048 -> 1 <= L1 <= 2 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z11 z12 z14 z15 : word) (nb : Z), 0 <= nb <= 11 -> 1 <= bv_unsigned z12 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x900fc) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90040) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x900fc] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 38) R.
  all: let R := fresh "R" in kx_range (EVar 40) R.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_P5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 4 <= Qe -> Qe <= dcap ->
  1 <= tl <= 11 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 51 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 2048 -> 1 <= L1 <= 2 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (nb l5 : Z), 0 <= nb <= 11 -> 1 <= l5 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) (Z_to_bv 64 (DST + (q + (L1 + l5))))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x8fcd4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x900fc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x8fcd4] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 51; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 38) R.
  all: let R := fresh "R" in kx_range (EVar 40) R.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4b_tr : forall (mm mm' : amem) (SP DST dcap DT tl : Z) (cbs : list byte),
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 1 <= dcap -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 2 <= 2^tl <= 2048 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  bytes_at bsegs mm' (DT + 4) cbs /\ unpoisoned mm' (DT + 4) (DT + 4 + 4 * 2^tl) /\ unpoisoned mm' DST (DST + dcap).
Proof.
  intros mm mm' SP DST dcap DT tl cbs CB CBL CBU OBU MU AP1 AP2 AP3 AP4 HD HDE HDC HDT HSP HT2 HDX.
  unfold KXGoM.apart, AZ4_SB in *.
  split; [|split].
  - eapply bytes_at_transport; [exact CB | exact MU |]. cbn [disjoint_from]. lia.
  - eapply unpoisoned_munch; [exact CBU | exact MU |]. cbn [disjoint_from]. unfold shad, ASHOFF.
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
  - eapply unpoisoned_munch; [exact OBU | exact MU |]. cbn [disjoint_from]. unfold shad, ASHOFF.
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.

Lemma z4s31_B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  (forall i lo hi, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 11); (3, 1, 2)] = Some (lo, hi) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ lo <= bv_unsigned b <= hi) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 10 <= Qe -> Qe <= dcap ->
  1 <= tl <= 11 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 7 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 2048 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (q' bc' : Z), q < q' <= q + 10 -> 0 <= bc' <= 62 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc'); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 bc') (Z_to_bv 64 (DST + q'))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x8fcd4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fdfc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35 AP1 AP2 AP3 AP4 ZP HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  assert (ZT0 : ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB | lia | exact ZP]).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUa0.
  pose proof (wmono_refl bsegs mm) as WMa0.
  eapply z4s31_P1 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm1 z10 z13 z14 z15 nb1 NB1 LR1 SPL1 BD11 MI1 MU1 WM1 [ob1 [OB1 OL1]].
  destruct (z4b_tr mm mm1 SP DST dcap DT tl cbs CB CBL CBU OBU MU1 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB1 & CBU1 & OBU1).
  assert (ZT1 : ztab_fact bsegs mm1 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB1 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa0 MU1) as MUa1. pose proof (wmono_trans _ _ _ _ WMa0 WM1) as WMa1.
  rewrite <- (Z_to_bv_bv_unsigned z10).
  eapply z4s31_P2 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm2 y11 y12 y14 y15 nb2 NB2 LR2 SPL2 BD12 MI2 MU2 WM2 [ob2 [OB2 OL2]].
  destruct (z4b_tr mm1 mm2 SP DST dcap DT tl cbs CB1 CBL CBU1 OBU1 MU2 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB2 & CBU2 & OBU2).
  assert (ZT2 : ztab_fact bsegs mm2 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB2 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa1 MU2) as MUa2. pose proof (wmono_trans _ _ _ _ WMa1 WM2) as WMa2.
  rewrite <- (Z_to_bv_bv_unsigned y12).
  eapply z4s31_P3 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm3 y31 y32 y34 y35 nb3 NB3 LR3 SPL3 BD13 MI3 MU3 WM3 [ob3 [OB3 OL3]].
  destruct (z4b_tr mm2 mm3 SP DST dcap DT tl cbs CB2 CBL CBU2 OBU2 MU3 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB3 & CBU3 & OBU3).
  assert (ZT3 : ztab_fact bsegs mm3 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB3 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa2 MU3) as MUa3. pose proof (wmono_trans _ _ _ _ WMa2 WM3) as WMa3.
  rewrite <- (Z_to_bv_bv_unsigned y32).
  eapply z4s31_P4 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm4 y41 y42 y44 y45 nb4 NB4 LR4 SPL4 BD14 MI4 MU4 WM4 [ob4 [OB4 OL4]].
  destruct (z4b_tr mm3 mm4 SP DST dcap DT tl cbs CB3 CBL CBU3 OBU3 MU4 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB4 & CBU4 & OBU4).
  assert (ZT4 : ztab_fact bsegs mm4 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB4 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa3 MU4) as MUa4. pose proof (wmono_trans _ _ _ _ WMa3 WM4) as WMa4.
  rewrite <- (Z_to_bv_bv_unsigned y42).
  eapply z4s31_P5 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm5 y50 y53 y54 y55 nb5 l5 NB5 LR5 SPL5 BD15 MI5 MU5 WM5 [ob5 [OB5 OL5]].
  destruct (z4b_tr mm4 mm5 SP DST dcap DT tl cbs CB4 CBL CBU4 OBU4 MU5 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB5 & CBU5 & OBU5).
  assert (ZT5 : ztab_fact bsegs mm5 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB5 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa4 MU5) as MUa5. pose proof (wmono_trans _ _ _ _ WMa4 WM5) as WMa5.
  eapply K; try eassumption; try lia.
  exists ob5; split; [exact OB5 | exact OL5].
Qed.

Lemma z4s31_L6412 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (SP DST dcap DT Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= Qe <= dcap ->
  4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 1) x11 x8
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fdfc) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fdf0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT Qe tl mtl SPL MI RS HD HDE HDC HQE HDT HSP HTL HMT K.
  pose proof (munch_refl [(SP + -384, SP + -264)] mm) as MUW.
  kx_runFmd [0x8fdfc] 20%nat (@nil bool)
    [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange Qe 0 (2^32); KZRange DT 4096 (2^47);
     KZRange SP (2^46) (2^47); KZRange tl 1 12; KZRange mtl 1 12; KZWord (SP + -336) 8 (DST + dcap); KZWr (SP + -384) 120]
    (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_post.
  all: try (kx_munch MUW; kx_post_mem_free).
  all: z4post_ez.
  all: eapply K.
Qed.

Lemma z4s31_X6424 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (SP DST dcap DT q Qe tl mtl a : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  0 <= a <= 1 -> (a = 0 \/ Qe < q + 10) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 x21 x22 (Z_to_bv 64 (DST + Qe + -9)) x24 x25 x26 x27 x28 x29
           (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (DST + Qe + -9)) x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fdfc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28
    x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT q Qe tl mtl a SPL MI RS HD HDE HDC HQ HQE HDT HSP HTL HMT HA HX K.
  pose proof (munch_refl [(SP + -384, SP + -264)] mm) as MUW.
  destruct (Z_lt_ge_dec Qe (q + 10)) as [E1|E2].
  2: (destruct HX as [-> | HX]; [|lia]).
  2: kx_runFmd [0x90a08] 20%nat (@nil bool)
    [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 10 (2^32); KZRange (Qe - q) 10 (2^32);
     KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange tl 1 12; KZRange mtl 1 12;
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
    (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x90a08] 20%nat (@nil bool)
    [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 0 9;
     KZRange a 0 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange tl 1 12; KZRange mtl 1 12;
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
    (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_post.
  all: try (kx_munch MUW; kx_post_mem_free).
  all: z4post_ez.
  all: eapply K.
Qed.

Lemma z4s31_B5X : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  (forall i lo hi, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 11); (3, 1, 2)] = Some (lo, hi) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ lo <= bv_unsigned b <= hi) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q <= Qe -> Qe <= dcap ->
  1 <= tl <= 11 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 7 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 2048 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (q' bc' : Z), q < q' <= q + 10 -> 0 <= bc' <= 62 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc'); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 bc') (Z_to_bv 64 (DST + q'))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x8fcd4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x8fdfc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3.
  intros.
  destruct (Z_lt_ge_dec Qe (q + 10)) as [E1|E2].
  - eapply (z4s31_X6424 Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 _ _ _ _ x25 _ x27 x28
      x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT q Qe tl mtl 1).
    all: first [eassumption | lia | (right; lia)].
  - eapply (z4s31_B Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29 x30 x31
      w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3).
    all: first [eassumption | lia].
Qed.

Lemma z4b_tr4 : forall (mm mm' : amem) (SP DST dcap DT tl : Z) (cbs : list byte),
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 1 <= dcap -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 2 <= 2^tl <= 4096 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  bytes_at bsegs mm' (DT + 4) cbs /\ unpoisoned mm' (DT + 4) (DT + 4 + 4 * 2^tl) /\ unpoisoned mm' DST (DST + dcap).
Proof.
  intros mm mm' SP DST dcap DT tl cbs CB CBL CBU OBU MU AP1 AP2 AP3 AP4 HD HDE HDC HDT HSP HT2 HDX.
  unfold KXGoM.apart, AZ4_SB in *.
  split; [|split].
  - eapply bytes_at_transport; [exact CB | exact MU |]. cbn [disjoint_from]. lia.
  - eapply unpoisoned_munch; [exact CBU | exact MU |]. cbn [disjoint_from]. unfold shad, ASHOFF.
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
  - eapply unpoisoned_munch; [exact OBU | exact MU |]. cbn [disjoint_from]. unfold shad, ASHOFF.
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.

Lemma z4s31_Q1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 8 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 7 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 4096 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (nb : Z), 0 <= nb <= 12 -> 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) (Z_to_bv 64 (DST + q))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90684) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x905b8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90684; 0x90a04; 0x90a08] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 8 (2^32); KZRange (Qe - q) 8 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 7; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 8 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R40 := fresh "R40" in kx_range (EVar 40) R40.
  all: let R42 := fresh "R42" in kx_range (EVar 42) R42.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_Q2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x18 x19 x22 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 4 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 55 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 4096 -> 1 <= L1 <= 2 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z11 z12 z14 z15 : word) (nb : Z), 0 <= nb <= 12 -> 1 <= bv_unsigned z12 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90740) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 L1) (Z_to_bv 64 bc) (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90684) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x18 x19 x22 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90740] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 38) R.
  all: let R := fresh "R" in kx_range (EVar 40) R.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  replace (L1 + (DST + q)) with (DST + (q + L1)) in * by lia.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_Q3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x22 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 4 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 55 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 4096 -> 1 <= L1 <= 2 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z11 z12 z14 z15 : word) (nb : Z), 0 <= nb <= 12 -> 1 <= bv_unsigned z12 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x907fc) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90740) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x22 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x907fc] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 38) R.
  all: let R := fresh "R" in kx_range (EVar 40) R.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_Q4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x22 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 4 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 51 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 4096 -> 1 <= L1 <= 2 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (nb l5 : Z), 0 <= nb <= 12 -> 1 <= l5 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) (Z_to_bv 64 (DST + (q + (L1 + l5))))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90490) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x907fc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x18 x19 x22 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90490] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 51; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 38) R.
  all: let R := fresh "R" in kx_range (EVar 40) R.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_B4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  (forall i lo hi, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 12); (3, 1, 2)] = Some (lo, hi) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ lo <= bv_unsigned b <= hi) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 8 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 7 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 4096 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (q' bc' : Z), q < q' <= q + 8 -> 0 <= bc' <= 62 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc'); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 bc') (Z_to_bv 64 (DST + q'))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90490) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x905b8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35 AP1 AP2 AP3 AP4 ZP HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  assert (ZT0 : ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB | lia | exact ZP]).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUa0.
  pose proof (wmono_refl bsegs mm) as WMa0.
  eapply z4s31_Q1 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm1 z10 z13 z14 z15 nb1 NB1 LR1 SPL1 BD11 MI1 MU1 WM1 [ob1 [OB1 OL1]].
  destruct (z4b_tr4 mm mm1 SP DST dcap DT tl cbs CB CBL CBU OBU MU1 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB1 & CBU1 & OBU1).
  assert (ZT1 : ztab_fact bsegs mm1 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB1 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa0 MU1) as MUa1. pose proof (wmono_trans _ _ _ _ WMa0 WM1) as WMa1.
  rewrite <- (Z_to_bv_bv_unsigned z10).
  eapply z4s31_Q2 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm2 y11 y12 y14 y15 nb2 NB2 LR2 SPL2 BD12 MI2 MU2 WM2 [ob2 [OB2 OL2]].
  destruct (z4b_tr4 mm1 mm2 SP DST dcap DT tl cbs CB1 CBL CBU1 OBU1 MU2 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB2 & CBU2 & OBU2).
  assert (ZT2 : ztab_fact bsegs mm2 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB2 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa1 MU2) as MUa2. pose proof (wmono_trans _ _ _ _ WMa1 WM2) as WMa2.
  rewrite <- (Z_to_bv_bv_unsigned y12).
  eapply z4s31_Q3 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm3 y31 y32 y34 y35 nb3 NB3 LR3 SPL3 BD13 MI3 MU3 WM3 [ob3 [OB3 OL3]].
  destruct (z4b_tr4 mm2 mm3 SP DST dcap DT tl cbs CB2 CBL CBU2 OBU2 MU3 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB3 & CBU3 & OBU3).
  assert (ZT3 : ztab_fact bsegs mm3 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB3 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa2 MU3) as MUa3. pose proof (wmono_trans _ _ _ _ WMa2 WM3) as WMa3.
  rewrite <- (Z_to_bv_bv_unsigned y32).
  eapply z4s31_Q4 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm5 y50 y53 y54 y55 nb5 l5 NB5 LR5 SPL5 BD15 MI5 MU5 WM5 [ob5 [OB5 OL5]].
  destruct (z4b_tr4 mm3 mm5 SP DST dcap DT tl cbs CB3 CBL CBU3 OBU3 MU5 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB5 & CBU5 & OBU5).
  assert (ZT5 : ztab_fact bsegs mm5 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB5 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa3 MU5) as MUa5. pose proof (wmono_trans _ _ _ _ WMa3 WM5) as WMa5.
  eapply K; try eassumption; try lia.
  exists ob5; split; [exact OB5 | exact OL5].
Qed.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s31k.

Definition C31H5at (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z) : Prop :=
  forall (pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) mm (x1 x5 x7 x8 x10 x13 x14 x15 x16 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> tl < 12 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x8fcd4) fc None mm (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s31_M5 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell)
    (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
    (x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x17 x25 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  (forall q', q < q' -> C31H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q') ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
  0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> tl < 12 ->
  (x10 = Z_to_bv 64 0 \/ x10 = Z_to_bv 64 1 /\ b <= 7) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q))
        x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x8fdfc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q pt b c jp w0 w4 w5 w7 w8 w11 mm
    x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x17 x25 x27 x28 x29 x31
    C D6 O6 L1 OL HQe KJ IH FS Hq Hpt HptL Hb Htl Hx.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1. unfold C31H5at in IH.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  assert (KJ0 : forall x10' x11' x13' x14' x15' x16' : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10' x11' (Z_to_bv 64 (DST + q))
        x13' x14' x15' x16' (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs))).
  { intros. eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]]. }
  destruct Hx as [Hx0 | [Hx1 Hb7]]; subst x10.
  { eapply z4s31_X6424 with (a := 0).
    all: first [exact SPL | exact MI | exact FRS | lia | apply KJ0]. }
  destruct (Z_lt_le_dec Qe (q + 10)) as [HQ | HQ].
  { eapply z4s31_X6424 with (a := 1).
    all: first [exact SPL | exact MI | exact FRS | lia | apply KJ0]. }
  destruct BUF as (ob & OB & OBL).
  assert (HT2 : 2 <= 2^tl <= 2048).
  { split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]. }
  pose proof (z4ctx_dt_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C ltac:(lia)) as HDX.
  assert (FLD11 : forall i fl fh, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 11); (3, 1, 2)] = Some (fl, fh) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ fl <= bv_unsigned b <= fh)
    by (intros i fl fh Hi Hf; exact (FLD 11 i fl fh ltac:(lia) Hi Hf)).
  eapply (z4s31_B Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob
            (bv_unsigned sp) DST dcap SS DT q Qe O pt b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 z13 z14 z15 q' bc' Hq' Hbc SPL' BD1' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD1'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                 (BD4A c (Z_to_bv 64 bc') jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | exact B2S | | apply BD4A_size].
    - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD1'. }
  eapply (IH q'); [lia | exact FS' | lia | exact Hpt | exact HptL | lia | exact Htl].
Qed.

Section Z31RL5.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s31_H5L : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  (forall q', q < q' -> C31H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q') ->
  C31H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KJ IH.
  unfold C31H5at at 1.
  intros pt b c jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x13 x14 x15 x16 x25 x27 x28 x29 x31
    FS Hq Hpt HptL Hb Htl.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (z4_src_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm O Lk C D1 ltac:(lia) L1 OL BSS MU)
    as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6 & SB7 & SB8 & SB9 & SB10 & SB11 & SB12).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s31_H5 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16
            (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -9))
            (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w10 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
            (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  - intros Hp8 z13.
    eapply (z4_rl_call1 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd2 O Lk pt b c jp FR fc gp);
      [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
    intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof FS' as FS1.
    destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                     & FRM1 & MI1 & MU1 & WM1).
    unfold SPD in SPL1.
    eapply z4s31_L6412; [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia |].
    eapply (z4s31_M5 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q (pt - b / 8) (b mod 8));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  - intros Hp0 z10 z13 z14.
    eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]].
  - intros Hp17 Hbp mm' c' z5 z11 z13 z14 z15 z16 z17 SPL' BD1' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                   (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD1'. }
    eapply (z4s31_M5 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q (pt - b / 8) (b - 8 * (b / 8)));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  - intros Hp17 Hbp mm' c' z5 z11 z13 z14 z15 z16 z17 SPL' BD1' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                   (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. rewrite Z.add_0_r. exact BD1'. }
    eapply (z4s31_M5 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q 0 (b - 8 * pt));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | lia | left; reflexivity | Z.div_mod_to_equations; lia | lia | left; reflexivity].
Qed.

Lemma z4s31_L5 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  C31H5 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ.
  assert (H : forall q, C31H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q).
  { intros q.
    remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros q Hn.
    apply (z4s31_H5L Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KJ).
    intros q' Hq'.
    destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
    - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
    - unfold C31H5at. intros. lia. }
  unfold C31H5. intros q pt b c jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31.
  exact (H q pt b c jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x13 x14 x15 x16 x25 x27 x28 x29 x31).
Qed.

End Z31RL5.

End CANSEC1.

Lemma z4s31_R4A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x25 x20 x23 x24 x22 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x905b8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x15 (Z_to_bv 64 qb) x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x904a8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x25 x20 x23 x24 x22 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x905b8] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + (p2 + qb)); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_R4B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x25 x20 x23 x24 x22 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x905b8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x15 (Z_to_bv 64 qb) x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x904a8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x15 x17 x18 x19 x25 x20 x23 x24 x22 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x905b8] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_H4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x25 x20 x23 x24 x22 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z13 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x905ac) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x12 x9 (Z_to_bv 64 (SP + -144))
               (Z_to_bv 64 b) x12 z13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z13 z14 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) x12 z13 z14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x905b8) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z5 z11 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 x12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x905b8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90490) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x25 x20 x23 x24 x22 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x904a8] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x904a8] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x904a8] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s31_R4A with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
        all: exact (KA ltac:(lia) Q1).
       - eapply z4s31_R4B with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
        all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4s31_L8392 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x21 x20 x23 x24 x22 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (SP DST dcap DT Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= Qe <= dcap ->
  4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 1) x11 x8
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x905b8) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x905ac) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x21 x20 x23 x24 x22 x26 x27 x28
    x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT Qe tl mtl SPL MI RS HD HDE HDC HQE HDT HSP HTL HMT K.
  pose proof (munch_refl [(SP + -384, SP + -264)] mm) as MUW.
  kx_runFmd [0x905b8] 20%nat (@nil bool)
    [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange Qe 0 (2^32); KZRange DT 4096 (2^47);
     KZRange SP (2^46) (2^47); KZRange tl 1 12; KZRange mtl 1 12; KZWord (SP + -336) 8 (DST + dcap); KZWr (SP + -384) 120]
    (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_post.
  all: try (kx_munch MUW; kx_post_mem_free).
  all: z4post_ez.
  all: eapply K.
Qed.

Lemma z4s31_X8404 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x21 x20 x24 x22 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (SP DST dcap DT q Qe tl mtl a : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  0 <= a <= 1 -> (a = 0 \/ Qe < q + 8) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 x21 x22 (Z_to_bv 64 (DST + Qe + -7)) x24 x25 x26 x27 x28 x29
           (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (DST + Qe + -7)) x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x905b8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x25 x21 x20 x24 x22 x26 x27 x28
    x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT q Qe tl mtl a SPL MI RS HD HDE HDC HQ HQE HDT HSP HTL HMT HA HX K.
  pose proof (munch_refl [(SP + -384, SP + -264)] mm) as MUW.
  destruct (Z_lt_ge_dec Qe (q + 8)) as [E1|E2].
  2: (destruct HX as [-> | HX]; [|lia]).
  2: kx_runFmd [0x90a08] 20%nat (@nil bool)
    [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 8 (2^32); KZRange (Qe - q) 8 (2^32);
     KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange tl 1 12; KZRange mtl 1 12;
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
    (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x90a08] 20%nat (@nil bool)
    [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 0 7;
     KZRange a 0 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange tl 1 12; KZRange mtl 1 12;
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
    (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_post.
  all: try (kx_munch MUW; kx_post_mem_free).
  all: z4post_ez.
  all: eapply K.
Qed.

Lemma z4s31_B4X : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  (forall i lo hi, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 12); (3, 1, 2)] = Some (lo, hi) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ lo <= bv_unsigned b <= hi) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= bc <= 7 -> 0 <= c < 2^64 ->
  2 <= 2^tl <= 4096 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 ->
  (forall mm' (z10 z13 z14 z15 : word) (q' bc' : Z), q < q' <= q + 8 -> 0 <= bc' <= 62 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc'); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 bc') (Z_to_bv 64 (DST + q'))
              z13 z14 z15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90490) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (DST + q))
           x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x905b8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3.
  intros.
  destruct (Z_lt_ge_dec Qe (q + 8)) as [E1|E2].
  - eapply (z4s31_X8404 Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 _ _ _ _ x22 _ x27 x28
      x29 x30 x31 w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT q Qe tl mtl 1).
    all: first [eassumption | lia | (right; lia)].
  - eapply (z4s31_B4 Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29 x30 x31
      w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3).
    all: first [eassumption | lia].
Qed.

Definition C31H4at (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z) : Prop :=
  forall (pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) mm (x1 x5 x7 x8 x10 x13 x14 x15 x16 x22 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> 12 <= tl ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x90490) fc None mm (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s31_M4 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell)
    (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
    (x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x17 x22 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  (forall q', q < q' -> C31H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q') ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
  0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> 12 <= tl ->
  (x10 = Z_to_bv 64 0 \/ x10 = Z_to_bv 64 1 /\ b <= 7) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q))
        x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x905b8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q pt b c jp w0 w4 w5 w7 w8 w11 mm
    x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x17 x22 x27 x28 x29 x31
    C D6 O6 L1 OL HQe KJ IH FS Hq Hpt HptL Hb Htl Hx.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1. unfold C31H4at in IH.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  assert (KJ0 : forall x10' x11' x13' x14' x15' x16' : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10' x11' (Z_to_bv 64 (DST + q))
        x13' x14' x15' x16' (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs))).
  { intros. eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]]. }
  destruct Hx as [Hx0 | [Hx1 Hb7]]; subst x10.
  { eapply z4s31_X8404 with (a := 0).
    all: first [exact SPL | exact MI | exact FRS | lia | apply KJ0]. }
  destruct (Z_lt_le_dec Qe (q + 8)) as [HQ | HQ].
  { eapply z4s31_X8404 with (a := 1).
    all: first [exact SPL | exact MI | exact FRS | lia | apply KJ0]. }
  destruct BUF as (ob & OB & OBL).
  assert (HT2 : 2 <= 2^tl <= 4096).
  { split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]. }
  pose proof (z4ctx_dt_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C ltac:(lia)) as HDX.
  assert (FLD12 : forall i fl fh, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 12); (3, 1, 2)] = Some (fl, fh) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ fl <= bv_unsigned b <= fh)
    by (intros i fl fh Hi Hf; exact (FLD 12 i fl fh ltac:(lia) Hi Hf)).
  eapply (z4s31_B4 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x22 x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w10 w11 jp cbs ob
            (bv_unsigned sp) DST dcap SS DT q Qe O pt b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 z13 z14 z15 q' bc' Hq' Hbc SPL' BD1' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD1'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                 (BD4A c (Z_to_bv 64 bc') jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | exact B2S | | apply BD4A_size].
    - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD1'. }
  eapply (IH q'); [lia | exact FS' | lia | exact Hpt | exact HptL | lia | exact Htl].
Qed.

Section Z31RL4.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s31_H4L : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  (forall q', q < q' -> C31H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q') ->
  C31H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KJ IH.
  unfold C31H4at at 1.
  intros pt b c jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x13 x14 x15 x16 x22 x27 x28 x29 x31
    FS Hq Hpt HptL Hb Htl.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (z4_src_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm O Lk C D1 ltac:(lia) L1 OL BSS MU)
    as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6 & SB7 & SB8 & SB9 & SB10 & SB11 & SB12).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s31_H4 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16
            (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -7))
            (Z_to_bv 64 (64 - tl)) x22 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w10 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
            (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  - intros Hp8 z13.
    eapply (z4_rl_call1 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd2 O Lk pt b c jp FR fc gp);
      [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
    intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof FS' as FS1.
    destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                     & FRM1 & MI1 & MU1 & WM1).
    unfold SPD in SPL1.
    eapply z4s31_L8392; [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia |].
    eapply (z4s31_M4 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q (pt - b / 8) (b mod 8));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  - intros Hp0 z10 z13 z14.
    eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]].
  - intros Hp17 Hbp mm' c' z5 z11 z13 z14 z15 z16 z17 SPL' BD1' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                   (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD1'. }
    eapply (z4s31_M4 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q (pt - b / 8) (b - 8 * (b / 8)));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  - intros Hp17 Hbp mm' c' z5 z11 z13 z14 z15 z16 z17 SPL' BD1' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                   (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. rewrite Z.add_0_r. exact BD1'. }
    eapply (z4s31_M4 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q 0 (b - 8 * pt));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | lia | left; reflexivity | Z.div_mod_to_equations; lia | lia | left; reflexivity].
Qed.

Lemma z4s31_L4 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  forall q, C31H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ.
  assert (H : forall q, C31H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q).
  { intros q.
    remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros q Hn.
    apply (z4s31_H4L Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KJ).
    intros q' Hq'.
    destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
    - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
    - unfold C31H4at. intros. lia. }
  exact H.
Qed.

End Z31RL4.

End CANSEC1.

Lemma z4s31_N4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x8 x9 x10 x11 x13 x14 x15 x16 x19 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O -> 1 <= L < 2^26 -> 0 <= pt <= L -> 0 <= b < 2^31 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> tl <= mtl -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> O <= 2^26 ->
  (b <= 64 -> forall mm',
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (- tl + -256 * mtl)) (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
               x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x90490) fc None mm' (seg_rom bsegs))) ->
  (64 < b -> forall mm',
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00);
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 0x20e00) (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
               x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x90a08) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x90460) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x8 x9 x10 x11 x13 x14 x15 x16 x19 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp SP DST dcap SS DT q Qe O L pt b cz tl mtl
    SPL BD MI RS HD HDE HDC HQ HQE HS HSE HO HL HPT HB HCZ HTL HMT HTM HDT HSP HO2 K1 K2.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_le_gt_dec b 64) as [C3|C3].
  2: kx_runFmd [0x90490; 0x90a08; 0x8fbec] 40%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x90490; 0x90a08; 0x8fbec] 40%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: rewrite ?z4_eext in *.
  all: repeat (lazymatch goal with |- context [edenot ?E ?e] =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite ?(ez_ok zv E (kE_atoms zv xs) e); let na := eval vm_compute in (length zv) in
         cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb] end end).
  all: rewrite ?z4_dl_b0 in * by lia.
  all: rewrite ?Z_to_bv_bv_unsigned in *.
  all: repeat match goal with H : rw_cells _ _ _ [C8 (ext_val false 0 1 (edenot ?E ?e))] |- _ =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite (ez_ok zv E (kE_atoms zv xs) e) in H; let na := eval vm_compute in (length zv) in
         cbv [ez] in H; change (length zv) with na in H; cbv [nth Nat.ltb Nat.leb] in H; rewrite z4_dl_b0 in H by lia end end.
  2: (eapply K2; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  1: z4_m64.
  1: (eapply K1; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Section CANSEC1. Context {rc : runConstT}.

Section Z31RL4E.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.
Lemma z4s31_E4 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  C31H4 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ.
  pose proof (z4s31_L4 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ) as KH.
  unfold C31H4.
  intros q pt b c jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31
    FS Hq HqQ Hpt HptL Hb Htl.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (z4_src_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm O Lk C D1 ltac:(lia) L1 OL BSS MU)
    as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6 & SB7 & SB8 & SB9 & SB10 & SB11 & SB12).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_N4 Q RNG mm FR fc gp tp x1 x5 x7 x8 x9 x10 x11 x13 x14 x15 x16 x19 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 jp (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  - intros Hb64 mm' SPL' BD1' MI' MU' WM'.
    rewrite Z_to_bv_bv_unsigned in BD1'.
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 bd2 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD1'. }
    eapply (KH q); [exact FS' | lia | exact Hpt | exact HptL | lia | exact Htl].
  - intros Hb64 mm' SPL' BD1' MI' MU' WM'.
    rewrite Z_to_bv_bv_unsigned in BD1'.
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    match type of BD1' with rw_cells _ _ _ [_; _; _; C8 ?pv; _; _] =>
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 bd2 (BD4A c (Z_to_bv 64 b) jp pv (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))) end.
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD1'. }
    eapply KJ; [exact FS' | lia | right; lia].
Qed.

End Z31RL4E.

End CANSEC1.

Lemma z4s31_RH0 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= pt <= L -> 0 <= b < 2^31 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (b <= 64 ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 (Z_to_bv 64 65) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90340) fc None mm (seg_rom bsegs))) ->
  (64 < b -> forall mm',
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00);
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 (Z_to_bv 64 0x20e00) (Z_to_bv 64 b) x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90328) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp SP DST dcap SS DT q Qe O L pt b cz tl mtl
    SPL BD MI RS HD HDE HDC HQ HQE HS HSE HO HL HPT HB HCZ HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_le_gt_dec b 64) as [C3|C3].
  2: kx_runFmd [0x90340; 0x90a08] 30%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x90340; 0x90a08] 30%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: rewrite ?z4_eext in *.
  all: repeat (lazymatch goal with |- context [edenot ?E ?e] =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite ?(ez_ok zv E (kE_atoms zv xs) e); let na := eval vm_compute in (length zv) in
         cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb] end end).
  all: rewrite ?z4_dl_b0 in * by lia.
  all: rewrite ?Z_to_bv_bv_unsigned in *.
  2: (eapply K2; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  1: (apply K1; lia).
Qed.

Lemma z4s31_LR : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word)
    (SP DST dcap DT Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x8 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x909f0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT Qe tl mtl SPL MI RS HD HDE HDC HQE HTL HMT HDT HSP K.
  kx_runFmd [0x90a08] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: z4post_ez.
  exact K.
Qed.

Lemma z4s31_RA : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x9 x10 x12 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 z10 z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 x10 (Z_to_bv 64 b)
           x12 (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 qb) (Z_to_bv 64 (SS + O)) x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x9035c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x9 x10 x12 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x90a08] 80%nat [true; true; true; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + (p2 + qb)); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_RB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x9 x10 x12 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 z10 z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 x10 (Z_to_bv 64 b)
           x12 (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 qb) (Z_to_bv 64 (SS + O)) x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x9035c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x9 x10 x12 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x90a08] 80%nat [true; true; true; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s31_RH : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x909f0) (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 (Z_to_bv 64 (SP + -144))
               (Z_to_bv 64 b) x12 z12 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z14 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 z10 (Z_to_bv 64 b) x12 z12 x14 z14 x16 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 z10 z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -144) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 z10 z11 x12 z12 z13 z14 z15 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x90a08) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x12 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90340) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w10 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD1 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x9035c] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x9035c] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x90a08; 0x9035c] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s31_RA with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s31_RB with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Section CANSEC1. Context {rc : runConstT}.

Section Z31RL.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.
Lemma z4s31_RL : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  C31R RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ.
  unfold C31R.
  intros q pt b c jp w0 w4 w5 w7 w8 w11 mm x6 x17 x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31
    FS Hq HqQ Hpt HptL Hb.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (z4_src_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm O Lk C D1 ltac:(lia) L1 OL BSS MU)
    as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6 & SB7 & SB8 & SB9 & SB10 & SB11 & SB12).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s31_RH0 Q RNG mm FR fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
            x18 x19 x20 x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w10 w11 jp (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hb64.
    eapply (z4s31_RH Q RNG mm FR fc gp tp x1 x5 x7 x9 (Z_to_bv 64 65) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
              x18 x19 x20 x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31
              w0 w1 w4 w5 w7 w8 w10 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
              (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
    all: try (lazymatch goal with
         | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
         end).
    all: try assumption.
    all: try lia.
    +
      intros Hp8 z12.
      eapply (z4_rl_call1 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd2 O Lk pt b c jp FR fc gp);
        [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
      intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
      rewrite ret_pc_even by first [lia | reflexivity].
      pose proof FS' as FS1.
      destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                       & FRM1 & MI1 & MU1 & WM1).
      unfold SPD in SPL1.
      eapply z4s31_LR; [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia |].
      eapply KJ; [exact FS' | lia | left; split;
        [exists (pt - b / 8); split; [reflexivity | split; [Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia]]
        | Z.div_mod_to_equations; lia]].
    +
      intros Hp0 z10 z12 z14.
      eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]].
    +
      intros Hp17 Hbp mm' c' z10 z11 z12 z13 z14 z15 SPL' BD1' MI' MU' WM'.
      destruct BUF as (ob & OB & OBL).
      assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                           (DST, DST + dcap)] mm mm').
      { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
      assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                     (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                          (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                     bd3 bd2 (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                           (Z_to_bv 64 (SS + O + 8)))).
      { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                  cells cbs pdt SBL SBH rstk mm mm' (-144));
          [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
          | | exact B3S | | exact B2S | | apply BD4A_size].
        - exists ob. split; [| exact OBL].
          eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
        - unfold SPD. exact SPL'.
        - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
        - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
        - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
        - unfold BD4A. exact BD1'. }
      eapply KJ; [exact FS' | lia | left; split;
        [exists (pt - b / 8); split; [reflexivity | split; [Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia]]
        | Z.div_mod_to_equations; lia]].
    +
      intros Hp17 Hbp mm' c' z10 z11 z12 z13 z14 z15 SPL' BD1' MI' MU' WM'.
      destruct BUF as (ob & OB & OBL).
      assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                           (DST, DST + dcap)] mm mm').
      { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
      assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                     (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                          (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                     bd3 bd2 (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                           (Z_to_bv 64 (SS + O + 8)))).
      { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                  cells cbs pdt SBL SBH rstk mm mm' (-144));
          [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
          | | exact B3S | | exact B2S | | apply BD4A_size].
        - exists ob. split; [| exact OBL].
          eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
        - unfold SPD. exact SPL'.
        - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
        - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
        - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
        - unfold BD4A. rewrite Z.add_0_r. exact BD1'. }
      eapply KJ; [exact FS' | lia | left; split;
        [exists 0; split; [reflexivity | split; [lia | left; reflexivity]]
        | Z.div_mod_to_equations; lia]].
  -
    intros Hb64 mm' SPL' BD1' MI' MU' WM'.
    rewrite Z_to_bv_bv_unsigned in BD1'.
    match type of BD1' with
    | context [C8 (Z_to_bv 64 ?v) :: C8 (Z_to_bv 64 (SS + O)) :: _] => set (pl := v) in *
    end.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 bd2 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 pl) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD1'. }
    eapply KJ; [exact FS' | lia | right; lia].
Qed.

End Z31RL.

End CANSEC1.
