(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s31k AF_huf_z4s31b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s32k.

Lemma z4s32_P1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
  (forall mm' (z10 z12 z13 z14 z15 : word) (nb : Z), 0 <= nb <= 11 -> 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) z12
              z13 z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x9110c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12
           x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 x30 x31)
       F (Z_to_bv 64 0x91044) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x9110c; 0x91c1c; 0x91c20] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 10 (2^32); KZRange (Qe - q) 10 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 7; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 10 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
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

Lemma z4s32_P2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x911c8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 L1) (Z_to_bv 64 bc) x12
           x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x9110c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x911c8] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 39) R.
  all: let R := fresh "R" in kx_range (EVar 41) R.
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

Lemma z4s32_P3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91284) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x911c8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x91284] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 39) R.
  all: let R := fresh "R" in kx_range (EVar 41) R.
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

Lemma z4s32_P4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91340) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91284) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x91340] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 39) R.
  all: let R := fresh "R" in kx_range (EVar 41) R.
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

Lemma z4s32_P5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
  (forall mm' (z10 z12 z13 z14 z15 : word) (nb l5 : Z), 0 <= nb <= 11 -> 1 <= l5 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) z12
              z13 z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + (q + (L1 + l5)))) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90f24) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91340) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90f24] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 53 63; KZRange (2^tl) 2 2048; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 11; KZRange mtl 1 12; KZRange bc 0 51; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 39) R.
  all: let R := fresh "R" in kx_range (EVar 41) R.
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

Lemma z4s32_tr : forall (mm mm' : amem) (SP DST dcap DT tl : Z) (cbs : list byte),
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
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

Lemma z4s32_B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
  (forall mm' (z10 z12 z13 z14 z15 : word) (q' bc' : Z), q < q' <= q + 10 -> 0 <= bc' <= 62 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc'); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 bc') z12
              z13 z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + q')) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90f24) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12
           x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 x30 x31)
       F (Z_to_bv 64 0x91044) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31 w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35 AP1 AP2 AP3 AP4 ZP HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  assert (ZT0 : ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB | lia | exact ZP]).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUa0.
  pose proof (wmono_refl bsegs mm) as WMa0.
  eapply z4s32_P1 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm1 z10 z12 z13 z14 z15 nb1 NB1 LR1 SPL1 BD11 MI1 MU1 WM1 [ob1 [OB1 OL1]].
  destruct (z4s32_tr mm mm1 SP DST dcap DT tl cbs CB CBL CBU OBU MU1 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB1 & CBU1 & OBU1).
  assert (ZT1 : ztab_fact bsegs mm1 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB1 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa0 MU1) as MUa1. pose proof (wmono_trans _ _ _ _ WMa0 WM1) as WMa1.
  rewrite <- (Z_to_bv_bv_unsigned z10).
  eapply z4s32_P2 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm2 y11 y12 y14 y15 nb2 NB2 LR2 SPL2 BD12 MI2 MU2 WM2 [ob2 [OB2 OL2]].
  destruct (z4s32_tr mm1 mm2 SP DST dcap DT tl cbs CB1 CBL CBU1 OBU1 MU2 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB2 & CBU2 & OBU2).
  assert (ZT2 : ztab_fact bsegs mm2 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB2 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa1 MU2) as MUa2. pose proof (wmono_trans _ _ _ _ WMa1 WM2) as WMa2.
  rewrite <- (Z_to_bv_bv_unsigned y12).
  eapply z4s32_P3 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm3 y31 y32 y34 y35 nb3 NB3 LR3 SPL3 BD13 MI3 MU3 WM3 [ob3 [OB3 OL3]].
  destruct (z4s32_tr mm2 mm3 SP DST dcap DT tl cbs CB2 CBL CBU2 OBU2 MU3 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB3 & CBU3 & OBU3).
  assert (ZT3 : ztab_fact bsegs mm3 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB3 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa2 MU3) as MUa3. pose proof (wmono_trans _ _ _ _ WMa2 WM3) as WMa3.
  rewrite <- (Z_to_bv_bv_unsigned y32).
  eapply z4s32_P4 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm4 y41 y42 y44 y45 nb4 NB4 LR4 SPL4 BD14 MI4 MU4 WM4 [ob4 [OB4 OL4]].
  destruct (z4s32_tr mm3 mm4 SP DST dcap DT tl cbs CB3 CBL CBU3 OBU3 MU4 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB4 & CBU4 & OBU4).
  assert (ZT4 : ztab_fact bsegs mm4 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB4 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa3 MU4) as MUa4. pose proof (wmono_trans _ _ _ _ WMa3 WM4) as WMa4.
  rewrite <- (Z_to_bv_bv_unsigned y42).
  eapply z4s32_P5 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm5 y50 y52 y53 y54 y55 nb5 l5 NB5 LR5 SPL5 BD15 MI5 MU5 WM5 [ob5 [OB5 OL5]].
  destruct (z4s32_tr mm4 mm5 SP DST dcap DT tl cbs CB4 CBL CBU4 OBU4 MU5 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB5 & CBU5 & OBU5).
  assert (ZT5 : ztab_fact bsegs mm5 (DT + 4) (4 * 2^tl) 4 [(2, 0, 11); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB5 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa4 MU5) as MUa5. pose proof (wmono_trans _ _ _ _ WMa4 WM5) as WMa5.
  eapply K; try eassumption; try lia.
  exists ob5; split; [exact OB5 | exact OL5].
Qed.

Lemma z4s32_tr4 : forall (mm mm' : amem) (SP DST dcap DT tl : Z) (cbs : list byte),
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
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

Lemma z4s32_Q1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
  (forall mm' (z10 z12 z13 z14 z15 : word) (nb : Z), 0 <= nb <= 12 -> 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) z12
              z13 z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x918ac) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12
           x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 x30 x31)
       F (Z_to_bv 64 0x917e4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x918ac; 0x91c1c; 0x91c20] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 8 (2^32); KZRange (Qe - q) 8 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 7; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 8 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
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

Lemma z4s32_Q2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91968) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 L1) (Z_to_bv 64 bc) x12
           x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x918ac) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x91968] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 39) R.
  all: let R := fresh "R" in kx_range (EVar 41) R.
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

Lemma z4s32_Q3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + (q + L1))) z11 z12
              (Z_to_bv 64 (bc + nb)) z14 z15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91a24) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91968) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x91a24] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 55; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 39) R.
  all: let R := fresh "R" in kx_range (EVar 41) R.
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

Lemma z4s32_Q4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
  (forall mm' (z10 z12 z13 z14 z15 : word) (nb l5 : Z), 0 <= nb <= 12 -> 1 <= l5 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (bc + nb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 (bc + nb)) z12
              z13 z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + (q + (L1 + l5)))) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x916c4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + q)) x11 (Z_to_bv 64 L1)
           (Z_to_bv 64 bc) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91a24) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x25 x22 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c L1 tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HL1 HDX K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x916c4] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 4 (2^32); KZRange (Qe - q) 4 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange bc 0 51; KZRange L1 1 2; KZRange c 0 (2^64 - 1); KZRange (dcap - q) 4 (2^32);
      KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 bc;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: let R := fresh "R" in kx_range (EVar 39) R.
  all: let R := fresh "R" in kx_range (EVar 41) R.
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

Lemma z4s32_B4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
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
  (forall mm' (z10 z12 z13 z14 z15 : word) (q' bc' : Z), q < q' <= q + 8 -> 0 <= bc' <= 62 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc'); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
             C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 bc') z12
              z13 z14 z15 x16 x17 x18 (Z_to_bv 64 (DST + q')) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x916c4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12
           x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x25 x28 x29 x30 x31)
       F (Z_to_bv 64 0x917e4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29 x30 x31 w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob SP DST dcap SS DT q Qe O pt bc c tl mtl A2 L2 A3 L3 SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35 AP1 AP2 AP3 AP4 ZP HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HBC HC HT2 HDX K.
  assert (ZT0 : ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB | lia | exact ZP]).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUa0.
  pose proof (wmono_refl bsegs mm) as WMa0.
  eapply z4s32_Q1 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm1 z10 z12 z13 z14 z15 nb1 NB1 LR1 SPL1 BD11 MI1 MU1 WM1 [ob1 [OB1 OL1]].
  destruct (z4s32_tr4 mm mm1 SP DST dcap DT tl cbs CB CBL CBU OBU MU1 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB1 & CBU1 & OBU1).
  assert (ZT1 : ztab_fact bsegs mm1 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB1 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa0 MU1) as MUa1. pose proof (wmono_trans _ _ _ _ WMa0 WM1) as WMa1.
  rewrite <- (Z_to_bv_bv_unsigned z10).
  eapply z4s32_Q2 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm2 y11 y12 y14 y15 nb2 NB2 LR2 SPL2 BD12 MI2 MU2 WM2 [ob2 [OB2 OL2]].
  destruct (z4s32_tr4 mm1 mm2 SP DST dcap DT tl cbs CB1 CBL CBU1 OBU1 MU2 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB2 & CBU2 & OBU2).
  assert (ZT2 : ztab_fact bsegs mm2 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB2 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa1 MU2) as MUa2. pose proof (wmono_trans _ _ _ _ WMa1 WM2) as WMa2.
  rewrite <- (Z_to_bv_bv_unsigned y12).
  eapply z4s32_Q3 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm3 y31 y32 y34 y35 nb3 NB3 LR3 SPL3 BD13 MI3 MU3 WM3 [ob3 [OB3 OL3]].
  destruct (z4s32_tr4 mm2 mm3 SP DST dcap DT tl cbs CB2 CBL CBU2 OBU2 MU3 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB3 & CBU3 & OBU3).
  assert (ZT3 : ztab_fact bsegs mm3 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB3 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa2 MU3) as MUa3. pose proof (wmono_trans _ _ _ _ WMa2 WM3) as WMa3.
  rewrite <- (Z_to_bv_bv_unsigned y32).
  eapply z4s32_Q4 with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
  intros mm5 y50 y52 y53 y54 y55 nb5 l5 NB5 LR5 SPL5 BD15 MI5 MU5 WM5 [ob5 [OB5 OL5]].
  destruct (z4s32_tr4 mm3 mm5 SP DST dcap DT tl cbs CB3 CBL CBU3 OBU3 MU5 AP1 AP2 AP3 AP4 HD HDE ltac:(lia) HDT HSP HT2 HDX)
    as (CB5 & CBU5 & OBU5).
  assert (ZT5 : ztab_fact bsegs mm5 (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)])
    by (eapply ztab_fact_bytes_at; [exact CB5 | lia | exact ZP]).
  pose proof (munch_trans _ _ _ _ MUa3 MU5) as MUa5. pose proof (wmono_trans _ _ _ _ WMa3 WM5) as WMa5.
  eapply K; try eassumption; try lia.
  exists ob5; split; [exact OB5 | exact OL5].
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
