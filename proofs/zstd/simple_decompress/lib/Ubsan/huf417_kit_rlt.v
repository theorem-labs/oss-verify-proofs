(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf411_kit_rs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf417_kit_rlk huf417_kit_rld huf417_kit_rc.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41RLT.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Notation K5004 := (huf417_kit_rlk.K5004 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation KH := (huf417_kit_rld.KH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).

  Lemma x41_rlt : forall rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0,
    KH rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K5004 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0.
  Proof using CTX DJ3 SPVA DTA.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KHh.
    unfold huf417_kit_rld.KH in KHh. unfold huf417_kit_rlk.K5004.
    intros mm K1 K2 K3 K4 c1 o1 Q1 c2 o2 Q2 c3 o3 Q3 c4 o4 Q4 x7 x8 x12 x20 x27 KB FA B1 B2 B3 B4 RL1 RL2 RL3 RL4.
    destruct KB as (PV & MI & OUT & DTB & NB & SB1 & SB2 & SB3 & SB4 & HJ & HE & HROOM & HDL & HTL & HRSV).
    destruct RL1 as (RR1 & H1 & SI1 & C1). destruct RL2 as (RR2 & H2 & SI2 & C2).
    destruct RL3 as (RR3 & H3 & SI3 & C3). destruct RL4 as (RR4 & H4 & SI4 & C4).
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        let p7 := eval vm_compute in (p + 2784) in
        let p3 := eval vm_compute in (p - 1832) in
        kx_autoLx [p7; p3] 20%nat
          [KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange dcap 0 (2^32); KZRange (dcap - 3 * e1 - j) 4 (2^32);
           KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
          [(SPV - 512, 136)]
    end.
    all: kx_mem.
    all: lazymatch goal with
         | E : Z.lor (Z.lor _ _) (Z.lor _ _) = 0 |- _ =>
             apply Z.lor_eq_0_iff in E as [E21 E34];
             apply Z.lor_eq_0_iff in E21 as [A2 A1]; apply Z.lor_eq_0_iff in E34 as [A3 A4];
             replace (DST + j + 4) with (DST + (j + 4)) by lia;
             eapply (KHh mm K1 K2 K3 K4 c1 o1 c2 o2 c3 o3 c4 o4);
             first [ exact FA | exact B1 | exact B2 | exact B3 | exact B4
                   | exact (H1 A1) | exact (H2 A2) | exact (H3 A3) | exact (H4 A4)
                   | refine (conj PV (conj MI (conj OUT (conj DTB (conj NB (conj SB1 (conj SB2 (conj SB3 (conj SB4 _))))))))); lia ]
         | |- _ =>
             eapply (huf417_kit_rc.x41_r_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
                       CTX DJ3 SPVA DTA mm rest j e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
                       K1 K2 K3 K4 pad1 pad2 pad3 pad4);
             first [ eassumption | lia ]
         end.
  Qed.

End DX41RLT.
