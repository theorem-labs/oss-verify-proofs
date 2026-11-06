(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41h RZ_huf_dx41i.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41J.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 416, SPV - 216)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  Lemma x41_m0 : forall mm rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
      (k1 k2 k3 k4 : word) pad
      (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w11 w13 w15 w16 w17 w18 : word),
    X41P mm rest -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 w1 w2 w3 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 dl) k3 (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 S3) (Z_to_bv 64 c1) (Z_to_bv 64 (DST + 2 * e1)) w11 (Z_to_bv 64 dcap) w13 (Z_to_bv 64 (S1 - 6)) w15 w16 w17 w18 (Z_to_bv 64 c2) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    0 <= e1 -> 3 * e1 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    evt psegs POST (ST 0x22d88 mm x1 x5 x6 x7 (Z_to_bv 64 S1) (Z_to_bv 64 S2) x10 x11 x12 (Z_to_bv 64 S3) x14 x15 x16 x17 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 c3) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 e1) k2 k1 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv k1 k2 k3 k4 pad
      x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31
      w0 w1 w2 w3 w11 w13 w15 w16 w17 w18 PV MI OUT DTB NBOK FA BD SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HE1 HE3 HDL HTL HRSV.
    assert (MU : munch WDF mm mm) by apply munch_refl.
    assert (WM : wmono psegs mm mm) by apply wmono_refl.
    pose proof (proj1 HI4) as C4.
    kx_autoLx [0x22e10; 0x232bc] 80%nat
      [KZRange e1 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47);
       KZRange c4 0 64; KZRange dl 0 65535; KZWr (SPV - 416) 160]
      [(SPV - 416, 160); (SPV - 256, 40)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142864) _ _ _ _) =>
             subst dl; rewrite (neg_dl_sh tl rsv HTL);
             let HM := fresh "HM" in
             pose proof (x41_m1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 (Z.to_nat (dcap - 3 * e1)) m rest 0) as HM;
             replace (DST + 0) with DST in HM by lia;
             eapply (HM e1 (2 * e1) (3 * e1) (2 * e1) (3 * e1) (64 - tl) S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4
                        (tl + 256 * rsv) tl rsv)
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144060) _ _ _ _) =>
             let HC := fresh "HC" in
             pose proof (x41_c0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 m rest 0) as HC;
             replace (DST + 0) with DST in HC by lia;
             eapply (HC e1 (2 * e1) (3 * e1) e1 (2 * e1) (3 * e1) S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv k4 pad)
         end.
    all: first [ exact KXMI | exact NBOK | exact OUT | exact DTB | exact FA | exact BD | exact HI1 | exact HI2 | exact HI3 | exact HI4 | lia
               | eapply x41p_transport; first [exact CTX | exact DJ3 | exact PV | exact MU | exact WM]
               | eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MU]
               | unfold RZ_huf_dx41.SINV; unfold RZ_huf_dx41g.HINV in HI1, HI2, HI3, HI4; lia ].
  Qed.

End DX41J.
