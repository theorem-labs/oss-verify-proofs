(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41h RZ_huf_dx41i huf411_kit_rs huf41_kit_x41ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41J.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 224, SPV - 184)].
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  Lemma x41_m0 : forall mm rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
      (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w10 w12 w15 w16 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 (Z_to_bv 64 (DST + e1)) w10 (Z_to_bv 64 (DST + 2 * e1)) w12 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    0 <= e1 -> 3 * e1 <= dcap -> e1 = (dcap + 3) / 4 -> 6 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    evt usegs POST (ST 0x22d24 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) x20 x21 x22 x23
                     (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using CTX DJ3 SPVA DTA.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv k1 k2 k3 k4 pad1 pad2 pad3 pad4
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w10 w12 w15 w16 PV MI OUT DTB NBOK FA HB1 HB2 HB3 HB4 SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4
      HE1 HE3 HE4 HDC HDL HTL HRSV.
    assert (MU : munch WDF mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    pose proof (proj1 HI1) as C1. pose proof (proj1 HI2) as C2. pose proof (proj1 HI3) as C3. pose proof (proj1 HI4) as C4.
    pose proof (rsk_al_e _ _ SPVA) as SPA. pose proof (rsk_al_e _ _ DTA) as DT4.
    kx_autoLx [0x22df8; 0x24024] 80%nat
      [KZRange e1 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47);
       KZRange c1 0 64; KZRange c2 0 64; KZRange c3 0 64; KZRange c4 0 64; KZRange dl 0 (2^16); KZWr (SPV - 512) 136]
      [(SPV - 512, 136); (SPV - 376, 40); (SPV - 224, 40); (SPV - 184, 40); (SPV - 144, 40)].
    all: kx_mem.
    all: let v20 := eval vm_compute in (2^64 - 20) in let v1 := eval vm_compute in (2^64 - 1) in
         try replace (Z_to_bv 64 v20 : word) with (Z_to_bv 64 (-20) : word) by (apply Z_to_bv_eqm; reflexivity);
         try replace (Z_to_bv 64 v1 : word) with (Z_to_bv 64 (-1) : word) by (apply Z_to_bv_eqm; reflexivity).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22df8) _ _ ?m1 _) =>
             subst dl; rewrite ?(neg_dl_sh tl rsv HTL);
             let HM := fresh "HM" in
             pose proof x41_m1 as HM;
             specialize (HM ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb);
             try specialize (HM CTX); try specialize (HM DJ3); try specialize (HM SPVA); try specialize (HM DTA);
             specialize (HM (Z.to_nat (dcap - 3 * e1)) m1 rest 0 e1 (64 - tl) S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3
                            S4 n4 b4 o4 c4 (tl + 256 * rsv) tl rsv k1 k2 k3 k4 pad1 pad2 pad3 pad4);
             replace (DST + 0) with DST in HM by lia;
             eapply HM
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24024) _ _ ?m1 _) =>
             let HC := fresh "HC" in
             pose proof x41_c0 as HC;
             specialize (HC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb);
             try specialize (HC CTX); try specialize (HC DJ3); try specialize (HC SPVA); try specialize (HC DTA);
             specialize (HC m1 rest 0 e1 (2 * e1) (3 * e1) e1 (2 * e1) (3 * e1) S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3
                            S4 n4 b4 o4 c4 dl tl rsv k1 k2 k3 k4 pad1 pad2 pad3 pad4);
             replace (DST + 0) with DST in HC by lia;
             eapply HC
         end.
    all: first [ exact KXMI | exact NBOK | exact OUT | exact DTB | exact FA | exact HB1 | exact HB2 | exact HB3 | exact HB4
               | exact HI1 | exact HI2 | exact HI3 | exact HI4 | exact CTX | exact DJ3 | exact SPVA | exact DTA | lia
               | eapply x41p_transport; first [exact CTX | exact DJ3 | exact PV | exact MU | exact WM]
               | eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MU]
               | unfold RZ_huf_dx41.SINV; unfold RZ_huf_dx41g.HINV in HI1, HI2, HI3, HI4; lia ].
  Qed.

End DX41J.
