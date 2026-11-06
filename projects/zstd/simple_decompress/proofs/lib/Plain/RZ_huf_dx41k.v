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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41h RZ_huf_dx41i RZ_huf_dx41j.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41K.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis BITINIT : bit_init_stmt.

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

  (* [comment removed for export] *)
  Lemma x41_einv_gen : forall mm rest (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word) csB,
    X41P mm rest -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 -> rw_cells psegs mm (SPV + -256) csB -> cells_size csB = 40%nat -> EINV mm.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 csB (SV & STK & RS & MU & WM) MI OUT FA BD SZ.
    pose proof (stk_of_rw_cells psegs mm _ _ FA) as H1.
    pose proof (stk_of_rw_cells psegs mm _ _ BD) as H2.
    pose proof (stk_of_rw_cells psegs mm _ _ RS) as H3.
    rewrite SZ in H2. cbn [cells_size csize Nat.add] in H1, H3.
    change (Z.of_nat 160) with 160 in H1. change (Z.of_nat 40) with 40 in H2. change (Z.of_nat 112) with 112 in H3.
    replace (SPV + -416 + 160) with (SPV + -256) in H1 by lia.
    replace (SPV + -256 + 40) with (SPV + -216) in H2 by lia.
    replace (SPV + -216 + 112) with (SPV + -104) in H3 by lia.
    unfold RZ_huf_dx41.EINV. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU|split; [exact WM|exact MI]]].
    eapply (stk_merge psegs mm lo (SPV + -216)); [|exact H3|lia].
    eapply (stk_merge psegs mm lo (SPV + -256)); [|exact H2|lia].
    eapply (stk_merge psegs mm lo (SPV + -416)); [exact STK|exact H1|lia].
  Qed.

  Lemma x41_i4 : forall mm rest e1 n tot S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 dl tl rsv
      (k1 k2 k3 : word) junk
      (x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w11 w13 w15 w16 w17 w18 : word),
    X41P mm rest -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 w1 w2 w3 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 dl) k3 (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 S3) (Z_to_bv 64 c1) (Z_to_bv 64 (DST + 2 * e1)) w11 (Z_to_bv 64 dcap) w13 (Z_to_bv 64 (S1 - 6)) w15 w16 w17 w18 (Z_to_bv 64 c2) ->
    rw_cells psegs mm (SPV + -256) [CB 40 junk] ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 ->
    n4 = n - tot -> 0 <= tot <= n -> n < 2^32 ->
    0 <= e1 -> 3 * e1 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    evt psegs POST (ST 0x22d70 mm (Z_to_bv 64 n) x5 x6 x7 (Z_to_bv 64 S1) (Z_to_bv 64 S2) x10 (Z_to_bv 64 S4) (Z_to_bv 64 tot) x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 c3) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 e1) k2 k1 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 n tot S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 dl tl rsv k1 k2 k3 junk
      x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31
      w0 w1 w2 w3 w11 w13 w15 w16 w17 w18 PV MI OUT DTB NBOK FA BD SB1 SB2 SB3 SB4 HI1 HI2 HI3 HN4 HTOT HN HE1 HE3 HDL HTL HRSV.
    kx_autoLx [0x24134] 10%nat [KZRange n 0 (2^32); KZRange tot 0 (2^32); KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
    destruct PV as (SV & STK & RS & MU & WM).
    destruct SB1 as (B1 & SF1). destruct SB2 as (B2 & SF2). destruct SB3 as (B3 & SF3).
    destruct SB4 as (B4 & L4 & R40 & R41 & R42 & D41 & D42).
    clear KXK KXA KXRD.
    eapply evt_cut; [eapply (BITINIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (SPV + -256) S4 (n + -1 * tot) b4 junk)
                    | unfold bit_init_post; post_call psegs mm].
    1-10: first [eassumption | lia].
    rename x22 into m1. rename x23 into r.
    assert (PV1 : X41P m1 rest) by exact (conj SV (conj STK (conj RS (conj MU WM)))).
    assert (SB1' : SBUF m1 S1 n1 b1) by exact (conj B1 SF1).
    assert (SB2' : SBUF m1 S2 n2 b2) by exact (conj B2 SF2).
    assert (SB3' : SBUF m1 S3 n3 b3) by exact (conj B3 SF3).
    assert (SB4' : SBUF m1 S4 n4 b4) by exact (conj B4 (conj L4 (conj R40 (conj R41 (conj R42 (conj D41 D42)))))).
    destruct POST as [(HR & HR1 & cont & bc & pad & HB1 & HB2 & BDC) | (HER & HRB & bs & BDC)].
    1: unfold bitd_cells in BDC.
    all: kx_autoLx [0x23454; 0x22d88] 10%nat [KZRange r 0 (2^64 - 1); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ _ _) =>
             first [ exfalso; lia
                   | eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m1);
                     [ eapply (x41_einv_gen m1 rest); first [exact PV1 | exact KXMI | exact OUT | exact FA | exact BDC | reflexivity]
                     | right; exact (conj HER HRB) ] ]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142728) _ _ _ _) =>
             first [ exfalso; unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; lia
                   | unfold bitd_ptr in BDC; destruct (8 <=? n + -1 * tot) eqn:E8; [apply Z.leb_le in E8 | apply Z.leb_gt in E8];
                     [ replace (S4 + (n + -1 * tot) - 8) with (S4 + (n4 - 8)) in BDC by lia;
                       eapply (x41_m0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 m1 rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3
                                 S4 n4 b4 (n4 - 8) bc dl tl rsv k1 k2 k3 cont pad)
                     | assert (BD' : BD4 m1 cont (Z_to_bv 64 bc) pad (Z_to_bv 64 (S4 + 0)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
                         by (replace (S4 + 0) with S4 by lia; exact BDC);
                       eapply (x41_m0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 m1 rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3
                                 S4 n4 b4 0 bc dl tl rsv k1 k2 k3 cont pad) ] ]
         | _ => first [lia | unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; lia]
         end.
    all: first [ exact PV1 | exact KXMI | exact NBOK | exact OUT | exact DTB | exact FA | exact BDC | exact BD'
               | exact SB1' | exact SB2' | exact SB3' | exact SB4' | exact HI1 | exact HI2 | exact HI3 | lia
               | unfold RZ_huf_dx41g.HINV; lia ].
  Qed.

End DX41K.
