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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41q RZ_huf_fkit RZ_huf_dx41r RZ_huf_dx41r2 RZ_huf_dx41t RZ_huf_dx41u RZ_huf_dx41f RZ_huf_dx41k RZ_huf_dx41o.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41V.
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

  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw ilo oew ie0 ie1 ie2 ie3 :=
    (rw_cells psegs mm (SPV + -256) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 bt0; C8 bt1; C8 bt2; C8 bt3; C8 dtw; C8 ilo; C8 oew; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).

  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_einv_f := (RZ_huf_dx41r.x41_einv_f ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_f0_ok : forall mm SRC n src l1 l2 l3 (b0 b1 b2 b3 : word)
      (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17 w18 w19 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 DT) w16 w17 w18 w19 ->
    rw_cells psegs mm (SPV + -256) (fast_args_cells DST dcap SRC n DT l1 l2 l3 b0 b1 b2 b3) ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    evt psegs POST (ST 0x21d90 mm x1 x5 x6 x7 x8 (Z_to_bv 64 DST) (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 dcap) x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src l1 l2 l3 b0 b1 b2 b3
      x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17 w18 w19 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HL1 HL2 HL3 HLN HQ3.
    unfold fast_args_cells in AR. cbv zeta in AR.
    assert (KS : SRC + n <= SPV - 416 \/ SPV <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 416 \/ SPV <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 416 \/ SPV <= DT) by (clear - DJ3 LO; lia).
    destruct PV as (SV & STK & MUP & WMP).
    kx_autoLx [0x21e28] 80%nat
      [KZImg 0x10000 0x14000; KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47);
       KZWr (SPV - 416) 160]
      [(SPV - 416, 160); (SPV - 256, 152); (0x110b8, 8)].
    kx_mem.
    set (q := (dcap + 3) / 4) in *.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        let HF := fresh "HF" in
        pose proof (x41_fo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 (Z.to_nat (dcap + 1)) m2 SRC n src
                      (l1 + -2) ((l1 + l2) + -2) ((l1 + (l2 + l3)) + -2) (n + -8) 0 q (2 * q) (3 * q)) as HF;
        replace (SRC + (l1 + -2)) with (SRC + l1 + -2) in HF by lia;
        replace (SRC + (l1 + l2 + -2)) with (SRC + (l1 + l2) + -2) in HF by lia;
        replace (SRC + (l1 + (l2 + l3) + -2)) with (SRC + (l1 + (l2 + l3)) + -2) in HF by lia;
        replace (SRC + (n + -8)) with (SRC + n + -8) in HF by lia;
        replace (DST + 0) with DST in HF by lia;
        eapply HF
    end.
    all: first [ exact (conj SV (conj STK (conj MUP WMP))) | exact KXMI | exact OUT | exact DTB | exact FA | exact AR | exact SB | exact SL
               | exact DJS | exact DKS | subst q; lia ].
  Qed.

  Lemma x41_f0_no : forall mm SRC n src tl rsv r bs
      (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w16 w17 w18 w19 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb -> huf_nb_ok false dtb tl ->
    nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 n) (Z_to_bv 64 SRC) (Z_to_bv 64 DT) w16 w17 w18 w19 ->
    rw_cells psegs mm (SPV + -256) [CB 152 bs] ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    (r = 0 \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evt psegs POST (ST 0x21d90 mm x1 x5 x6 x7 x8 (Z_to_bv 64 DST) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 dcap) x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src tl rsv r bs
      x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w16 w17 w18 w19 PV MI OUT DTB NBOK DT2 DT3 HTL HRSV FA AR SB SL S0 S1 SL32 DJS DKS HR HRB.
    kx_autoLx [0x23454; 0x226c0; 0x21e28] 80%nat
      [KZImg 0x10000 0x14000; KZRange r 0 (2^64 - 1); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47);
       KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160]
      [(SPV - 416, 160); (SPV - 256, 152); (0x110b8, 8)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ _ _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm);
             [ eapply (x41_einv_f mm); first [ exact PV | exact MI | exact OUT | exact FA | exact AR | reflexivity ]
             | right; split; [destruct HR as [HR|HR]; [exfalso; lia | exact HR] | lia] ]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140992) _ _ _ _) =>
             destruct (cb_carve psegs mm (SPV + -256) 152 bs 40 112 AR ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & C1 & C2 & _);
             change (Z.to_nat 40) with 40%nat in C1; change (Z.to_nat 112) with 112%nat in C2;
             replace (SPV + -256 + 40) with (SPV + -216) in C2 by lia;
             destruct PV as (SV & STK & MUP & WMP);
             eapply (x41_s0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 BITINIT mm j2 SRC n src tl rsv j1);
             first [ exact (conj SV (conj STK (conj C2 (conj MUP WMP)))) | exact MI | exact OUT | exact DTB | exact NBOK | exact DT2 | exact DT3
                   | exact HTL | exact HRSV | exact FA | exact C1 | exact SB | exact SL | exact DJS | exact DKS | lia ]
         | _ => exfalso; destruct HR as [HR|HR]; [lia | unfold zd_is_error, ZE_maxCode in HR; apply Z.ltb_lt in HR; lia]
         end.
  Qed.

End DX41V.
