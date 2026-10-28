(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 huf41_kit_x41ck huf411_kit_rs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf411_kit_d1t huf411_kit_d1l huf411_kit_d1e.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis LO : 4096 <= lo /\ lo <= SPV - 912.
  Hypothesis SPB : SPV < 2^47.
  Hypothesis R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47.
  Hypothesis OS1 : DST + dcap <= lo \/ SPV <= DST.
  Hypothesis DL : zlen dtb = 16388.
  Hypothesis R3 : 4096 <= DT /\ DT + 16388 < 2^47.
  Hypothesis DJ2 : DST + dcap <= DT \/ DT + 16388 <= DST.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).

  (* [comment removed for export] *)
  Definition EINV (mm : fmem) : Prop :=
    stk usegs mm DST (DST + dcap) /\
    rw_cells usegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk usegs mm lo (SPV + -104) /\
    munch [(DST, DST + dcap); (SPV - 912, SPV)] m0 mm /\ wmono usegs m0 mm /\ mem_inv usegs mm.

  (* [comment removed for export] *)
  Lemma x41_ret : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINV mm -> (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x23594) fc None mm (seg_rom usegs)).
  Proof.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI HR.
    destruct EI as (OUT & FR & STK & MU & WM & MI).
    kx_autoLx [] 30%nat [KZRange SPV 4096 (2^47)] [(SPV - 104, 104)].
    kx_mem. zstep. release_frame FR STK SPV.
    apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end).
    (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
      (split; [exact OUT|]); (split; [|split; [|exact I]]).
    - destruct HR as [HR|[HR _]]; [left; exact HR | right; exact HR].
    - destruct HR as [->|[HR1 HR2]]; [clear - R1; lia|]. unfold zd_is_error, ZE_maxCode in HR1. apply Z.ltb_lt in HR1. clear - HR1 HR2. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation WD := [(DST, DST + dcap)].
  Notation WDK := [(DST, DST + dcap); (SPV - 376, SPV - 336)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).
  Notation DT4 := (Z_to_bv 64 (DT + 4)).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).

  (* [comment removed for export] *)
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation BD1 mm c b pad p st lm := (rw_cells usegs mm (SPV + -376) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).

  Notation KD1 mb pe x9 x19 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S :=
    (forall mm' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y26 y28 y29 y30 y31 c' b' p' : word) (pad' : list byte),
        munch WDK mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
        BD1 mm' c' b' pad' p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x2448c mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 y18 x19 Q62 x21 x22 x23 x24
                           DT4 y26 OEND y28 y29 y30 y31)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SINV (off len bc : Z) : Prop := off = 0 \/ (1 <= off /\ off + 8 <= len /\ bc <= 64).

  (* [comment removed for export] *)
  Lemma x41_d1 : forall mb mm j pe off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^32 -> SPV mod 16 = 0 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x24034 mm x1 x5 x6 (Z_to_bv 64 DST) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dl)
                       x20 x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    (* [comment removed for export] *)
    intros mb mm j pe off S len bs dl tl rsv bc c0 pad x1 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 MU WM MI OUT DTB FA BD DJ3 SB SL S0 S1 SL32 DJS DJK HJ HPE HDL HTL HRSV HS HB SP16 K.
    apply rsk_al_i in SP16.
    assert (CASES : bc <= 64 \/ (65 <= bc < 2^31) \/ 2^31 <= bc) by lia.
    destruct CASES as [BC|[BC|BC]];
    [ kx_autoLx [0x24080; 0x24300; 0x243fc] 40%nat
        [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange (pe - j) 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
         KZRange (DST + j) 4096 (2^47); KZRange (DST + pe) 4096 (2^47); KZRange bc 0 64; KZRange dl 0 65535; KZRange SPV 4096 (2^47);
         KZWr (SPV + -376) 40]
        [(SPV + -512, 136); (SPV + -376, 40)]
    | kx_autoLx [0x24080; 0x24300; 0x243fc] 40%nat
        [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange (pe - j) 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
         KZRange (DST + j) 4096 (2^47); KZRange (DST + pe) 4096 (2^47); KZRange bc 65 (2^31 - 1); KZRange dl 0 65535;
         KZRange SPV 4096 (2^47); KZWr (SPV + -376) 40]
        [(SPV + -512, 136); (SPV + -376, 40)]
    | kx_autoLx [0x24080; 0x24300; 0x243fc] 40%nat
        [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange (pe - j) 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
         KZRange (DST + j) 4096 (2^47); KZRange (DST + pe) 4096 (2^47); KZRange bc (2^31) (2^32 - 1); KZRange dl 0 65535;
         KZRange SPV 4096 (2^47); KZWr (SPV + -376) 40]
        [(SPV + -512, 136); (SPV + -376, 40)] ].
    all: x41_ck.
    Time all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24300) _ _ _ _) =>
             eapply (x41_e1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2
                       mb _ j pe off S len bs dl tl rsv bc (DST + j))
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x243fc) _ _ _ _) =>
             eapply (x41_g1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2
                       mb _ j pe dl tl rsv S (DST + j))
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24080) _ _ _ _) =>
             eapply (x41_l1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2
                       (Z.to_nat (pe - j)) mb _ j pe off S len bs dl tl rsv bc bc 64 (DST + pe + -3) (-1 * DT + -5) (DST + j + 3) 2
                       (Z.land ((-1 * dl) mod 2^64) 63) (2^64 - 1) (DST + j))
         end.
    all: try exact K.
    all: try eassumption.
    all: try (exact (rsk_al_e _ _ SP16)).
    all: try reflexivity.
    all: try lia.
    all: subst dl; rewrite (neg_dl_sh tl rsv HTL); apply Z.mod_small; lia.
  Qed.

End DX41.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x41_ctx (SPV DST dcap DT lo : Z) (dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 912) /\ SPV < 2^47 /\ (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\
  (DST + dcap <= lo \/ SPV <= DST) /\ zlen dtb = 16388 /\ (4096 <= DT /\ DT + 16388 < 2^47) /\ (DST + dcap <= DT \/ DT + 16388 <= DST).

Ltac x41_ctx_open CTX := destruct CTX as (LO & SPB & R1 & OS1 & DL & R3 & DJ2).

Section DX41C.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Definition x41_ret_c := ltac:(x41_ctx_open CTX;
    exact (x41_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 R3 DJ2)).
  Definition x41_d1_c := ltac:(x41_ctx_open CTX;
    exact (x41_d1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2)).
End DX41C.
