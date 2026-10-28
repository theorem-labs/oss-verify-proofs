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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_5.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 912, SPV - 616)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 776, SPV - 736)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -776) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -736) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -696) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -656) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition X42P (mm : fmem) (rest : list byte) : Prop :=
    rw_cells usegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk usegs mm lo (SPV + -912) /\
    (exists u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : word,
       rw_cells usegs mm (SPV + -616) [C8 u11; C8 u10; C8 u9; C8 u8; C8 u7; C8 u6; C8 u5; C8 u4; C8 u3; C8 u2; C8 u1; C8 u0;
                                      C8 (Z_to_bv 64 0x22090)]) /\
    rw_cells usegs mm (SPV + -512) [CB 408 rest] /\
    munch [(DST, DST + dcap); (SPV - 912, SPV)] m0 mm /\ wmono usegs m0 mm /\ SPV mod 16 = 0.

  Lemma x42p_transport : forall mm mm' rest, X42P mm rest -> munch WDF mm mm' -> wmono usegs mm mm' -> X42P mm' rest.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' rest (SV & STK & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & BS) & RS & MU & WM & AL) MU' WM'.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply (rw_cells_transport usegs _ mm mm' _ _ SV MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (stk_transport_disjoint usegs _ mm mm' _ _ STK MU' WM'); cbn [disjoint_from]; lia.
    - exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11.
      eapply (rw_cells_transport usegs _ mm mm' _ _ BS MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (rw_cells_transport usegs _ mm mm' _ _ RS MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
    - exact (wmono_trans usegs m0 mm mm' WM WM').
    - exact AL.
  Qed.

  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Lemma x42_sbuf_transport : forall mm mm' S len bs, SBUF mm S len bs -> munch WDF mm mm' -> SBUF mm' S len bs.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' S len bs (SB & SL & R0 & R1' & R2 & D1 & D2) MU'.
    split; [|repeat split; assumption].
    eapply (bytes_at_transport usegs _ mm mm' S bs SB MU'); cbn [disjoint_from]; lia.
  Qed.

  Definition EINVB (mm : fmem) : Prop :=
    stk usegs mm DST (DST + dcap) /\
    rw_cells usegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : word,
       rw_cells usegs mm (SPV + -616) [C8 u11; C8 u10; C8 u9; C8 u8; C8 u7; C8 u6; C8 u5; C8 u4; C8 u3; C8 u2; C8 u1; C8 u0;
                                      C8 (Z_to_bv 64 0x22090)]) /\
    stk usegs mm lo (SPV + -616) /\ stk usegs mm (SPV + -512) (SPV + -104) /\
    munch [(DST, DST + dcap); (SPV - 912, SPV)] m0 mm /\ wmono usegs m0 mm /\ mem_inv usegs mm.

  Lemma x42_einv : forall mm rest (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word)
      c1 b1 pd1 p1 st1 lm1 c2 b2 pd2 p2 st2 lm2 c3 b3 pd3 p3 st3 lm3 c4 b4 pd4 p4 st4 lm4,
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD1 mm c1 b1 pd1 p1 st1 lm1 -> BD2 mm c2 b2 pd2 p2 st2 lm2 -> BD3 mm c3 b3 pd3 p3 st3 lm3 -> BD4 mm c4 b4 pd4 p4 st4 lm4 ->
    EINVB mm.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      c1 b1 pd1 p1 st1 lm1 c2 b2 pd2 p2 st2 lm2 c3 b3 pd3 p3 st3 lm3 c4 b4 pd4 p4 st4 lm4
      (SV & STK & BS & RS & MU & WM & AL) MI OUT FA B1 B2 B3 B4.
    pose proof (stk_of_rw_cells usegs mm _ _ FA) as H1.
    pose proof (stk_of_rw_cells usegs mm _ _ B4) as H2.
    pose proof (stk_of_rw_cells usegs mm _ _ B3) as H3.
    pose proof (stk_of_rw_cells usegs mm _ _ B2) as H4.
    pose proof (stk_of_rw_cells usegs mm _ _ B1) as H5.
    pose proof (stk_of_rw_cells usegs mm _ _ RS) as H6.
    cbn [cells_size csize Nat.add] in H1, H2, H3, H4, H5, H6.
    change (Z.of_nat 136) with 136 in H1. change (Z.of_nat 40) with 40 in H2, H3, H4, H5. change (Z.of_nat 408) with 408 in H6.
    replace (SPV + -912 + 136) with (SPV + -776) in H1 by lia.
    replace (SPV + -776 + 40) with (SPV + -736) in H2 by lia.
    replace (SPV + -736 + 40) with (SPV + -696) in H3 by lia.
    replace (SPV + -696 + 40) with (SPV + -656) in H4 by lia.
    replace (SPV + -656 + 40) with (SPV + -616) in H5 by lia.
    replace (SPV + -512 + 408) with (SPV + -104) in H6 by lia.
    unfold EINVB. split; [exact OUT|]. split; [exact SV|]. split; [exact BS|].
    split; [|split; [exact H6|split; [exact MU|split; [exact WM|exact MI]]]].
    eapply (stk_merge usegs mm lo (SPV + -656)); [|exact H5|lia].
    eapply (stk_merge usegs mm lo (SPV + -696)); [|exact H4|lia].
    eapply (stk_merge usegs mm lo (SPV + -736)); [|exact H3|lia].
    eapply (stk_merge usegs mm lo (SPV + -776)); [|exact H2|lia].
    eapply (stk_merge usegs mm lo (SPV + -912)); [exact STK|exact H1|lia].
  Qed.

  Lemma x42_retf : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINV mm -> (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evt usegs POST (STF 0x22098 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
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
  Lemma x42_ret : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVB mm -> (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evt usegs POST (ST 0x29160 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI HR.
    destruct EI as (OUT & FR & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & BS) & STK & STK2 & MU & WM & MI).
    kx_autoLx [0x22098] 30%nat [KZRange SPV 4096 (2^47)] [(SPV - 616, 104)].
    all: kx_mem.
    all: try replace (SPV + -912 + 400) with (SPV + -512) by lia.
    pose proof (stk_of_rw_cells usegs mm _ _ BS) as H1.
    cbn [cells_size csize Nat.add] in H1. change (Z.of_nat 104) with 104 in H1.
    replace (SPV + -616 + 104) with (SPV + -512) in H1 by lia.
    eapply (x42_retf mm r); [|exact HR].
    unfold RZ_huf_dx41.EINV. split; [exact OUT|]. split; [exact FR|]. split; [|split; [exact MU|split; [exact WM|exact MI]]].
    eapply (stk_merge usegs mm lo (SPV + -512)); [|exact STK2|lia].
    eapply (stk_merge usegs mm lo (SPV + -616)); [exact STK|exact H1|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_end : forall mm c1 b1 pd1 p1 st1 lm1 c2 b2 pd2 p2 st2 lm2 c3 b3 pd3 p3 st3 lm3 c4 b4 pd4 p4 st4 lm4
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
    EINVB mm -> BD1 mm c1 b1 pd1 p1 st1 lm1 -> BD2 mm c2 b2 pd2 p2 st2 lm2 -> BD3 mm c3 b3 pd3 p3 st3 lm3 -> BD4 mm c4 b4 pd4 p4 st4 lm4 ->
    evt usegs POST (ST 0x290ec mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 dcap) x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm c1 b1 pd1 p1 st1 lm1 c2 b2 pd2 p2 st2 lm2 c3 b3 pd3 p3 st3 lm3 c4 b4 pd4 p4 st4 lm4
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 EI B1 B2 B3 B4.
    kx_autoLx [0x29160] 40%nat [KZRange SPV 4096 (2^47)] [(SPV - 776, 40); (SPV - 736, 40); (SPV - 696, 40); (SPV - 656, 40)].
    all: clear KXBR.
    all: eapply (x42_ret mm); [exact EI | first [left; reflexivity | right; split; reflexivity]].
  Qed.

End DX42_5.
